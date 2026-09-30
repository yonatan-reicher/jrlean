module

import Jrlean.ByteArray
import Jrlean.Of
import Jrlean.Option
import Std

namespace Jrlean
namespace DNS


structure DomainName where ofString ::
  toString : String
  deriving Inhabited, Repr

def DomainName.parts (d : DomainName) : Array String.Slice :=
  d.toString.split '.' |>.toArray

def DomainName.byteParts (d : DomainName) : Array ByteArray :=
  d.parts.map λ part => part.copy.toByteArray

def DomainName.encode (d : DomainName) : ByteArray :=
  d.byteParts
  |>.map withLength
  |> append
  |> (· ++ .mk #[ 0 ])
where
  withLength part := .mk #[ part.size.toUInt8 ] ++ part
  append := Array.foldl (· ++ ·) .empty

partial def DomainName.decode? (b : ByteSlice) : Except String (DomainName × Nat) :=
  go 0 ByteArray.empty |>.bind λ (bytes, nRead) => finalize bytes nRead
where
  go i acc : Except _ _ :=
    match b.get? i with
    | some 0x00 => .ok (acc, i + 1)
    | some l =>
      if i = 0
      then takePart l.toNat (i + 1) acc
      else takePart l.toNat (i + 1) (acc.push '.'.toUInt8)
    | none => throw "cannot read part length"
  takePart (l : Nat) (i : Nat) acc :=
    match l with
    | 0 => go i acc
    | l' + 1 =>
      match b.get? i with
      | some c => takePart l' (i + 1) (acc.push c)
      | none => throw "cannot read byte"
  finalize b nRead :=
    if h : b.IsValidUTF8
    then return (.ofString of .ofByteArray b h, nRead)
    else throw "invalid utf-8"

#eval!
  "www.google.com"
  |> DomainName.ofString
  |>.encode
  |>.toByteSlice
  |> DomainName.decode?
  |>.toOption
  |>.get!


open Std

#eval do
  let dnsServerAddress : Net.SocketAddress := .v4 { addr := ⟨#[8, 8, 8, 8].toVector⟩, port := 53 }
  let c ← Async.UDP.Socket.mk
  c.connect dnsServerAddress
  c.send of
    [
      -- Transaction ID
      0x00, 0x00,
      -- QR, OPCODE, AA, TC, RD
      0x01, 0x00,
      -- Question count
      0, 1,
      -- Answer count
      0, 0,
      -- Authority count
      0, 0,
      -- Addl. recond count
      0, 0,
    ].toByteArray
    ++ ("www.google.com" |> DomainName.ofString |>.encode)
    ++ [
      0, 0,
      -- CLASS = internet
      0, 1,
      -- TYPE = host address
      0, 1,
    ].toByteArray
  |>.wait
  let (x, responseAddress) ← c.recv 1000 |>.wait
  if responseAddress != dnsServerAddress then
    throw of IO.userError s!"bad response address: '{responseAddress}'"
  let answer := x.data.drop of 6 * 2 + 15
  IO.println answer
