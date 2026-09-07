module

import Jrlean.Of
import Jrlean.Python

namespace Jrlean

open IO.FS (Handle)
open System.Platform (isOSX)

public def mkWaveFile
    (frames : Nat)
    (framesPerSecond : Float)
    (sound : Fin frames → UInt8)
    : IO Handle := do
  let some python ← Python.get?
    | throw of .userError "could not find the python executable"
  let child ← python.run s!"
    import math
    import sys
    import wave
    with wave.open(sys.stdout.buffer, 'wb') as f:
      f.setnchannels(1)
      f.setsampwidth(1)
      f.setframerate({framesPerSecond})
      bytes = sys.stdin.buffer.read({frames})
      f.writeframes(bytes)
  "
  let N := 1024
  let Buf := { b : ByteArray // b.size = N }
  let mut buf : Buf := ⟨.mk of Array.replicate N 0, p1⟩
  -- For each frame,
  for h_iFrame : iFrame in [0:frames] do
    let iFrame : Fin frames := .mk iFrame (Membership.get_elem_helper h_iFrame rfl)
    -- for a whole chunk,
    let iChunkFrame := iFrame % N
    let i := iChunkFrame
    have : i < N := by grind
    -- read from the sound,
    buf := {
      val := buf.val.set i (sound iFrame) <| by rw [buf.property]; exact ‹i < N›
      property := by
        rw [ByteArray.set, ByteArray.size]
        simp only [Array.size_set, ByteArray.size_data]
        rw [buf.property]
    }
    -- and write it back!
    if i == N - 1 then child.stdin.write buf
  -- Write last partttt....
  -- Superfluos bytes get written too but the program knows how to handle it.
  child.stdin.write buf.val
  return child.stdout
where
  p1 {N} : (Array.replicate N 0).size = N := by
    grind only [=_ ByteArray.size_data, = Array.size_replicate]
  p2 {b : ByteArray} {i x h} : (b.set i x h).size = b.size := by
    repeat rw [←ByteArray.size_data]
    rw [ByteArray.data_set]
    rw [Array.size_set]

public def playWavFile (f : IO.FS.Stream) : IO Unit := do
  IO.FS.withTempDir fun d => do
    let p := d / "sound.wav"
    IO.FS.withFile p .writeNew fun t => do
      t.write (← f.readBinToEnd)
      t.flush
      let child ← IO.Process.spawn {
        cmd :=
          if isOSX
          then "afplay"
          else panic! "unsupported"
        args := #[p.toString]
        stdin := .null
        stdout := .null
        stderr := .piped
      }
      let exitCode ← child.wait
      IO.println exitCode
      IO.println (← child.stderr.readToEnd)

#eval do (← mkWaveFile 3 441000 fun i => .ofNat (i % 255)).readBinToEnd
-- #eval show IO _ from do
--   let b : IO.Ref IO.FS.Stream.Buffer ← IO.mkRef ⟨.empty, 0⟩
--   playWavFile (.ofBuffer b)
#eval do
  .ofHandle (← mkWaveFile 1000 8000 fun i => .ofNat (i % 255))
  |> playWavFile
