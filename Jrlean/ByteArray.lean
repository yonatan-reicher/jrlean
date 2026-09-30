module

public import Std.Data.ByteSlice

open Std

@[expose]
public section

namespace ByteArray

variable {b : ByteArray}

@[simp, grind →]
theorem not_isEmpty_to_zero_lt_size : b.isEmpty = false → 0 < b.size := by
  unfold isEmpty
  lia

@[simp, grind .]
theorem isEmpty_to_size_eq_zero : b.isEmpty → b.size = 0 := by
  unfold isEmpty
  lia

def get? (i : Nat) (b : ByteArray) : Option UInt8 :=
  if h : i < b.size then b.get i else none

end ByteArray

namespace ByteSlice

def get? (i : Nat) (b : ByteSlice) : Option UInt8 :=
  if h : i < b.size then b.get (.mk i h) else none

end ByteSlice
