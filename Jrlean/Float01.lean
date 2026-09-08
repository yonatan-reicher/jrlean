module
import Jrlean.Float

namespace Jrlean

@[expose] public section

structure Float01 extends x : Float where
  h : 0 ≤ x ∧ x < 1
  deriving DecidableEq /- , Hashable -/

namespace Float01

@[local grind, local simp]
def toFloat := Float01.x

instance : Coe    Float01 Float where coe := toFloat
instance : CoeOut Float01 Float where coe := toFloat

-- With what's available for floats right now, there is now way I am proving something even as
-- simple as this theorem.
--
-- attribute [local grind, local simp]
--   -- <
--   LE.le Float.le Float.Model.le Float.Model.UnpackedFloat.le
--   -- conversions
--   OfNat.ofNat Float.ofNat -- OfScientific.ofScientific Float.ofScientific
--   in
-- private theorem zero_le_mul {x y : Float} : 0 ≤ x → 0 ≤ y → 0 ≤ x * y := by
--   intro h_x h_y
--   -- Start by rewriting the comparison operator
--   rcases x with ⟨⟨x, h_x_valid⟩⟩
--   rcases y with ⟨⟨y, h_y_valid⟩⟩
--   simp_all
--   simp [OfScientific.ofScientific] at *
--   unfold Float.ofScientific at *
--   unfold Float.ofNat at h_x
--   simp [LE.le, Float.le]
--   rw [Float.Model.le]
--   rw [Float.Model.unpack]
--   rw [Float.toModel]
--   simp [HMul.hMul, Mul.mul, Float.mul]

-- instance : Mul Float01 where
--   mul x y := .mk (x * y) $ by
--     obtain ⟨x, h_x⟩ := x
--     obtain ⟨y, h_y⟩ := y
--     simp
