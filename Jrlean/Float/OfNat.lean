module
-- Importing this exposes Float.ofNat which is very needed for proofs.
import all Init.Data.OfScientific

public section

namespace Jrlean.Float

@[grind =]
theorem ofNat_def : Float.ofNat = fun n => .ofScientific n false 0 := by rfl

@[grind =, simp]
theorem ofNat_zero : Float.ofNat 0 = (0 : Float) := rfl
