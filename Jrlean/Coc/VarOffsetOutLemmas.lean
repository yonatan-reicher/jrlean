module

public import Jrlean.Coc.VarOffseting

import Jrlean.Coc.ShadowedLemmas
import Jrlean.Coc.ShadowsLemmas
import Jrlean.Coc.VarIncLemmas
import Jrlean.Coc.VarDecLemmas
import Jrlean.Coc.VarOffsetInLemmas

namespace Jrlean.Coc.Var

public section

variable {varKind : VarKind}
variable {x y z : Var'}

-- TODO

theorem offsetOut_eq : x↓y = if y = x then none else x := rfl
