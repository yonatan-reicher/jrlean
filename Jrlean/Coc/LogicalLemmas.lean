module

public import Jrlean.Coc.Logical
public import Jrlean.Coc.Beta

namespace Jrlean.Coc

public section

theorem app_implies [VarKind] {a b}
: Term.app (.app .implies a) b =β Term.pi VarDecl.anonymous a b := sorry

theorem false_implies [VarKind] {a}
: Term.app (.app .implies .false) a =β Term.true := sorry

theorem true_nequiv_false [VarKind] : Term.true ≠β Term.false := sorry
