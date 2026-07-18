module

public import Jrlean.Coc.VarKind
public import Jrlean.Coc.VarDecl
public import Jrlean.Coc.Var
public import Jrlean.Coc.VarConversions

public import Jrlean.Coc.BinderKind
public import Jrlean.Coc.BinderKindNotation
public import Jrlean.Coc.Term
public import Jrlean.Coc.TermNotation

/-!
"CoC" stands for "Calculus of Constructions". It is an extension to the standard lambda calculus
that is the basis of both Lean's and Roq's dependent type theories. Coc expressions are called
"terms", and are dependently typed. This frameworks has both terms with de Bruijn indices and terms
with named identifiers.

Everything is defined in the `Coc` namespace.

In this module, the word `lambda` is sometimes written as `lam`.
-/
