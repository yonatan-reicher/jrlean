module

public import Jrlean.Coc.VarKind
public import Jrlean.Coc.VarDecl
public import Jrlean.Coc.Var
public import Jrlean.Coc.VarConversions

public import Jrlean.Coc.Offseting
public import Jrlean.Coc.VarOffseting
public import Jrlean.Coc.VarOffsetingLemmas
public import Jrlean.Coc.TermOffseting
public import Jrlean.Coc.TermOffsetingLemmas

public import Jrlean.Coc.BinderKind
public import Jrlean.Coc.BinderKindNotation
public import Jrlean.Coc.Term
public import Jrlean.Coc.TermNotation
public import Jrlean.Coc.Sort

public import Jrlean.Coc.VarSubst
public import Jrlean.Coc.TermFreeVars
public import Jrlean.Coc.Subst
-- public import Jrlean.Coc.SubstLemmas
--
-- public import Jrlean.Coc.BetaReducesTo

/-!
"CoC" stands for "Calculus of Constructions". It is an extension to the standard lambda calculus
that is the basis of both Lean's and Roq's dependent type theories. Coc expressions are called
"terms", and are dependently typed. This frameworks has both terms with de Bruijn indices and terms
with named identifiers.

Everything is defined in the `Coc` namespace.

In this module, the word `lambda` is sometimes written as `lam`.

## Offseting

Variables are defined either as de Bruijn indices or as named identifiers. Both representations are
dependent on context, and need to be adjusted when the context changes. We call this offseting.
A variable needs to be "offset in" by some variable when moved into a binder, and needs to be
"offset out" by some variable declaration when moved out of it.
An entire term can be offset in or out by a variable declaration as well.
-/
