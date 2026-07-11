module

public import Jrlean.Coc.Basic
open Std (Format)

namespace Jrlean.Coc.Term

variable {vkind : VarKind}

structure C where
  isRightMost : Bool
  asAtom : Bool

abbrev C.notRightMost (c : C) := { c with isRightMost := false }
abbrev C.setRightMost b (c : C) := { c with isRightMost := b }
abbrev C.notAsAtom (c : C) : C := { c with asAtom := false }

def prettyPrint (t : Term) : ReaderM C Format :=
  match t with
  | type => return "Type"
  | prop => return "Prop"
  | var v => return repr v
  | app f x => do
    let { isRightMost, asAtom } ← read
    let doParens := asAtom
    let fFmt ← (prettyPrint f).run { isRightMost := false, asAtom := true }
    let xFmt ← (prettyPrint x).run { isRightMost := isRightMost || doParens, asAtom := true }
    return fFmt ++ " " ++ xFmt
      |> if doParens then .paren else id
  | binder k v ty body => do
    let { isRightMost, asAtom } ← read
    let tyFmt ← (prettyPrint ty).run { isRightMost := true, asAtom := false }
    let bodyFmt ← (prettyPrint body).run { isRightMost := true, asAtom := false }
    return repr k ++ " " ++ repr v ++ " : " ++ tyFmt ++ " ." ++ .line ++ bodyFmt
      |> if asAtom && !isRightMost then .paren else id

public section

/-- Converts a `Term` to a `Std.Format` for pretty printing. -/
def reprPrec (t : Term) (n : Nat) : Std.Format :=
  -- TODO: Does this make any sense?
  let asAtom := n < 100
  (prettyPrint t).run { isRightMost := false, asAtom := asAtom }

instance : Repr Term where
  reprPrec := reprPrec

