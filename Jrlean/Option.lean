module

namespace Option

@[expose]
public section

def toExcept {α σ} (e : σ) (o : Option α) : Except σ α :=
  match o with
  | some a => .ok a
  | none => .error e
