module

meta import Lean.Parser
meta import Lean.Parser.Command
meta import Lean.Elab.Command
meta import Lean.Parser.Term

macro "instance " t:bracketedBinder* ": " typeClass:ident name:ident " infer" : command => do
  -- TODO: Why can't I add visibility modifiers before the instance keywords?
  `(
    instance $t:bracketedBinder* : $typeClass $name := by
      try unfold $typeClass
      simp [$name:term]; split <;> infer_instance
  )
