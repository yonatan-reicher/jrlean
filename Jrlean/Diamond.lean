module

public import Jrlean.Relation

namespace Jrlean

public section

/--
A proof that a relation sort of comes back together.
This is similiar to `Confluence`, and is useful for proving it.
-/
class Diamond (r : Relation α α) where
  diamond : ∀ a b c, r a b → r a c → ∃ d, r b d ∧ r c d
