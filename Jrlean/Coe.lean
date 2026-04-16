module

public def coe {α β} (a : α) [CoeT α a β] : β := a
public def coeAs {α} (β) (a : α) [CoeT α a β] : β := a
example (x : Nat) : Int := coe x
