module

namespace Jrlean

public section

/-- A depenedent version of the Reader monad. -/
@[expose]
def DReader (σ : Type) (α : σ → Type) : Type := 
  (s : σ) → α s

def DReader.pure {σ α} : (∀ s, α s) → DReader σ α
  | a => fun s => a s

def DReader.map {σ α β} (f : ∀ s, α s → β s) : DReader σ α → DReader σ β
  | x => fun s => f s (x s)

def DReader.bind {σ α β} (f : ∀ s, α s → DReader σ β)
: DReader σ α → DReader σ β
  | x => fun s => f s (x s) s

def _root_.Reader.toDReader {σ α} : ReaderM σ α → DReader σ (fun _ => α)
  | x => x
