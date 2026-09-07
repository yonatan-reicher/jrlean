module

namespace Jrlean

@[expose]
public section

inductive Wave where
  | sin
  | square
  deriving Repr

def Float.pi := 3.141592653589793

def Wave.sample : Wave → (Float → Float)
  | .sin, x => (2 * x * Float.pi).sin * 0.5 + 0.5
  | .square, x => if x < 0.5 then 0 else 1
