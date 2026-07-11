module

namespace Jrlean

public section

macro "by_contra " h:ident : tactic => do
  `(tactic| (apply Classical.byContradiction; intro $h:ident))
