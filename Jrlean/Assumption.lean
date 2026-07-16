module

namespace Jrlean

public meta section

/-- Just calls the `assumption` tactic -/
macro stx:"assumption" : term => `(by assumption%$stx)
