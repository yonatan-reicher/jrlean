module

public import Jrlean.TypeId
public import Jrlean.HasTypeId.Basic
import Jrlean.HasTypeId.Derive

namespace Jrlean

deriving instance TypeId for Nat, Int, String, Bool
