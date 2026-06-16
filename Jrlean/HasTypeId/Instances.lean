module

public import Jrlean.TypeId
public import Jrlean.HasTypeId.Basic
meta import Jrlean.HasTypeId.Derive

namespace Jrlean

deriving instance HasTypeId for Nat, Int, String, Bool
deriving instance HasTypeId for PUnit, Empty, PEmpty
deriving instance HasTypeId for List
deriving instance HasTypeId for ULift
