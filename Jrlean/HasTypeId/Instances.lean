module

public import Jrlean.TypeId
public import Jrlean.HasTypeId.Basic
meta import Jrlean.HasTypeId.Derive

namespace Jrlean

deriving instance TypeId for Nat, Int, String, Bool, PUnit


#print PUnit.typeId_ofType
