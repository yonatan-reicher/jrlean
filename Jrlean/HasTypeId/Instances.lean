module

public import Jrlean.TypeId
public import Jrlean.HasTypeId.Basic
meta import Jrlean.HasTypeId.Derive

namespace Jrlean

deriving instance HasTypeId for Nat, Int, String, Bool, PUnit
#print PUnit.typeId
#print PUnit.typeId_ofType
deriving instance HasTypeId for List
#print List.typeId
#eval List.typeId Nat
#eval List.typeId_ofType Nat
