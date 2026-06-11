module

/-
This module defines the `HasTypeId` class. This class associates a unique
identifier to types, which can be used to check for type equality at runtime.

This is an extended version of the builtin `TypeName` class. Namely, it supports
all types, not just those that are without parameters and without universe
parameters.
-/

public import Jrlean.HasTypeId.Basic
public import Jrlean.HasTypeId.Derive
public import Jrlean.HasTypeId.Instances
public import Jrlean.HasTypeId.Lemmas
