/-
Stuff about Equiv.Perm α
-/

import Mathlib.Logic.Equiv.Defs

-- The version in import Mathlib.GroupTheory.Perm.Support is useless to us
def Equiv.Perm.support' {α : Type*} (f : Equiv.Perm α): Set α :=
  {x | f x ≠ x}
