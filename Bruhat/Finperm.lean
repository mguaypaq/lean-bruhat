/-
Stuff about finperm α
-/

import Bruhat.Perm



def finperm : (α : Type) → Set (Equiv.Perm α) :=
  fun α => univ
