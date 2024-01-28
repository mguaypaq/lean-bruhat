/-
Stuff about Equiv.Perm α
-/

import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Set.Pointwise.SMul
import Mathlib.GroupTheory.GroupAction.Group
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.Set.Finite


open Set

variable {α : Type*} {x y : α} {f : Equiv.Perm α}

-- The version in import Mathlib.GroupTheory.Perm.Support is useless to us
def Equiv.Perm.support' (f : Equiv.Perm α) : Set α :=
  {x | f x ≠ x}


namespace Equiv.Perm

instance mulActionPermSet (α : Type*) : MulAction (Equiv.Perm α) (Set α) := Set.mulActionSet

@[simp] theorem not_mem_support' {f : Equiv.Perm α} : x ∉ f.support' ↔ f x = x := by
  simp [support']

@[simp] theorem mem_support' {f : Equiv.Perm α} : x ∈ f.support' ↔ f x ≠ x := by
  simp [support']

@[simp] theorem support'_one (α : Type*) : support' (1 : Equiv.Perm α) = ∅ := by
  ext; simp

@[simp] theorem support'_inv (f : Equiv.Perm α) : support' (f ⁻¹) = support' f := by
  ext x
  rw [mem_support', ne_eq, mem_support', inv_eq_iff_eq, eq_comm]

theorem support'_prod (f g : Equiv.Perm α) : support' (f * g) ⊆ support' f ∪ support' g := by
  refine fun x hx ↦ by_contra <| fun h ↦ hx ?_
  simp only [mem_union, not_or, not_mem_support'] at h
  rw [coe_mul, Function.comp_apply]
  simp [h.1, h.2]

section Swap

variable [DecidableEq α]

theorem support'_swap (hxy : x ≠ y) : (Equiv.swap x y).support' = {x,y} := by
  ext z
  simp only [support', ne_eq, mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  rw [← Ne.def, Equiv.swap_apply_ne_self_iff, and_iff_right hxy]

-- def foo (α : Type) [DecidableEq α] :
--     {f : Equiv.Perm α // f.IsSwap} ≃ {p : Finset α // p.card = 2} where
--   toFun f :=
--     ⟨(show f.1.support'.Finite from sorry).toFinset, sorry⟩
--   invFun p := by
--     _
--   left_inv := _
--   right_inv := _




@[ext] structure Pair (α : Type*) [LT α] where
  lo : α
  hi : α
  lt : lo < hi


variable [LinearOrder α]

-- def PairEquiv1 (α : Type*) [LinearOrder α] :
--     Pair α ≃ {s : Set α // ∃ x y : α, x ≠ y ∧ s = {x,y} } where
--   toFun := sorry
--   invFun := sorry
--   left_inv := sorry
--   right_inv := sorry


theorem exists_pair_of_isSwap (hf : Equiv.Perm.IsSwap f) :
    ∃ p : Pair α, f = Equiv.swap p.lo p.hi := by
  obtain ⟨x,y, hxy, rfl⟩ := hf
  obtain (h | h) := hxy.lt_or_lt
  · exact ⟨Pair.mk x y h, rfl⟩
  rw [Equiv.swap_comm]
  exact ⟨Pair.mk y x h, rfl⟩



theorem swap_eq_swap {x x' y y' : α} :
    Equiv.swap x y = Equiv.swap x' y' ↔ (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  sorry

/-- The type of increasing pairs is equivalent to the type of transpositions -/
noncomputable def pairEquivSwap (α : Type*) [LinearOrder α] :
    Pair α ≃ {f : Equiv.Perm α // f.IsSwap} where
  toFun p := ⟨Equiv.swap p.lo p.hi, ⟨p.lo, p.hi, p.lt.ne, rfl⟩⟩
  invFun f := Classical.choose (exists_pair_of_isSwap f.2)
  left_inv := by
    sorry
    -- intro p
    -- have := Classical.choose_spec <| exists_pair_of_isSwap ⟨p.lo, p.hi, p.lt.ne, rfl⟩
    -- have := swap_eq_swap.1 this
    -- simp at this
    -- simp
    -- ext

    -- have := Classical.choose_spec
  right_inv := sorry





end Swap

-- def inversion (f : Equiv.Perm α) : Set
