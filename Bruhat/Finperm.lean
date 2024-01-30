/-
Stuff about finperm α
-/
import Bruhat.Perm
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Pointwise.SMul

open Finset
open Equiv.Perm

variable {α : Type*} {x y : α}

@[ext] structure Finperm (α : Type*) where
  toPerm : Equiv.Perm α
  support : Finset α
  mem_support_iff' (x : α) : x ∈ support ↔ toPerm x ≠ x

namespace Finperm

variable {f g : Finperm α}

instance {α : Type*} : CoeOut (Finperm α) (Equiv.Perm α) where
  coe f := f.toPerm

instance {α : Type*} : FunLike (Finperm α) α (fun _ ↦ α) where
  coe f x := f.toPerm x
  coe_injective' := by
    intro f g h
    simp only [FunLike.coe_fn_eq] at h
    ext x
    · rw [h]
    rw [f.mem_support_iff', g.mem_support_iff', h]

@[simp] theorem mem_support_iff (f : Finperm α) : x ∈ f.support ↔ f x ≠ x :=
  f.mem_support_iff' x

@[simp] theorem toPerm_eq_coe (f : Finperm α) (x : α) : f.toPerm x = f x := rfl

theorem coe_inj {f g : Finperm α} (h : (f : Equiv.Perm α) = g) : f = g := by
  ext x
  · rw [h]
  rw [mem_support_iff, mem_support_iff, ← toPerm_eq_coe, h, toPerm_eq_coe]

theorem funext {f g : Finperm α} (h : ∀ x, f x = g x) : f = g := by
  apply coe_inj
  ext x
  exact h x

theorem inj_iff {x y : α} : f x = f y ↔ x = y :=
  EquivLike.apply_eq_iff_eq f.toPerm

theorem funext_support {f g : Finperm α} (h : f.support = g.support)
    (h' : ∀ i ∈ f.support, f i = g i) : f = g := by
  refine funext <| fun x ↦ ?_
  obtain (hx | hx) := em (x ∈ f.support)
  · rw [h' x hx]
  have hx' := hx
  rw [h] at hx'
  rw [mem_support_iff, not_not] at hx hx'
  rw [hx, hx']

theorem funext_support_subset {s : Finset α} {f g : Finperm α} (hf : f.support ⊆ s)
    (hg : g.support ⊆ s) (h : ∀ i ∈ s, f i = g i) : f = g := by
  refine funext <| fun x ↦ ?_
  obtain (hx | hx) := em (x ∈ s)
  · exact h _ hx
  rw [(show f x = x by simpa using not_mem_mono hf hx),
    (show g x = x by simpa using not_mem_mono hg hx)]

theorem funext_support_union [DecidableEq α] {f g : Finperm α}
    (h : ∀ i ∈ f.support ∪ g.support, f i = g i) : f = g :=
  funext_support_subset (subset_union_left _ _) (subset_union_right _ _) h

theorem funext_support_iff {f g : Finperm α} : f = g ↔ f.support = g.support ∧
    ∀ i ∈ f.support, f i = g i :=
  ⟨fun h ↦ by simp [h], fun h ↦ funext_support h.1 h.2⟩

instance [DecidableEq α] : DecidableEq (Finperm α) :=
  fun _ _ ↦ @decidable_of_iff _ _ funext_support_iff.symm And.decidable

@[simps, pp_dot] def symm (f : Finperm α) : Finperm α where
  toPerm := (f : Equiv.Perm α).symm
  support := f.support
  mem_support_iff' := by
    intro x
    simp only [mem_support_iff, ne_eq]
    rw [← toPerm_eq_coe, Equiv.apply_eq_iff_eq_symm_apply, eq_comm]

@[simp] theorem symm_symm (f : Finperm α) : f.symm.symm = f := by
  apply coe_inj; simp

@[simp] theorem symm_apply_apply (f : Finperm α) (x : α) : f.symm (f x) = x :=
  Equiv.symm_apply_apply (f : Equiv.Perm α) x

@[simp] theorem apply_symm_apply (f : Finperm α) (x : α) : f (f.symm x) = x :=
  Equiv.apply_symm_apply (f : Equiv.Perm α) x


@[simps] def refl {α : Type*} : Finperm α where
  toPerm := 1
  support := ∅
  mem_support_iff' := by simp

@[simp] theorem refl_apply (x : α) : (refl x) = x := rfl

@[simp] theorem support_eq_empty_iff (f : Finperm α) : f.support = ∅ ↔ f = refl :=
  ⟨fun h ↦ funext_support (by simp [h]) (by simp [h]), fun h ↦ h ▸ rfl⟩

section Group

variable [DecidableEq α]

instance : Mul (Finperm α) where
  mul f g := {
    toPerm := (f : Equiv.Perm α) * g
    support := (f.support ∪ g.support).filter (fun x ↦ f (g x) ≠ x)
    mem_support_iff' := by
      intro x
      simp only [ne_eq, Finset.mem_filter, Finset.mem_union, mem_support_iff, coe_mul,
        Function.comp_apply, toPerm_eq_coe, and_iff_right_iff_imp]
      refine fun h ↦ by_contra fun h' ↦ ?_
      rw [not_or, not_not, not_not] at h'
      rw [h'.2] at h
      exact h h'.1 }

@[simp] theorem mul_apply (f g : Finperm α) (x : α) : (f * g) x = f (g x) := rfl

theorem mul_support_subset (f g : Finperm α) : (f * g).support ⊆ f.support ∪ g.support :=
  Finset.filter_subset _ _

theorem mul_support_eq (f g : Finperm α) :
  (f * g).support = (f.support ∪ g.support).filter (fun x ↦ f (g x) ≠ x) := rfl

/-- Finitely supported permutations are a group -/
instance : Group (Finperm α) where
  one := refl
  inv := symm
  mul_assoc f g h := funext (fun _ ↦ by simp)
  one_mul f := funext (fun _ ↦ rfl)
  mul_one f := funext (fun _ ↦ rfl)
  mul_left_inv f := funext (fun _ ↦ by simp only [mul_apply, symm_apply_apply]; rfl)

theorem one_def : (1 : Finperm α) = refl := rfl

@[simp] theorem one_support (α : Type*) [DecidableEq α] : (1 : Finperm α).support = ∅ := rfl

@[simp] theorem one_apply (x : α) : (1 : Finperm α) x = x := rfl

@[simp] theorem mul_refl (f : Finperm α) : f * refl = f := mul_one f

@[simp] theorem refl_mul (f : Finperm α) : refl * f = f := one_mul f

theorem inv_def (f : Finperm α) : f⁻¹ = f.symm := rfl

@[simp] theorem inv_support (f : Finperm α) : f⁻¹.support = f.support := rfl

theorem inv_eq_iff_eq : f⁻¹ x = y ↔ x = f y := Equiv.Perm.inv_eq_iff_eq

theorem eq_inv_iff_eq : x = f⁻¹ y ↔ f x = y := Equiv.Perm.eq_inv_iff_eq

@[simp] theorem inv_apply_apply (f : Finperm α) (x : α) : f⁻¹ (f x) = x :=
  Equiv.symm_apply_apply (f : Equiv.Perm α) x

@[simp] theorem apply_inv_apply (f : Finperm α) (x : α) : f (f⁻¹ x) = x :=
  Equiv.apply_symm_apply (f : Equiv.Perm α) x


end Group


section Swap

variable [DecidableEq α]

@[simps] def swap (x y : α) : Finperm α where
  toPerm := Equiv.swap x y
  support := if x = y then ∅ else {x,y}
  mem_support_iff' := by
    obtain (rfl | hne) := eq_or_ne x y; simp
    intro z
    rw [if_neg hne, Finset.mem_insert, Finset.mem_singleton, Equiv.swap_apply_ne_self_iff,
      and_iff_right hne]

@[simp] theorem swap_coe_eq (x y : α) : (swap x y : Equiv.Perm α) = Equiv.swap x y := rfl

@[simp] theorem swap_self (x : α) : swap x x = refl := by
  apply coe_inj
  simp only [swap_toPerm, Equiv.swap_self, refl_toPerm]
  rfl

@[simp] theorem swap_apply_left (x y : α) : (swap x y) x = y :=
  Equiv.swap_apply_left x y

@[simp] theorem swap_apply_right (x y : α) : (swap x y) y = x :=
  Equiv.swap_apply_right x y

theorem swap_apply_of_ne_of_ne {z : α} (hx : z ≠ x) (hy : z ≠ y) : (swap x y) z = z :=
  Equiv.swap_apply_of_ne_of_ne hx hy

theorem swap_support_of_ne (hxy : x ≠ y) : (swap x y).support = {x,y} := by
  simp [swap, hxy]

theorem swap_comm (a b : α) : swap a b = swap b a := by
  rw [funext_support_iff]; aesop

theorem swap_mul_swap (a b : α) : swap a b * swap a b = 1 := by
  obtain (rfl | hne) := eq_or_ne a b
  · simp [one_def]
  apply funext_support_subset (s := {a,b})
  · refine (mul_support_subset _ _).trans ?_
    rw [Finset.union_self, swap_support_of_ne hne]
  · simp
  simp

theorem swap_conj_eq (hxz : x ≠ z) (hyz : y ≠ z) :
    (swap x y) * (swap y z) * (swap x y) = swap x z := by
  obtain (rfl | hxy) := eq_or_ne x y
  · simp
  apply funext_support_subset (s := {x,y,z})
  · rw [mul_support_eq, mul_support_eq]
    simp only [mul_apply, ne_eq, swap_support, filter_congr_decidable, if_neg hxy, if_neg hyz]
    refine (filter_subset _ _).trans (union_subset ((filter_subset _ _).trans ?_) (by aesop))
    apply union_subset <;> aesop
  · aesop
  simp only [mem_insert, mem_singleton, mul_apply, forall_eq_or_imp, swap_apply_left,
    swap_apply_right, forall_eq]
  rw [swap_apply_of_ne_of_ne hxz.symm hyz.symm, swap_apply_of_ne_of_ne hxy hxz,
    swap_apply_of_ne_of_ne hxy.symm hyz]
  simp

theorem support_mul_pair_subset (hx : x ∈ f.support) :
    (f * swap x (f⁻¹ x)).support ⊆ f.support.erase x := by
  intro y hy
  simp only [mem_erase, ne_eq, mem_support_iff]
  obtain (rfl | hne) := eq_or_ne y x
  · simp at hy
  refine ⟨hne, fun hy' ↦ ?_⟩
  simp only [mem_support_iff, mul_apply, ne_eq] at hy
  obtain (rfl | hne') := eq_or_ne y (f⁻¹ x)
  · simp only [swap_apply_right, apply_inv_apply] at hy'
    rw [← hy'] at hne
    exact hne rfl
  rw [swap_apply_of_ne_of_ne hne hne'] at hy
  exact hy hy'

def swaps (α : Type*) [DecidableEq α] : Set (Finperm α) :=
    {s : Finperm α | ∃ (x y : α) (_ : x ≠ y), s = swap x y}

theorem support_closure_aux (f : Finperm α) : f ∈ Subgroup.closure (swaps α) := by
  obtain (h | h) := eq_or_ne f.support ∅
  · rw [show f = 1 from (support_eq_empty_iff _).1 h]
    exact Subgroup.one_mem _
  simp only [ne_eq, eq_empty_iff_forall_not_mem, mem_support_iff, not_not, not_forall] at h
  obtain ⟨x, hx⟩ := h
  have hx' : x ∈ f.support := by simpa
  set g := f * swap x (f⁻¹ x) with hg_def
  have _ : g.support.card < f.support.card := by
    have hsupp : g.support ⊆ _ := support_mul_pair_subset hx'
    exact card_lt_card <| (hsupp.trans_ssubset (erase_ssubset hx'))
  have hg := support_closure_aux g
  have hs : swap x (f⁻¹ x) ∈ Subgroup.closure (swaps α)
  · exact Subgroup.subset_closure ⟨_, _, by rwa [ne_eq, eq_inv_iff_eq], rfl⟩
  have hf' : f = g * (swap x (f⁻¹ x))
  · rw [hg_def, mul_assoc, swap_mul_swap, mul_one]
  rw [hf']
  exact Subgroup.mul_mem _ hg hs
termination_by _ => f.support.card

theorem cl_swaps_eq_top (α : Type*) [DecidableEq α] : Subgroup.closure (swaps α) = ⊤ := by
  ext f
  simp only [Subgroup.mem_top, iff_true]
  exact support_closure_aux f

end Swap

section Map

variable {α β : Type*} [DecidableEq α] [DecidableEq β] {f : Finperm α}

/-- The subgroup of `Finperm`s with support contained in some set `s` -/
def restrict (s : Set α) : Subgroup (Finperm α) where
  carrier := {f | (f.support : Set α) ⊆ s}
  mul_mem' {f} {g} hf hg := by
    refine (Finset.coe_subset.2 (mul_support_subset f g)).trans ?_
    rw [coe_union, Set.union_subset_iff]
    exact ⟨hf, hg⟩
  one_mem' := by simp
  inv_mem' := by simp

@[simp] theorem mem_restrict_iff {s : Set α} : f ∈ restrict s ↔ (f.support : Set α) ⊆ s := Iff.rfl

theorem restrict_mono {s t : Set α} (hst : s ⊆ t) : restrict s ≤ restrict t :=
  fun _ hi ↦ Set.Subset.trans hi hst




-- noncomputable def foo (i : α ↪ β) : Finperm α ≃ {f : // f.support ⊆ range i} where
--   toFun f := by
--     _
--   map_one' := _
--   map_mul' := _

end Map
