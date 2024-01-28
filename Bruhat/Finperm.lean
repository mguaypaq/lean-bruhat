/-
Stuff about finperm α
-/
import Bruhat.Perm
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.Set.Pointwise.SMul

open Set
open Equiv.Perm

variable {α : Type*} {x y : α} {f g : Equiv.Perm α}

/-- Finitely supported permutations are a subgroup -/
def finperm' (α : Type*) : Subgroup (Equiv.Perm α) where
  carrier := {f | f.support'.Finite}
  mul_mem' := fun {a} {b} ha hb ↦ (ha.union hb).subset <| Equiv.Perm.support'_prod _ _
  one_mem' := by simp
  inv_mem' := by simp

@[simp] theorem mem_finperm'_iff : f ∈ finperm' α ↔ f.support'.Finite := Iff.rfl

theorem swap_mem_finperm [DecidableEq α] (x y : α) : Equiv.swap x y ∈ finperm' α := by
  obtain (rfl | hne) := em (x = y)
  · simp [← Equiv.Perm.one_def]
  rw [mem_finperm'_iff, support'_swap hne]
  exact toFinite {x, y}
