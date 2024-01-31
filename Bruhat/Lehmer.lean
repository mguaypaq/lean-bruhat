import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Intervals
import Bruhat.Finperm
import Mathlib.Data.Nat.Lattice

open scoped Nat

def truncate (f : ℕ → ℕ) (n : ℕ) : ℕ →₀ ℕ where
  support := (Finset.range n).filter (fun x ↦ f x ≠ 0)
  toFun x := if x < n then f x else 0
  mem_support_toFun x := by simp

theorem truncate_apply_of_lt (f : ℕ → ℕ) {n x : ℕ} (hx : x < n) : truncate f n x = f x :=
  if_pos hx

theorem truncate_apply_of_le (f : ℕ → ℕ) {n x : ℕ} (hx : n ≤ x) : truncate f n x = 0 :=
  if_neg (by simpa)

def finLehmer (n : ℕ) : Set (ℕ →₀ ℕ) := {f | (f : ℕ → ℕ) ≤ truncate id n}

def le_truncate_equiv_prod_fin (f : ℕ → ℕ) (n : ℕ) :
    {g : ℕ →₀ ℕ // (g : ℕ → ℕ) ≤ truncate f n} ≃ Π (i : Fin n), Fin (f i + 1) where
  toFun g i := ⟨g.1 i, by simpa [Nat.lt_succ, truncate] using g.2 i⟩
  invFun h := ⟨Finsupp.mk ((Finset.range n).filter (fun i ↦ ∃ hi : i < n, h ⟨i,hi⟩ ≠ 0))
      (fun i ↦ if hi : i < n then h ⟨i,hi⟩ else 0)
      (by
        intro i
        simp only [ne_eq, Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_range,
          dite_eq_right_iff, not_forall]
        obtain (hlt | hle) := em (i < n)
        · simp only [hlt, exists_true_left, true_and, not_iff_not]
          exact eq_iff_eq_of_cmp_eq_cmp rfl
        simp [hle]),
      by
        intro x
        simp only [ne_eq, Finset.filter_congr_decidable, Finsupp.coe_mk]
        split_ifs with hx
        · rw [truncate_apply_of_lt _ hx]
          exact Nat.lt_succ.1 (h ⟨x, hx⟩).2
        exact Nat.zero_le ((truncate f n) x)⟩
  left_inv g := by
    ext x
    simp only [ne_eq, Finset.filter_congr_decidable, dite_eq_ite, Finsupp.coe_mk, ite_eq_left_iff,
      not_lt]
    intro hnx
    have h := g.2 x
    rwa [truncate_apply_of_le _ hnx, Nat.le_zero, eq_comm] at h
  right_inv g := by ext; simp

def Iic_truncate_equiv : {g : ℕ → ℕ // g ≤ truncate f n} ≃ Π (i : Fin n), Fin (f i + 1) where
  toFun g i := ⟨g.1 i, by simpa [Nat.lt_succ, truncate] using g.2 i⟩
  invFun h := ⟨fun i ↦ if hi : i < n then h ⟨i,hi⟩ else 0, by
    intro i
    simp only
    split_ifs with hi
    · rw [truncate_apply_of_lt _ hi]
      exact Nat.lt_succ.1 (h ⟨i, hi⟩).2
    exact Nat.zero_le ((truncate f n) i)⟩
  left_inv g := by
    ext i
    simp only [dite_eq_ite, ite_eq_left_iff, not_lt]
    have hg' := g.2 i
    intro hni
    rwa [truncate_apply_of_le _ hni, Nat.le_zero, eq_comm] at hg'
  right_inv g := by ext; simp

instance le_truncate_fintype (f : ℕ → ℕ) (n : ℕ) :
    Fintype {g : ℕ →₀ ℕ // (g : ℕ → ℕ) ≤ truncate f n} :=
  Fintype.ofEquiv _ (le_truncate_equiv_prod_fin f n).symm

theorem card_lehmer_eq_factorial (n : ℕ) :
    Fintype.card {g : ℕ →₀ ℕ // (g : ℕ → ℕ) ≤ truncate id n} = n ! := by
  rw [Fintype.card_of_bijective (le_truncate_equiv_prod_fin _ _).bijective]
  simp only [id_eq, Fintype.card_pi, Fintype.card_fin]
  rw [← Finset.prod_range_add_one_eq_factorial n]
  exact Fin.prod_univ_eq_prod_range Nat.succ n

def lehmer : Set (ℕ →₀ ℕ) := ⋃ (i : ℕ), finLehmer i

section Inversions

variable {f : Finperm ℕ} {i x n : ℕ}



def Finperm.inversions (f : Finperm ℕ) : Set (ℕ × ℕ) := {p | p.1 < p.2 ∧ f p.2 < f p.1}

def Finperm.inversionsAbove (f : Finperm ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range f.ub).filter (fun j ↦ i < j ∧ f j < f i)

def Finperm.inversionsBelow (f : Finperm ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.range i).filter (fun j ↦ j < i ∧ f i < f j)

def inversionBelowCount (f : Finperm ℕ) (n : ℕ) : ℕ := (f.inversionsBelow n).card

-- def inversionBelowFoo (f : Finperm ℕ)




end Inversions
