import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs

-- The type of words in the generators s₀, s₁, ... of adjacency transpositions
@[reducible] def Word := List ℕ

def Word.toPerm (w : Word) : Equiv.Perm ℕ :=
  FreeMonoid.lift (fun i => Equiv.swap i (i + 1)) (FreeMonoid.ofList w)

-- The word for the transposition swapping i and i + k + 1
def WordForSwap (i k : ℕ) : Word :=
match k with
| 0       => [i]
| (k + 1) => ((i + k + 1) :: (WordForSwap i k) ++ [i + k + 1])

lemma WordForSwap_toPerm_succ (i k : ℕ) :
  (WordForSwap i (k + 1)).toPerm =
  Equiv.swap (i + (k + 1)) (i + (k + 2)) * (WordForSwap i k).toPerm *
  Equiv.swap (i + (k + 1)) (i + (k + 2)) := by
  simp [WordForSwap, Word.toPerm]
  rfl

lemma wordForSwap_eq_swap (i k : ℕ) :
  (WordForSwap i k).toPerm = Equiv.swap i (i + (k + 1)) := by
  induction' k with k ih
  . simp only [Nat.zero_eq, add_zero, Equiv.swap_self]
    rfl
  . rw [WordForSwap_toPerm_succ, ih]
    change _ * _ * (Equiv.swap _ _)⁻¹ = _
    rw [← Equiv.swap_apply_apply, Equiv.swap_apply_left,
        Equiv.swap_apply_of_ne_of_ne (by simp) (by simp)]

lemma Word_mul (w v : Word) : (w ++ v).toPerm = w.toPerm * v.toPerm := by
  simp only [Word.toPerm, FreeMonoid.ofList_append, map_mul, FreeMonoid.lift_ofList]

section RepbleByWord
/- Showing that every FinPerm is representable by a word -/

-- should this instead be a type, with a nonempty instance?
def RepbleByWord (f : Equiv.Perm ℕ) : Prop := ∃ w : Word, w.toPerm = f

lemma idHasWord : Word.toPerm [] = 1 := rfl

lemma swapHasWord (i j : ℕ) : RepbleByWord (Equiv.swap i j) := by
  cases' le_or_lt i j with h h
  cases' h.eq_or_lt with h h
  . use []
    rw [idHasWord, h, Equiv.swap_self]
    rfl
  . obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    use WordForSwap i k
    rw [wordForSwap_eq_swap, add_assoc]
  . obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
    use WordForSwap j k
    rw [wordForSwap_eq_swap, add_assoc, Equiv.swap_comm]

def support {α : Type*} (f : Equiv.Perm α) : Set α :=
  {x | f x ≠ x}

lemma apply_of_not_mem_support {α : Type*} (f : Equiv.Perm α) (a : α) (ha : a ∉ support f) :
  f a = a := not_not.mp ha

lemma support_inv {α : Type*} (f : Equiv.Perm α) :
  support f = support f⁻¹ := by
  ext a
  simp [support, not_iff_not]
  rw [← Equiv.Perm.eq_inv_iff_eq, eq_comm]

lemma support_min_lt_inv_apply (f : Equiv.Perm ℕ) (hf : ∃ n, f n ≠ n) :
  (Nat.find hf) < f⁻¹ (Nat.find hf) := by
  set n := Nat.find hf with hn
  obtain ⟨hn', hn''⟩ := (Nat.find_eq_iff hf).mp hn.symm
  specialize hn'' (f⁻¹ n)
  rw [imp_not_comm, not_lt, f.apply_inv_self] at hn''
  rw [ne_eq, ← Equiv.Perm.eq_inv_iff_eq] at hn'
  apply lt_of_le_of_ne (hn'' hn') hn'

lemma support_min_lt_apply (f : Equiv.Perm ℕ) (hf : ∃ n, f n ≠ n) :
  (Nat.find hf) < f (Nat.find hf) := by
  have hg : ∃ n, f⁻¹ n ≠ n
  . simp_rw [ne_comm, ne_eq, Equiv.Perm.eq_inv_iff_eq]
    exact hf
  have hf_finv : ∀ n, f n ≠ n ↔ f⁻¹ n ≠ n
  . simp_rw [ne_comm, ne_eq, Equiv.Perm.eq_inv_iff_eq, eq_comm]
    exact fun n ↦ trivial
  have key : Nat.find hf = Nat.find hg
  . simp_rw [Nat.find_eq_iff, hf_finv, ← Nat.find_eq_iff hg]
  rw [key]
  have := support_min_lt_inv_apply f⁻¹ hg
  rw [inv_inv] at this
  exact this

lemma support_empty_iff_id {α : Type*} (f : Equiv.Perm α) :
  support f = ∅ ↔ f = 1 := by
  simp only [Set.eq_empty_iff_forall_not_mem, support,
              ne_eq, Set.mem_setOf_eq, not_not]
  exact Iff.symm Equiv.ext_iff

lemma unswap_support [DecidableEq α] (f : Equiv.Perm α) (a : α) :
  a ∉ support ((Equiv.swap a (f a)) * f) := by
  simp [support] at *

lemma unswap_support' [DecidableEq α] (f : Equiv.Perm α) (a : α) :
  support ((Equiv.swap a (f a)) * f) ⊆ support f := by
  simp [support] at *
  intro b
  contrapose!
  intro hbf
  rw [hbf]
  by_cases h : b = a
  . subst b
    simp [hbf]
  by_cases h' : b = f a
  . subst b
    simp
    apply f.injective hbf.symm
  apply Equiv.swap_apply_of_ne_of_ne h h'

def RepbleByWord_aux (s : Set ℕ) : Prop :=
  ∀ (f : Equiv.Perm ℕ), support f ⊆ s → RepbleByWord f

-- Every FinPerm is represented by a Word (constructed by induction on the support)
-- Note that this word is generally not reduced. However, the same proof technique
-- should work for ReducedWords if we go induct on the inversions set.
lemma repbleByWord_aux (s : Set ℕ) (hs : Set.Finite s) : RepbleByWord_aux s := by
  apply @Set.Finite.induction_on _ RepbleByWord_aux _ hs
  all_goals clear s hs
  . intros f hf
    rw [Set.subset_empty_iff, support_empty_iff_id] at hf
    subst hf
    exact ⟨_, idHasWord⟩
  . intros a s _ _ hs_repble f hf
    set g := (Equiv.swap a (f a)) * f with hg
    suffices hgs : support g ⊆ s
    obtain ⟨w, hw⟩ := hs_repble g hgs
    obtain ⟨w_swap, hw_swap⟩ := swapHasWord a (f a)
    use (w_swap ++ w)
    simp [Word_mul, hw_swap, hw, hg]
    . intro b hb
      by_cases h : b = a
      . subst b
        absurd (unswap_support f a)
        exact hb
      exact Set.mem_of_mem_insert_of_ne (hf (unswap_support' _ _ hb)) h
  done

-- Every FinPerm is represented by a Word (not necessarily reduced)
theorem repbleByWord (f : Equiv.Perm ℕ) (hf : (support f).Finite) : RepbleByWord f := by
  exact repbleByWord_aux _ hf f (subset_refl _)

end RepbleByWord

section Inversions

-- Inversions: we allow a < b or b < a
-- This definition could really apply to any map of ordered sets
def Inversions [LinearOrder α] (g : Equiv.Perm α) : Set (α × α) :=
  {p | (p.fst < p.snd ↔ g p.snd ≤ g p.fst)}

lemma mem_inversions [LinearOrder α] (g : Equiv.Perm α) (p : α × α) :
  p ∈ Inversions g ↔ (p.fst < p.snd ↔ g p.snd ≤ g p.fst) := by rfl

lemma mem_inversions' [LinearOrder α] (g : Equiv.Perm α) (a b : α) :
  (a, b) ∈ Inversions g ↔ (a < b ↔ g b ≤ g a) := by rfl

lemma not_mem_inversions_diag [LinearOrder α] (g : Equiv.Perm α) (a : α) :
  (a, a) ∉ Inversions g := by simp [mem_inversions']

lemma mem_inversions_symm [LinearOrder α] (g : Equiv.Perm α) (a b : α) :
  (a, b) ∈ Inversions g ↔ (b, a) ∈ Inversions g := by
  simp only [mem_inversions']
  wlog h : a < b
  . cases' eq_or_lt_of_le (le_of_not_lt h) with h' h'
    . simp [h']
    . rw [this _ _ _ h']
  have h' : g a ≠ g b := fun hg => h.ne (g.injective hg)
  simp [h, h.not_lt, h'.symm.le_iff_lt]

lemma mem_support_of_inversion [LinearOrder α] (g : Equiv.Perm α) (a b : α)
  (hab : (a, b) ∈ Inversions g) : a ∈ support g ∨ b ∈ support g := by
  simp only [mem_inversions', support, ne_eq, Set.mem_setOf_eq] at hab ⊢
  by_contra! hab'
  rw [hab'.1, hab'.2, ← not_le] at hab
  exact not_iff_self hab

lemma min_support_mem_inversions (f : Equiv.Perm ℕ) (hf : ∃ n, f n ≠ n) :
  (Nat.find hf, f⁻¹ (Nat.find hf)) ∈ Inversions f := by
  rw [mem_inversions']
  simp only [support_min_lt_inv_apply f hf, Equiv.Perm.apply_inv_self,
             (support_min_lt_apply f hf).le]

lemma exists_inversion_of_apply_lt (f : Equiv.Perm ℕ) (n : ℕ) (hn : f n < n) :
  ∃ m < n, (m, n) ∈ Inversions f := by
  suffices : ∃ m < n, n ≤ f m
  . obtain ⟨m, ⟨hmn, hm'⟩⟩ := this
    refine' ⟨m, hmn, _⟩
    simp [mem_inversions', hmn, (hn.trans_le hm').le]
  by_contra! h_lt
  have key1 : Finset.image f (Finset.range (n + 1)) ⊆ Finset.range n
  . intro _ hm
    simp only [Finset.mem_image, Finset.mem_range] at hm ⊢
    obtain ⟨m', ⟨hm', rfl⟩⟩ := hm
    cases' Nat.lt_succ_iff_lt_or_eq.mp hm' with hm' hm'
    . exact h_lt _ hm'
    . simp [hm', hn]
  replace key1 := Finset.card_le_card key1
  simp [Finset.card_image_of_injective _ f.injective, Finset.card_range] at key1

lemma inversions_empty_iff_support_empty (f : Equiv.Perm ℕ) :
  Inversions f = ∅ ↔ support f = ∅ := by
  rw [← not_iff_not]
  push_neg
  constructor
  . rintro ⟨⟨a, b⟩, hab⟩
    cases' mem_support_of_inversion _ _ _ hab with ha hb
    . exact ⟨_, ha⟩
    . exact ⟨_, hb⟩
  . exact fun hf => ⟨_, min_support_mem_inversions f hf⟩

lemma inversions_empty_iff_id (f : Equiv.Perm ℕ) :
  Inversions f = ∅ ↔ f = 1 :=
(inversions_empty_iff_support_empty f).trans (support_empty_iff_id f)

section StdInversions

-- Standard inversions (where we assume a < b)
def StdInversions [LinearOrder α] (g : Equiv.Perm α) : Set (α × α) :=
  {p | (p.fst < p.snd ∧ g p.snd ≤ g p.fst)}

lemma mem_stdinversions [LinearOrder α] (g : Equiv.Perm α) (p : α × α) :
  p ∈ StdInversions g ↔ (p.fst < p.snd ∧ g p.snd ≤ g p.fst) := by rfl

lemma mem_stdinversions' [LinearOrder α] (g : Equiv.Perm α) (a b : α) :
  (a, b) ∈ StdInversions g ↔ (a < b ∧ g b ≤ g a) := by rfl

lemma mem_stdinversions'' [LinearOrder α] (g : Equiv.Perm α) (a b : α) :
  (a, b) ∈ StdInversions g ↔ (a < b ∧ g b < g a) := by
  rw [mem_stdinversions']
  by_cases h : a = b
  . simp [h]
  . have h' : g a ≠ g b := fun hg => h (g.injective hg)
    simp [h, h'.symm.le_iff_lt]

lemma not_mem_stdinversions_diag [LinearOrder α] (g : Equiv.Perm α) (a : α) :
  (a, a) ∉ StdInversions g := by simp [mem_stdinversions']

-- The relationship between the inversions and the standard inversions
lemma stdinversions_inversions [LinearOrder α] (g : Equiv.Perm α) :
  Inversions g = StdInversions g ∪ Prod.swap ⁻¹' (StdInversions g) := by
  ext ⟨a, b⟩
  simp only [Set.mem_union, Set.mem_preimage, Prod.swap_prod_mk]
  by_cases hab : a = b
  . subst b
    simp [not_mem_stdinversions_diag, not_mem_inversions_diag]
  . push_neg at hab
    obtain (hab | hba) := hab.lt_or_lt
    . simp [mem_stdinversions', mem_inversions, hab, hab.not_lt]
    . rw [mem_inversions_symm]
      simp [mem_stdinversions', mem_inversions, hba, hba.not_lt]

end StdInversions

-- We should next try to show that a certain adjacency Equiv.swap deletes
-- an inversion.

end Inversions
