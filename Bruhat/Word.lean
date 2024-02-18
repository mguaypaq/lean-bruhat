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
  f a = a := by
  by_contra ha'
  exact ha ha'

lemma id_iff_support_empty {α : Type*} (f : Equiv.Perm α) :
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
    rw [Set.subset_empty_iff, id_iff_support_empty] at hf
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

-- could really apply to any map of ordered sets
-- the symmetric definition actually seems kind of painful to work with
-- but we wanted it for the formula
def Inversions [LinearOrder α] (g : Equiv.Perm α) : Set (α × α) :=
  {p | p.fst ≠ p.snd ∧ (p.fst < p.snd ↔ g p.snd < g p.fst)}

lemma mem_inversions [LinearOrder α] (g : Equiv.Perm α) (p : α × α) :
  p ∈ Inversions g ↔ p.fst ≠ p.snd ∧ (p.fst < p.snd ↔ g p.snd < g p.fst) := by rfl

lemma mem_inversions' [LinearOrder α] (g : Equiv.Perm α) (a b : α) :
  (a, b) ∈ Inversions g ↔ a ≠ b ∧ (a < b ↔ g b < g a) := by rfl

lemma notmem_inversions [LinearOrder α] (g : Equiv.Perm α) (p : α × α) :
  p ∉ Inversions g ↔ p.fst = p.snd ∨ ¬(p.fst < p.snd ↔ g p.snd < g p.fst) := by
  rw [Inversions, Set.mem_setOf_eq, ne_eq, not_and_or, not_not]

lemma notmem_inversions' [LinearOrder α] (g : Equiv.Perm α) (a b : α) :
  (a, b) ∉ Inversions g ↔ a = b ∨ ¬(a < b ↔ g b < g a) := by
  rw [Inversions, Set.mem_setOf_eq, ne_eq, not_and_or, not_not]

lemma notmem_inversions_diag [LinearOrder α] (g : Equiv.Perm α) (a : α) :
  (a, a) ∉ Inversions g := by simp [Inversions]

lemma mem_inversions_of_lt [LinearOrder α] (g : Equiv.Perm α)
  {a b : α} (hab : a < b) :
  (a, b) ∈ Inversions g ↔ g b < g a := by
  rw [Inversions, Set.mem_setOf_eq, ne_eq]
  simp [hab, hab.ne]

lemma not_mem_inversions_of_lt [LinearOrder α] (g : Equiv.Perm α)
  {a b : α} (hab : a < b) :
  (a, b) ∉ Inversions g ↔ g a < g b := by
  rw [mem_inversions_of_lt g hab, not_lt, le_iff_eq_or_lt, or_iff_right]
  exact fun hg ↦ hab.ne (g.injective hg)

lemma mem_inversions_symm [LinearOrder α] (g : Equiv.Perm α) (a b : α) :
  (a, b) ∈ Inversions g ↔ (b, a) ∈ Inversions g := by
  by_cases h : a = b
  . subst b
    simp [notmem_inversions_diag]
  change a ≠ b at h
  wlog hlt : a < b with key
  . push_neg at hlt
    specialize key g b a h.symm (hlt.lt_of_ne h.symm)
    rw [key]
  rw [mem_inversions_of_lt g hlt, mem_inversions', and_iff_right h.symm]
  simp [hlt.not_lt, le_iff_eq_or_lt, or_iff_right h.symm]

def SInversions [LinearOrder α] (g : Equiv.Perm α) : Set (α × α) :=
  {p | p.fst < p.snd ∧ g p.snd < g p.fst}

def SSInversions [LinearOrder α] (g : Equiv.Perm α) : Set (α × α) :=
  {p | p.fst < p.snd ↔ g p.snd ≤ g p.fst}

lemma inversions_empty_iff_increasing (f : Equiv.Perm ℕ) :
  Inversions f = ∅ ↔ ∀ a b, a < b → f a < f b := by
  simp_rw [Set.eq_empty_iff_forall_not_mem]
  constructor
  . intros hinv a b hab
    specialize hinv (a, b)
    exact (not_mem_inversions_of_lt _ hab).mp hinv
  rintro h ⟨a, b⟩
  by_cases h : a = b
  . subst b
    simp [Inversions]
  cases' Nat.lt_or_lt_of_ne h with h h

lemma inversions_empty_iff_id (f : Equiv.Perm ℕ) :
  Inversions f = ∅ ↔ f = 1 := by
  rw [inversions_empty_iff_increasing]
  constructor
  . intro hf_incr
    ext n
    apply Nat.strongInductionOn n
    clear n
    intros n hn
    cases' lt_or_le n (f⁻¹ n) with h h
    . specialize hf_incr _ _ h
      simp only [Equiv.Perm.apply_inv_self] at hf_incr
      apply f.injective (hn _ hf_incr)
    cases' eq_or_lt_of_le h with h h
    . nth_rewrite 1 [← h]
      simp
    specialize hn _ h
    simp at hn
    nth_rewrite 1 [hn]
    simp
  . rintro rfl
    simp
  done



example [LinearOrder α] (g : Equiv.Perm α) :
  Inversions g = SInversions g ∪ Prod.swap ⁻¹' (SInversions g) := by
  ext ⟨i, j⟩
  simp [Inversions, SInversions]
  -- cases lt_or_eq_or_lt i j
  obtain (hlt | hle) := lt_or_le i j
  . sorry
  obtain (rfl | hlt) := eq_or_lt_of_le hle
  . aesop
  . simp [hlt.ne.symm, hlt, hlt.not_lt]
    rw [le_iff_lt_or_eq]
    aesop

example (g : Equiv.Perm ℕ) (i : ℕ) (hi : g i = i) : (i, g i) ∉ Inversions g := by
  simp [Inversions, hi]
example (g : Equiv.Perm ℕ) (i j : ℕ) (hij : i < j) (gij : g j < g i) :
  (i, j) ∈ Inversions g := by
  simp [Inversions, hij, gij, hij.ne]
example (g : Equiv.Perm ℕ) (i j : ℕ) (hij : j < i) (gij : g i < g j) :
  (i, j) ∈ Inversions g := by
  simp [Inversions, hij.not_lt, gij.not_lt, hij.ne.symm, gij.ne]
