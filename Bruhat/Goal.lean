import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs

-- Finperm

lemma perm_conj {α : Type*} (f g : Equiv.Perm α) (a b : α) (hab : f a = b) :
  g (f (g.symm (g a))) = (g b) := by
    rw [Equiv.symm_apply_apply, hab]

lemma swap_conj {α : Type*} [DecidableEq α] (a b c d : α) :
  (Equiv.swap a b) * (Equiv.swap c d) * (Equiv.swap a b) =
  Equiv.swap (Equiv.swap a b c) (Equiv.swap a b d) := by
  rw [Equiv.swap_apply_apply]
  rfl

def support {α : Type*} (f : Equiv.Perm α) : Set α :=
  {x | f x ≠ x}

def finperm (α : Type*) : Set (Equiv.Perm α) :=
  {f | Set.Finite (support f) }

def transposition (α : Type*) [DecidableEq α] : Set (Equiv.Perm α) :=
  {f | ∃ x y, x ≠ y ∧ f = Equiv.swap x y}

-- The type of words in the generators s₀, s₁, ... of adjacency transpositions
def Word := FreeMonoid ℕ

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

-- All finitely supported permutations can be written as words
example : Set.range Word.toPerm = finperm ℕ := sorry

-- The type of reduced words for a given permutation
structure ReducedWord (f : Equiv.Perm ℕ) where
  word : Word
  eq : word.toPerm = f
  min (other : Word) : other.toPerm = f → word.length ≤ other.length

noncomputable def BruhatLength (f : Equiv.Perm ℕ) : ℕ :=
  sInf (List.length '' (Word.toPerm ⁻¹' {f}))

lemma idHasWord : Word.toPerm [] = 1 := rfl

lemma unswap_support [DecidableEq α] (f : Equiv.Perm α) (a : α) :
  a ∉ support ((Equiv.swap a (f a)) * f) := by
  simp [support] at *

def RepbleByWord (S : Set ℕ) : Prop :=
  ∀ (f : Equiv.Perm ℕ), support f ⊆ S → ∃ w : Word, w.toPerm = f

lemma wordsByInduction (S : Set ℕ) (n : ℕ) (hS : RepbleByWord S) :
  RepbleByWord (insert n S) := sorry
--   intros f hfS
--   by_cases h : n ∈ support f
--   . specialize hS ((Equiv.swap n (f n)) * f) sorry
--     obtain ⟨w, hw⟩ := hS
--     -- use (Equiv.swap n (f n) :: w)
--     sorry
--   . apply hS f ((Set.subset_insert_iff_of_not_mem h).mp hfS)

-- def HasWord (f : finperm ℕ) : ∃ w : Word, w.toPerm = f := by
--   obtain ⟨f, hf : Set.Finite _⟩ := f
--   set s := support f
--   apply Set.Finite.induction_on


def BruhatSubword (g h : finperm ℕ) : Prop :=
  ∃ (gw : ReducedWord g) (hw : ReducedWord h), List.Sublist gw.word hw.word

def BruhatPrefix (g h : finperm ℕ) : Prop :=
  ∃ (gw : ReducedWord g) (hw : ReducedWord h), List.IsPrefix gw.word hw.word

def BruhatSuffix (g h : finperm ℕ) : Prop :=
  ∃ (gw : ReducedWord g) (hw : ReducedWord h), List.IsSuffix gw.word hw.word

section EquivalentDefinitionsForBruhatSubword

def BruhatSubwordForAll (g h : finperm ℕ) : Prop :=
  ∀ (hw : ReducedWord h), ∃ (gw : ReducedWord g), List.Sublist gw.word hw.word

def RankTable (f : Equiv.Perm ℕ) (i j : ℕ) : ℕ :=
  ((Finset.range i).filter (fun i' => f i' < j)).card

def BruhatSubwordRankTable (g h : finperm ℕ) : Prop :=
  RankTable g ≤ RankTable h

section EquivalentDefinitionsForBruhatPrefixAndSuffix

def BruhatPrefixForAll (g h : finperm ℕ) : Prop :=
  ∀ (gw : ReducedWord g), ∃ (hw : ReducedWord h), List.IsPrefix gw.word hw.word

def BruhatSuffixForAll (g h : finperm ℕ) : Prop :=
  ∀ (gw : ReducedWord g), ∃ (hw : ReducedWord h), List.IsSuffix gw.word hw.word

def Inversions [LinearOrder α] (g : Equiv.Perm α) : Set (α × α) :=
  {p | p.fst ≠ p.snd ∧ (p.fst < p.snd ↔ g p.snd < g p.fst)}

def SInversions [LinearOrder α] (g : Equiv.Perm α) : Set (α × α) :=
  {p | p.fst < p.snd ∧ g p.snd < g p.fst}

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

def BruhatSuffixInversions (g h : Equiv.Perm ℕ) : Prop :=
  Inversions g ⊆ Inversions h

lemma inversions_mul (f g : Equiv.Perm ℕ) :
  Inversions (f * g) = (Prod.map g.symm g.symm '' Inversions f) ∩ Inversions g := by
  sorry

-- These are partial orders on the set of finitely supported permutations
example : IsPartialOrder (finperm ℕ) BruhatSubword' := sorry

example : IsPartialOrder (finperm ℕ) BruhatPrefix := sorry

example : IsPartialOrder (finperm ℕ) BruhatSuffix := sorry
