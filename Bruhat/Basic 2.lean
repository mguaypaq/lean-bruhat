import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Set.Finite
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Logic.Basic
import Mathlib.Logic.Equiv.Defs

-- Finperm

def support {α : Type*} (f : Equiv.Perm α) : Set α :=
  {x : α | f x ≠ x}

def Finperm (α : Type*) :=
  {f : Equiv.Perm α | Set.Finite (support f) }

-- The type of words in the generators s₀, s₁, ...
def Word := List ℕ

def Word.toPerm : Word → Equiv.Perm ℕ :=
  FreeMonoid.lift fun i => Equiv.swap i (i+1)

-- All finitely supported permutations can be written as words
example : Set.range Word.toPerm = Finperm ℕ := sorry

-- The type of reduced words for a given permutation
structure ReducedWord (f : Equiv.Perm ℕ) where
  word : Word
  eq : word.toPerm = f
  min (other : Word) : other.toPerm = f → word.length ≤ other.length

def BruhatSubword (g h : Finperm ℕ) : Prop :=
  ∃ (gw : ReducedWord g) (hw : ReducedWord h), List.Sublist gw.word hw.word

def BruhatPrefix (g h : Finperm ℕ) : Prop :=
  ∃ (gw : ReducedWord g) (hw : ReducedWord h), List.IsPrefix gw.word hw.word

def BruhatSuffix (g h : Finperm ℕ) : Prop :=
  ∃ (gw : ReducedWord g) (hw : ReducedWord h), List.IsSuffix gw.word hw.word

-- These are partial orders on the set of finitely supported permutations
example : IsPartialOrder (Finperm ℕ) BruhatSubword := sorry

example : IsPartialOrder (Finperm ℕ) BruhatPrefix := sorry

example : IsPartialOrder (Finperm ℕ) BruhatSuffix := sorry
