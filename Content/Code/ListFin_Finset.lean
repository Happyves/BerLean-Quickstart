/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Slice

-- Propety of having pairwise different elements
#check List.Nodup

-- Lifted to multisets
#check Multiset.Nodup

/-- A finite set-/
structure finset (α : Type) where
  val : Multiset α
  nodup : Multiset.Nodup val

-- Mathlib's version
#check Finset

-- How to build one
def my_finset : finset ℕ where
  val := {1,2,3}
  nodup :=
    by
    --decide -- Works! But let's take a walk:
    rw [Multiset.nodup_iff_pairwise]
    dsimp [Multiset.Pairwise]
    use [1,2,3]
    constructor
    · rfl
    · decide

-- Structures and suffixes
#check my_finset
#check my_finset.val
#check my_finset.nodup

/-- Union of finite sets-/
def my_union (s t : finset ℕ) : finset ℕ where
  val := Multiset.ndunion s.val t.val
  nodup :=
    by
    apply Multiset.Nodup.ndunion
    exact t.nodup

-- Sanity check
#reduce my_union my_finset {val := {1,2,4}, nodup := by decide}

-- Size of a finite set
#check Finset.card

-- Size of a multiset
#check Multiset.card

-- Is evaluable
#eval ({1,2,3} : Finset ℕ).card

-- mainstream notion of finiteness
#check Finset.card_congr
#check Finset.image
#check Finset.image_val_of_injOn
#check Multiset.Nodup.map_on

-- Subsets
example (a b : Finset ℕ ) (h : a = b) : a ⊆ b :=
  by
  rw [h]

example (a b : Finset ℕ ) (h : a = b) : ¬ (a ⊂ b) :=
  by
  rw [h]
  exact ssubset_irrfl

-- Operations
example (a b : Finset ℕ ) (h : a = b) : a ∩ b = a :=
  by
  rw [h]
  exact Finset.inter_self b

example (a b : Finset ℕ ) (h : a = b) : a \ b = ∅ :=
  by
  rw [h]
  exact Finset.sdiff_self b

example (a : Finset ℕ ) :
  Finset.disjUnion a ∅ (by exact Finset.disjoint_empty_right a) = a :=
  by
  exact Finset.disjUnion_empty a (Finset.disjoint_empty_right a)


-- Filtering
#check Finset.filter

#eval ({1,2,3,4,5,6,7,8} : Finset ℕ).filter Nat.Prime

#eval ({1,2,3,4,5,6,7,8} : Finset ℕ).filter (fun x => x^3 + 2 = x + 8)

#check_failure ({1,2,3,4,5,6,7,8} : Finset ℕ).filter (fun x => ∃ y, y ∣ x)

#check_failure ({1,2,3,4,5,6,7,8} : Finset ℕ).filter (fun n => ∃ x, ∃ y, ∃ z, x^n + y^n = z^n)

open Classical in
#check ({1,2,3,4,5,6,7,8} : Finset ℕ).filter (fun x => ∃ y, y ∣ x)

-- Decidability
instance : DecidablePred (fun x : ℕ => ∃ y, y ∣ x) :=
  by
  intro x
  apply isTrue
  dsimp
  use x

#eval ({1,2,3,4,5,6,7,8} : Finset ℕ).filter (fun x => ∃ y, y ∣ x)

instance : DecidablePred (fun x : ℕ => ∃ y, y < x ∧ y ∣ x) :=
  by
  intro x
  cases x with
  | zero =>
    apply isFalse
    dsimp
    push_neg
    intro y problem
    exfalso
    exact (Nat.not_lt_zero y) problem
  | succ n =>
    cases n with
    | zero =>
      apply isFalse
      dsimp
      push_neg
      intro y problem
      rw [Nat.lt_one_iff] at problem
      rw [problem]
      decide
    | succ m =>
      apply isTrue
      use 1
      constructor
      · norm_num
      · exact Nat.one_dvd (Nat.succ (Nat.succ m))

#check_failure (fun (α : Type) (a : α) (s : Finset α) => s.filter (fun x => x = a))

open Classical in
#check (fun (α : Type) (a : α) (s : Finset α) => s.filter (fun x => x = a))

#check (fun (α : Type) [DecidableEq α] (a : α) (s : Finset α) => s.filter (fun x => x = a))

#check ({(2+2=4), (∀n : ℕ, n ≥ 2 →  ∃ x: ℤ, ∃ y, ∃ z, x^n + y^n = z^n)} : Finset Prop)

#check ({(2+2=4), (∀n : ℕ, n ≥ 2 → ∃ x: ℤ, ∃ y, ∃ z, x^n + y^n = z^n)} : Finset Prop).filter (fun x => x = True)

-- What the syntax for finite sets means:
#check insert 1 ({2,3} : Finset ℕ)

-- Extracting elements from finite sets
example (x : ℕ) (h : x ∈ ({2,4,6} : Finset ℕ)) : Even x :=
  by
  rw [Finset.mem_insert] at h
  cases h with
  | inl h =>
      rw [h]
      decide
  | inr h =>
      rw [Finset.mem_insert] at h
      cases h with
      | inl h =>
          rw [h]
          decide
      | inr h =>
          rw [Finset.mem_singleton] at h
          rw [h]
          decide

-- Automation!
example (x : ℕ) (h : x ∈ ({2,4,6} : Finset ℕ)) : Even x :=
  by
  fin_cases h <;> decide

-- {0,...,n}
#eval Finset.range 5

-- Intervals
#eval Finset.Icc  1 5
#eval Finset.Ico  1 5
#eval Finset.Ioo  1 5
#eval Finset.Ioc  1 5
#eval Finset.Icc  (-2) 5
#check Finset.Icc  (-2) 5

-- The powerset
#eval Finset.powerset {1,2,3}
-- is based on
#eval List.sublists [1,2,3]

-- Slices
#eval Finset.powersetCard 2 {1,2,3}
#check Finset.slice

-- Lots of API
example (a b : Finset ℕ ): a ∩ b = a.filter (fun x => x ∈ b) :=
  by
  rw [Finset.filter_mem_eq_inter]

-- Exercise
open Finset in
example (a b : Finset ℕ ): a ∩ b = a.filter (fun x => x ∈ b) :=
  by
  ext x
  sorry

#check Finset.mem_filter
#check Finset.mem_inter

-- Sets
#check Set

#check Set ℤ

#check Set.union

#check {n : ℕ | n.Prime}

-- Relation to finiteness
#check Finset.toSet

-- Finset membership
#check 2 ∈ ({2,3} : Finset ℕ)

#check Set.Finite

structure set.finite {α : Type } (s : Set α) where
  elems : Finset α
  prop : ∀ x, x ∈ s → x ∈ elems

#check Set.Finite.toFinset

#check Finite
