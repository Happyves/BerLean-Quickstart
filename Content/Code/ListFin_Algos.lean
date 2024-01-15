/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic
import Mathlib.Data.List.Sort


/-- Inserting x into list L at the first entry where it's smaller-/
def my_insert (x : ℕ) : List ℕ → List ℕ
| [] => [x]
| y :: l =>
    if x ≤ y
    then x :: (y :: l)
    else y :: (my_insert x l)

-- Sanity check
#eval my_insert 3 [1,2,3,4,5]

/-- The insertion-sort algorithm to order a list of natural numbers-/
def insertion_sort : List ℕ → List ℕ
| [] => []
| x :: l => my_insert x (insertion_sort l)

-- Sanity check
#eval insertion_sort [1,3,2,5,4,7,6]

/-- `y` is in the list obtained by inserting `x` into `l` iff it is either `x` or it is in `l` -/
lemma mem_insertion (x y: ℕ) (l : List ℕ) : y ∈ my_insert x l ↔ (y = x ∨ y ∈ l) :=
  by
  constructor
  · induction' l with z l ih
    · dsimp [my_insert]
      rw [List.mem_singleton]
      apply Or.inl
    · intro H
      dsimp [my_insert] at H
      split_ifs at H with Q
      · rw [List.mem_cons] at H
        exact H
      · rw [List.mem_cons] at H
        cases H with
        | inl lef =>
            right
            rw [lef]
            exact List.mem_cons_self z l
        | inr rig =>
            specialize ih rig
            cases ih with
            | inl a =>
                left
                exact a
            | inr b =>
                right
                exact List.mem_cons_of_mem z b
  · induction' l with z l ih
    · dsimp [my_insert]
      rw [List.mem_singleton]
      intro h
      cases h with
      | inl a => exact a
      | inr b => contradiction
    · intro H
      dsimp [my_insert]
      split_ifs with Q
      · cases H with
        | inl a =>
            rw [a]
            exact List.mem_cons_self x (z :: l)
        | inr b =>
            exact List.mem_cons_of_mem x b
      · cases H with
        | inl a =>
            apply List.mem_cons_of_mem z
            apply ih
            left
            exact a
        | inr b =>
            rw [List.mem_cons] at b
            cases b with
            | inl c =>
              rw [c]
              exact List.mem_cons_self z (my_insert x l)
            | inr d =>
                apply List.mem_cons_of_mem z
                apply ih
                right
                exact d

/-- If list `l` is sorted, then using `my_insert` to insert some number maintains this property -/
lemma insertion_maintains_sort (x: ℕ) (l : List ℕ) (hl : List.Sorted Nat.le l) :
  List.Sorted Nat.le (my_insert x l) :=
  by
  sorry

#check List.sorted_singleton
#check List.sorted_cons

-- I find case disjunction in Lean 4 a bit weird, so I need this technicallity
lemma technicallity (l : List ℕ): l = [] ∨ ∃ L : List ℕ, ∃ x : ℕ, l = x :: L :=
  by
  cases l with
  | nil =>
      left
      rfl
  | cons x L =>
      right
      use L
      use x

-- Correctness of the insertion-sort algorithm
example : ∀ l : List ℕ, List.Sorted Nat.le (insertion_sort l) :=
  by
  intro l
  induction' l with x l ih
  · dsimp [insertion_sort]
    apply List.sorted_nil
  · dsimp [insertion_sort]
    apply Or.elim (technicallity (insertion_sort l))
    · intro nil_case
      rw [nil_case]
      dsimp [my_insert]
      exact List.sorted_singleton x
    · rintro ⟨L, y, eq⟩
      rw [eq] at ih
      rw [eq]
      dsimp [my_insert]
      split_ifs with H
      · apply List.Pairwise.cons
        · intro z z_def
          rw [List.mem_cons] at z_def
          cases z_def with
          | inl lef =>
              rw [lef]
              apply H
          | inr rig =>
              rw [List.sorted_cons] at ih
              apply le_trans H
              exact ih.left z rig
        · exact ih
      · push_neg at H
        rw [List.sorted_cons] at *
        constructor
        · intro z z_def
          rw [mem_insertion] at z_def
          cases z_def with
          | inl a =>
            rw [a]
            exact le_of_lt H
          | inr b =>
              exact ih.left z b
        · exact insertion_maintains_sort x L ih.right

-- Powerful tools
#check List.foldl

def Automaton : ℕ → ℕ → ℕ
| 0, 1 => 1 --be in state 0, see a 1, go to state 1
| 1, 1 => 1
| 1, 2 => 2
| 2, 1 => 1
| 2, 3 => 3
| 3, _ => 3
| _, _ => 0

-- Sanity check
#eval List.foldl Automaton 0 [1,1,2,2,1,2,1,3,3]
#eval List.foldl Automaton 0 [1,1,2,2,1,2,1,2,3,1,2,4,5,6]
