/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic
import Mathlib.Data.List.Sort

-- Lists
inductive list (α : Type u) where
| nil : list α
| cons (head : α) (tail : list α) : list α

/-- The list [1,2,3] -/
def my_list : list ℕ := list.cons 1 (list.cons 2 (list.cons 3 (list.nil)))

-- Mathlib's lists
#check [1,2,3]

/-- Length of a list-/
def list.length : list α → ℕ
| list.nil => 0
| list.cons x l => 1 + list.length l

-- Sanity check
#eval list.length my_list

/-- Concatenating lists -/
def list.concat : list α → list α → list α
| list.nil , l => l
| list.cons x l , L => list.cons x (list.concat l L)

-- Sanity check
#reduce list.concat my_list my_list

-- Mathlib's version
#check List.append
-- and its notation
#eval [1,2,3] ++ [1,2,3]

-- Proving facts about lists !
example (l s: list ℕ) : (list.concat l s).length = l.length + s.length :=
  by
  induction' l with x l ih
  · dsimp [list.length, list.concat]
    rw [zero_add]
  · dsimp [list.length, list.concat]
    rw [ih]
    rw [add_assoc]

-- Exercise
example (l s: list ℕ) : list.concat l list.nil = l :=
  by
  sorry

/-- Membership in a list -/
inductive list.mem (x : α) : list α → Prop
| head (l : list α) : list.mem x (list.cons x l)
| tail (y : α) {l : list α} : list.mem x l → list.mem x (list.cons y l)

-- Sanity check
example : list.mem 2 my_list :=
  by
  rw [my_list]
  apply list.mem.tail
  apply list.mem.head

-- Mathlib's version
#check List.Mem
-- and its notation
#check 2 ∈ [1,2,3]

/-- Lists has its entries sorted increasingly-/
inductive list.sorted : list ℕ → Prop
| empty_case : list.sorted list.nil
| cons_case :
    (∀ y : ℕ, list.mem y l → x ≤ y) → (list.sorted l) → list.sorted (list.cons x l)

-- Proving that a list is sorted
example : list.sorted my_list :=
  by
  rw [my_list]
  apply list.sorted.cons_case
  · intro y y_def
    cases y_def with
    | head => decide -- one has to use the constructor name
    | tail _ l => -- if the second input in list.mem.tail is implicit, this fails XD
      cases l with
      | head => decide
      | tail _ l => contradiction
  · apply list.sorted.cons_case
    · intro y y_def
      cases y_def with
      | head => decide
      | tail _ l => contradiction
    · apply list.sorted.cons_case
      · intro y y_def
        contradiction
      · apply list.sorted.empty_case

-- Alternative 1
example : list.sorted my_list :=
  by unhygienic
  rw [my_list]
  apply list.sorted.cons_case
  · intro y y_def
    cases' y_def
    · decide
    · cases' a
      · decide
      · contradiction
  · apply list.sorted.cons_case
    · intro y y_def
      cases' y_def
      · decide
      · contradiction
    · apply list.sorted.cons_case
      · intro y y_def
        contradiction
      · apply list.sorted.empty_case

-- Alternative 2
example : list.sorted my_list :=
  by
  rw [my_list]
  apply list.sorted.cons_case
  · intro y y_def
    cases' y_def
    · decide
    · rename_i y_def
      cases' y_def
      · decide
      · contradiction
  · apply list.sorted.cons_case
    · intro y y_def
      cases' y_def
      · decide
      · contradiction
    · apply list.sorted.cons_case
      · intro y y_def
        contradiction
      · apply list.sorted.empty_case

-- Mathlib's version...
#check List.Sorted
-- ...is just an alias for
#check List.Pairwise

-- Automation!
example : List.Pairwise (fun a b => a ≠ b) [4,1,7] :=
  by
  decide

-- Exercise
example (l : list ℕ) : (∃ x, list.mem x l) → l.length ≠ 0 :=
  by
  sorry

-- Hint
example (x : ℕ) : 2 + x ≠ 0 := by norm_num
