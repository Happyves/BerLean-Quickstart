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


/-- Length of a list-/
def list.length : list α → ℕ
| list.nil => 0
| list.cons x l => 1 + list.length l

/-- Concatenating lists -/
def list.concat : list α → list α → list α
| list.nil , l => l
| list.cons x l , L => list.cons x (list.concat l L)


-- Exercise
example (l s: list ℕ) : list.concat l list.nil = l :=
  by
  induction' l with x l ih
  · dsimp [list.concat]
  · dsimp [list.concat]
    rw [ih]

/-- Membership in a list -/
inductive list.mem (x : α) : list α → Prop
| head (l : list α) : list.mem x (list.cons x l)
| tail (y : α) {l : list α} : list.mem x l → list.mem x (list.cons y l)

-- Exercise
example (l : list ℕ) : (∃ x, list.mem x l) → l.length ≠ 0 :=
  by
  rintro ⟨x, x_prop⟩
  cases x_prop with
  | head =>
      dsimp [list.length]
      norm_num
  | tail _ l =>
      dsimp [list.length]
      norm_num
