/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic

/-- The quotient of n by m in the Euclidean division-/
def quotient (n m : ℕ) : ℕ :=
  if h : 0 < m ∧ m ≤ n
  then
    have fact : n - m < n := Nat.div_rec_lemma h
    (quotient (n - m) m) + 1
  else
    0

/-- The remainder of n by m in the Euclidean division-/
def remainder (n m : ℕ) : ℕ :=
  if h : 0 < m ∧ m ≤ n
  then
    have fact : n - m < n := Nat.div_rec_lemma h
    remainder (n - m) m
  else
    n

-- The remainder is less then the divisor (is it ?)
example (n k : ℕ) (k_pos : 0 < k) : remainder n k < k :=
  by
  apply @Nat.strong_induction_on (fun x => remainder x k < k) n
  intro p ih
  rw [remainder]
  by_cases Q : k ≤ p
  · rw [dif_pos ⟨k_pos,Q⟩]
    dsimp
    have le_lem : p - k < p := Nat.sub_lt_of_pos_le k_pos Q
    exact ih (p-k) le_lem
  · rw [dif_neg (not_and_of_not_right (0<k) Q)]
    push_neg at Q
    exact Q
