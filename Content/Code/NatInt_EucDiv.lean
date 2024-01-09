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

-- Sanity checks
#eval quotient 8 3
#eval remainder 8 3

#eval quotient 9 3
#eval remainder 9 3

#eval quotient 1 3
#eval remainder 1 3

#eval quotient 0 3
#eval remainder 0 3

#eval quotient 8 0
#eval remainder 8 0

#eval quotient 0 0
#eval remainder 0 0


-- The Euclidean division
example (n k : ℕ) : (remainder n k) + k * (quotient n k) = n :=
  by
  by_cases Q : k = 0
  · rw [Q]
    rw [zero_mul, add_zero]
    rw [remainder]
    have Ifs_false : ¬ (0 < 0 ∧ 0 ≤ n) :=
      by
      push_neg
      intro problem
      exfalso
      exact (Nat.lt_irrefl 0) problem
    rw [dif_neg Ifs_false]
  · apply (@Nat.strong_induction_on (fun x => remainder x k + k * quotient x k = x) n)
    intro p ih
    replace Q := Nat.pos_of_ne_zero Q
    by_cases K : k ≤ p
    · rw [remainder, quotient]
      rw [dif_pos ⟨Q,K⟩]
      dsimp
      rw [if_pos ⟨Q,K⟩]
      have le_lem : p - k < p := Nat.sub_lt_of_pos_le Q K
      specialize ih (p-k) le_lem
      rw [mul_add, mul_one, ← add_assoc]
      rw [eq_comm] at *
      exact Nat.eq_add_of_sub_eq K ih
    · rw [remainder, quotient]
      have Ifs_false : ¬ (0 < k ∧ k ≤ p) :=
        by
        exact not_and_of_not_right (0<k) K
      rw [dif_neg Ifs_false, dif_neg Ifs_false]
      rw [mul_zero, add_zero]

#check Nat.mod_add_div -- Mathlib's version

-- The remainder is less then the divisor (is it ?)
example (n k : ℕ) : remainder n k < k :=
  by
  sorry
