/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic

import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.GCD.Basic


-- Exercise 1
example (n p : ℕ) (hp : p.Prime) (hn : 0 < n) (hnp : n < p) : Nat.gcd n p = 1 :=
  by
  rw [← Nat.coprime_iff_gcd_eq_one]
  rw [Nat.coprime_comm]
  exact Nat.coprime_of_lt_prime hn hnp hp

-- Exercise 2
example (z : ℤ) : 0 ≤ max z (-z) :=
  by
  rw [Int.max_def]
  split_ifs with da_case
  · linarith
  · push_neg at da_case
    rw [neg_lt_iff_pos_add] at da_case
    rw [← two_mul] at da_case
    rw [mul_comm] at da_case
    apply nonneg_of_mul_nonneg_left (le_of_lt da_case)
    decide
