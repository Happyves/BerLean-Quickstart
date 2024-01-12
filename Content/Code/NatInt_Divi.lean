/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic

import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.GCD.Basic

-- Divisibility
example (n m : ℤ)  : n ∣ m ↔ ∃ k, m = n*k := by rfl

-- def lemma
#check dvd_def
example (n m : ℤ)  : n ∣ m ↔ ∃ k, m = n*k := by rw [dvd_def]

-- Trying iff works too
#print Nat.Coprime
#check Nat.coprime_iff_gcd_eq_one

-- A first example
example (n m : ℤ)  : n ∣ m → m % n = 0 :=
  by
  intro h
  obtain ⟨k,eq⟩ := h
  rw [eq]
  exact Int.mul_emod_right n k

-- rintro
example (n m : ℤ)  : n ∣ m → m % n = 0 :=
  by
  rintro ⟨k,eq⟩
  rw [eq]
  exact Int.mul_emod_right n k

-- apply?
example (n m : ℤ)  : n ∣ m → m % n = 0 :=
  by
  apply Int.emod_eq_zero_of_dvd

-- rw?
example (n m : ℤ)  : n ∣ m ↔ m % n = 0 :=
  by
  rw [@EuclideanDomain.mod_eq_zero]

-- Actual definition of the primes
#print Nat.Prime

-- Casual definition of the primes
#check Nat.prime_def_lt''

-- The greatest common divisor
#check Nat.gcd

-- Defined algorithmically
#eval Nat.gcd 6 8

-- Infix notation
#eval (6 : ℕ).gcd 8

-- Infix notation (compare with `Nat.Prime n`) and norm_num
example (n : ℕ) (h : n = 7) : n.Prime := by rw [h] ; norm_num

-- Exercise 1
example (n p : ℕ) (hp : p.Prime) (hn : 0 < n) (hnp : n < p) : Nat.gcd n p = 1 :=
  by
  sorry

#check Nat.coprime_iff_gcd_eq_one
#check Nat.coprime_comm

-- Exercise 2
example (z : ℤ) : 0 ≤ max z (-z) :=
  by
  rw [Int.max_def]
  split_ifs with da_case
  · linarith
  · sorry

#check mul_comm
#check two_mul
#check neg_lt_iff_pos_add
#check nonneg_of_mul_nonneg_left
#check le_of_lt
