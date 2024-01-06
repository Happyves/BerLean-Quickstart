/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


-- Ignore these for now
import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

-- Ignore these as well
open Finset Nat
open BigOperators


-- First example
example (n m: ℕ) (hn : Even n) (hm : Even m) : Even (n+m) :=
  by
  rw [even_iff]
  rw [even_iff] at hn hm
  rw [add_mod]
  rw [hn, hm]
  rfl

-- Alternative ways to use rw
example (n m: ℕ) (hn : Even n) (hm : Even m) : Even (n+m) :=
  by
  rw [even_iff, add_mod]
  rw [even_iff] at hn
  rw [even_iff] at hm
  rw [hm]
  rw [hn]
  rfl

 -- Apply, exact and one more use of rw
lemma my_lemma (n m: ℕ) (hn : Odd n) (hm : Odd m) : Odd (n*m) :=
  by
  rw [odd_iff] at *
  apply odd_mul_odd
  · exact hn
  · exact hm

-- Shorter syntax
example (n m: ℕ) (hn : Odd n) (hm : Odd m) : Odd (n*m) :=
  by
  rw [odd_iff] at *
  apply odd_mul_odd <;> assumption

-- Using `my_lemma` in a proof
example (n : ℕ) (hn : Odd n)  : Odd (n*3) :=
  by
  apply my_lemma
  · exact hn
  · rw [odd_iff]
    rfl

-- Using a composite lemma
example (a : ℕ) (ha : Odd a)  : Odd (a*3) :=
  by
  apply my_lemma a _ ha
  rw [odd_iff]
  rfl

-- Ignore this, its for aesthetics in what follows
lemma proof_of_oddity_3 : Odd 3 := by rw [odd_iff] ; rfl
lemma proof_of_oddity_5 : Odd 5 := by rw [odd_iff] ; rfl
-- Checks
#check my_lemma
#check my_lemma 3
#check my_lemma 3 5
#check my_lemma 3 5 proof_of_oddity_3
#check my_lemma 3 5 proof_of_oddity_3 proof_of_oddity_5

-- Have and exact
example (n : ℕ) (hn : Odd n)  : Odd (n*3) :=
  by
  have H : Odd 3 :=
    by
    rw [odd_iff]
    rfl
  exact my_lemma n 3 hn H

-- Have without goal
example (n : ℕ) (hn : Odd n)  : Odd (n*3) :=
  by
  have H : Odd 3 :=
    by
    rw [odd_iff]
    rfl
  have Goal := my_lemma n 3 hn H
  exact Goal

-- First part of Euclids proof of the infinitude of primes
theorem Euclid_proof :
  ∀ (s : Finset ℕ), ∃ p, Nat.Prime p ∧ p ∉ s :=
  by
  intro s
  by_contra! h
  set s_primes := (s.filter Nat.Prime) with s_primes_def
  -- Let's add a membership definition lemma to ease exposition
  have mem_s_primes : ∀ {n : ℕ}, n ∈ s_primes ↔  n.Prime :=
    by
    intro n
    rw [s_primes_def, mem_filter, and_iff_right_iff_imp]
    --simp [s_primes_def],
      --alternative to the previous line
    exact h n
  -- In order to get a prime factor from `nat.exists_prime_and_dvd`, we need:
  have condition : (∏ i in s_primes, i) + 1 ≠ 1 :=
    by
    intro con
    rw [add_left_eq_self] at con
    have however : 0 < (∏ i in s_primes, i) :=
      by
      apply prod_pos
      intro n ns_primes
      apply Prime.pos
      exact (mem_s_primes.mp ns_primes)
    apply lt_irrefl 0
    nth_rewrite 2 [← con]
    exact however
  obtain ⟨p, pp, pdvd⟩ := (exists_prime_and_dvd condition)
  -- The factor also divides the product:
  have : p ∣ (∏ i in s_primes, i) :=
    by
    apply dvd_prod_of_mem
    rw [mem_s_primes]
    apply pp
  -- Using the properties of divisibility, we reach a contradiction thorugh:
  have problem : p ∣ 1 :=
    by
    convert dvd_sub' pdvd this
    rw [add_tsub_cancel_left]
  exact (Nat.Prime.not_dvd_one pp) problem


-- Infinitude of primes
lemma Euclid_proof_standardised :
  {n : ℕ | Nat.Prime n }.Infinite :=
  by
  rw [Set.Infinite]
  intro con
  obtain ⟨p, ⟨p_prop, p_mem⟩⟩ := Euclid_proof (Set.Finite.toFinset con)
  apply p_mem
  rw [Set.Finite.mem_toFinset con]
  dsimp
  exact p_prop
