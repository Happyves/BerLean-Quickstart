/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


import Mathlib.Algebra.BigOperators.Order
import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Finset Nat
open BigOperators

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



/-- The Fermat numbers-/
def F : ℕ → ℕ := (fun n => 2^(2^n) + 1)

#eval F 7

/-- An evaluation lemma-/
lemma F₀:
  F 0 = 3 :=
  by
  sorry


/-- A technical lemma used to show the bound 2 < F n -/
lemma fermat_stricly_monotone {n : ℕ} :
  F n < F (n+1) :=
  by
  dsimp [F]
  sorry

#check add_lt_add_iff_right
#check Nat.pow_succ
#check pow_lt_pow_iff_right
#check one_lt_two
#check lt_mul_iff_one_lt_right
#check pow_pos


/-- A technical lemma used to handle subtraction of naturals,
    as well as the fact that F n ≠ 1 -/
lemma fermat_bound (n : ℕ) :
  2 < F n :=
  by
  induction' n with n ih
  · sorry
  · sorry

#check lt_trans

/-- Fermat numbers are odd-/
lemma fermat_odd {n : ℕ} :
  Odd (F n) :=
  by
  sorry

#check zero_lt_two
#check Nat.ne_of_gt
#check even_add_one
#check Nat.odd_iff_not_even
#check even_pow
#check not_not
#check even_two
#check pow_pos

/-- The recurence relation satisfied by Fermat numbers-/
lemma fermat_product (n : ℕ) :
  ∏ k in range n, F k = F n - 2 :=
  by
  induction' n with n ih
  · decide
  · rw [prod_range_succ]
    rw [ih]
    -- We prove a form without subtraction of naturals
    have h : (F n)*(F n) + 2 = (F n.succ) + 2 * (F n) :=
      by
      dsimp [F]
      rw [succ_eq_add_one]
      ring
    have h_natsub := le_of_lt (fermat_bound n.succ)
    rw [Nat.mul_sub_right_distrib]
    apply Nat.sub_eq_of_eq_add
    rw [← Nat.sub_add_comm h_natsub]
    rw [Nat.sub_eq_of_eq_add]
    exact h.symm


/--
Fermat numbers are coprime.

This follows from the recurrence relations and divisibility,
as well as the parity of Fermat numbers.
-/
lemma fermat_coprimes  (k n : ℕ) (h : k < n):
  Coprime (F n) (F k) :=
  by
  -- Some notation and facts to ease exposition
  let m := (F n).gcd (F k)
  have h_n : m ∣ F n := (F n).gcd_dvd_left (F k)
  have h_k : m ∣ F k := (F n).gcd_dvd_right (F k)
  -- This will contradict Fermat numbers parity
  have h_m : m ∣ 2 :=
    -- The gcd divides the product of Fermat numbers up n-1
    -- since it divides the kth term
    by
    have h_m_prod : m ∣ (∏ k in range n, F k) :=
      by
      sorry
    -- This product is also found in:
    have h_prod : (∏ k in range n, F k) + 2 = F n :=
      by
      sorry
    -- Hence we can use divisibility of linear combinations
    -- to conclude with our claim.
    apply (Nat.dvd_add_right h_m_prod).mp
    rw [h_prod]
    exact h_n
  have h_one_or_two := (dvd_prime prime_two).mp h_m
  cases' h_one_or_two with h_one h_two
  · exact h_one
  -- This is where the Fermat numbers parity, which we derived from
  -- their closed form, comes into play.
  · exfalso
    rw [h_two] at h_n
    have h_even : Even (F n) := even_iff_two_dvd.mpr h_n
    have h_odd : Odd (F n) := fermat_odd
    exact (even_iff_not_odd.mp h_even) h_odd

#check lt_trans
#check dvd_trans
#check mem_range
#check Nat.sub_add_cancel


/-- A technical lemma to allow for the use of `nat.exists_prime_and_dvd`
    on Fermat numbers -/
lemma fermat_neq (n : ℕ) :
   F n ≠ 1 :=
  by
  intro con
  linarith [fermat_bound n]


theorem second_proof :
  ∃ (P : ℕ → ℕ),
  (∀ k, (P k).Prime) ∧
  (∀ k, ∀ q, k≠q → (P k) ≠ (P q))
  :=
  by
  let prime_dvds := (fun n => @exists_prime_and_dvd (F n) (fermat_neq n))
  obtain ⟨P, Pprop⟩ := Classical.axiom_of_choice prime_dvds
  dsimp at *
  clear prime_dvds
  use P
  constructor
  · intro k
    exact (Pprop k).1
  · intros k q knq problem
    wlog C : k < q with Symmetry
    · specialize Symmetry P Pprop q k
      specialize Symmetry (Ne.symm knq)
      specialize Symmetry (Eq.symm problem)
      specialize Symmetry (lt_of_le_of_ne (not_lt.mp C) (Ne.symm knq))
      exact Symmetry
    · have h_prime := (Pprop k).1
      have h_dvd_1 := (Pprop k).2
      have h_dvd_2 := (Pprop q).2
      rw [← problem] at h_dvd_2
      have promblemo := eq_one_of_dvd_coprimes (fermat_coprimes k q C) h_dvd_2 h_dvd_1
      exact (Nat.Prime.ne_one h_prime) promblemo


lemma second_proof_standardised :
  {n : ℕ | n.Prime }.Infinite :=
  by
  set f := Classical.choose second_proof with f_def
  have f_prop := Classical.choose_spec second_proof
  rw [← f_def] at f_prop
  apply @Set.infinite_of_injective_forall_mem ℕ ℕ _ {n : ℕ | n.Prime } f
  · rw [Function.Injective]
    intros a b
    contrapose
    rw [← Ne.def]
    exact f_prop.2 a b
  · dsimp
    exact f_prop.1
