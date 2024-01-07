/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/


-- Ignore these for now
import Mathlib.Tactic

-- Ignore this as well
open Nat


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

-- Introduction
example : ∀ n : ℕ, Odd n → Odd (n*3) :=
  by
  intro n hn
  exact my_lemma n 3 hn proof_of_oddity_3

-- Reverting
example (n : ℕ) (hn : Odd n)  : Odd (n*3) :=
  by
  revert hn
  intro H
  exact my_lemma n 3 H proof_of_oddity_3

-- Specialising
example
  (a : ℕ) (ha : Odd a) (fact : ∀ n m : Nat, Odd n → Odd m → Odd (n*m)) :
  Odd (a*3) :=
  by
  specialize fact a
  specialize fact 3 ha
  exact fact proof_of_oddity_3

-- Use
example (n : ℕ) : ∃ m : ℕ, n < m :=
  by
  use n+1
  apply lt_succ_self

-- Cases and rw
example (n : ℕ) (h : ∃ m, n = m+m) : Even n :=
  by
  cases' h with m eq
  rw [← two_mul] at eq
  rw [even_iff_exists_two_mul]
  use m

-- Obtain
example (n : ℕ) (h : ∃ m, n = m+m) : Even n :=
  by
  obtain ⟨m , eq⟩ := h
  rw [← two_mul] at eq
  rw [even_iff_exists_two_mul]
  use m

-- Conjunctions in goal
example (n : ℕ) : ∃ m : ℕ, (n ≤ m ∧ Even m) :=
  by
  use 2*n
  constructor
  · apply le_mul_of_pos_left
    decide
  · rw [even_iff_exists_two_mul]
    use n

-- Conjunctions among assumptions
example (a b c : ℕ) (H : a ≤ b ∧ b ≤ c) : a ≤ c :=
  by
  apply @le_trans _ _ a b c
  · exact H.left
  · exact H.right

-- Disjunctions in goal
example (n : ℕ) (h : ∃ m, n = 2*m) : n = 42 ∨ Even n :=
  by
  right
  rw [even_iff_exists_two_mul]
  exact h

-- Disjunctions among assumptions
example (n : ℕ) (h : n = 42 ∨ Even n) :  Even n :=
  by
  cases' h with h42 he
  · rw [h42]
    decide
  · exact he

-- Equivalences in goal
example (n : ℕ) : (∃ m, n = m+m) ↔ Even n :=
  by
  constructor
  · intro h
    cases' h with m eq
    rw [← two_mul] at eq
    rw [even_iff_exists_two_mul]
    use m
  · intro h
    rw [even_iff_exists_two_mul] at h
    obtain ⟨m , eq⟩ := h
    use m
    rw [← two_mul]
    exact eq

-- Shorter syntax
example (n : ℕ) : (∃ m, n = m+m) ↔  Even n :=
  by
  rw [even_iff_exists_two_mul]
  constructor <;> { intro h ; convert h using 2 ; rw [two_mul] }

-- Even shorter syntax
example (n : ℕ) : (∃ m, n = m+m) ↔  Even n :=
  by
  congr! 3

-- Turning equivalences to implications
#check (even_iff_exists_two_mul 2)
#check (even_iff_exists_two_mul 2).mp
#check (even_iff_exists_two_mul 2).mpr
