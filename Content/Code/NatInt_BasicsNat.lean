/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic

/-- The type of naural numbers-/
inductive nat where
| zero : nat
| succ (n : nat) : nat

/-- Represents 2 -/
def two : nat := nat.succ (nat.succ nat.zero)

/-- Addition of natural numbers-/
def nat.add : nat → nat → nat
| a, nat.zero   => a
| a, nat.succ b => nat.succ (nat.add a b)

-- 2+2=4, quick maths
#reduce nat.add two two

/-- The factorial n! of n-/
def factorial : ℕ → ℕ
| Nat.zero => 1
| Nat.succ n => (Nat.succ n) * (factorial n)

-- sanity check
#reduce factorial 3

/-- (n+1) + m = (n + m)+1-/
lemma my_lemma_1 : ∀ (n m : nat), nat.add (nat.succ n) m = nat.succ (nat.add n m) :=
  by
  intro n m
  induction' m with m ih
  · dsimp [nat.add]
  · dsimp [nat.add]
    rw [ih]

/-- 0 + n = n -/
lemma my_lemma_2 : ∀ (n : nat), nat.add nat.zero n = n :=
  by
  sorry

-- Commutativity of addition
example : ∀ (n m : nat), nat.add n m = nat.add m n :=
  by
  intro n m
  induction' m with m ih
  · dsimp [nat.add]
    rw [my_lemma_2 n]
  · dsimp [nat.add]
    rw [my_lemma_1]
    rw [ih]

/-- n ≤ m -/
inductive nat.le (n : nat) : nat → Prop
| refl     : nat.le n n
| step {m} : nat.le n m → nat.le n (nat.succ m)

-- 0 ≤ 2
example : nat.le nat.zero two :=
  by
  rw [two]
  apply nat.le.step
  apply nat.le.step
  apply nat.le.refl

-- With composite lemmata
example : nat.le nat.zero two :=
  by
  apply nat.le.step (nat.le.step (nat.le.refl))

-- ∀ n m, n ≤ n + m
example : ∀ (n m : nat), nat.le n (nat.add n m) :=
  by
  sorry

/-- Predecessor of a natural number-/
def nat.pred : nat → nat
| nat.zero   => nat.zero
| nat.succ a => a

/-- Subtraction of natural numbers-/
def nat.sub : nat → nat → nat
  | a, nat.zero      => a
  | a, nat.succ b => nat.pred (nat.sub a b)

-- Computations
#reduce nat.sub (nat.succ two) two -- 3 - 2 = 1
#reduce nat.sub two (nat.succ two) -- 2 - 3 = 0

-- IRL (in real Lean)
#reduce 3 - 2
#reduce 2 - 3

-- (Perhaps) unexpected behaviors ...
example : ∃ a b c : ℕ, (a + b) - c ≠ a + (b - c) :=
  by
  use 1
  use 2
  use 3
  decide

-- ... yield (perhaps) unexpected additional hypotheses
#check Nat.add_sub_assoc
