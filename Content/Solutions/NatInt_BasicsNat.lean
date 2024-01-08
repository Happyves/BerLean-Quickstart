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

/-- 0 + n = n -/
lemma my_lemma_2 : ∀ (n : nat), nat.add nat.zero n = n :=
  by
  intro n
  induction' n with n ih
  · dsimp [nat.add]
  · dsimp [nat.add]
    rw [ih]


/-- n ≤ m -/
inductive nat.le (n : nat) : nat → Prop
| refl     : nat.le n n
| step {m} : nat.le n m → nat.le n (nat.succ m)

-- n ≤ n + m
example : ∀ (n m : nat), nat.le n (nat.add n m) :=
  by
  intro n m
  induction' m with m ih
  · dsimp [nat.add]
    apply nat.le.refl
  · dsimp [nat.add]
    apply nat.le.step
    exact ih
