/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic


/-- The integers-/
inductive int where
| ofNat   : ℕ → int
| negSucc : ℕ → int

/-- -3 -/
def minus_three : int := int.negSucc 2

/-- Subtraction of naturals with integer output-/
def subNatNat (m n : ℕ) : int :=
match (n - m : Nat) with
| 0        => int.ofNat (m - n)
| (Nat.succ k) => int.negSucc k

/-- Addition of integers-/
def int.add (m n : int) : int :=
match m, n with
| ofNat m,   ofNat n   => ofNat (m + n)
| ofNat m,   negSucc n => subNatNat m (Nat.succ n)
| negSucc m, ofNat n   => subNatNat n (Nat.succ m)
| negSucc m, negSucc n => negSucc (Nat.succ (m + n))

-- Sanity check
#reduce int.add (int.ofNat 2) (minus_three)

-- Ctrl + click on these
#check Int.neg
#check Int.sub

-- Typecasting
#check 2
#check (2 : ℤ)
#check -2


-- Coercion
#check Int.add
#eval Int.add 2 (-3)
