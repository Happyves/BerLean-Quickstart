/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic

-- Evaluable sums and products
open BigOperators in
#eval ∑ x in {1,2,3}, x

-- With functions
open BigOperators in
#eval ∑ x in {1,2,3}, x^2

-- Products
open BigOperators in
#eval ∏ x in {1,2,3}, x

-- Preferable when working with a lot of them
open BigOperators

-- Gauss' sums
example (n : ℕ): ∑  m in Finset.range (n+1), m = (n*(n+1))/2 :=
  by
  induction' n with n ih
  · rw [Nat.zero_mul, Nat.zero_div]
    rw [Finset.range_one]
    decide
  · rw [Nat.succ_eq_add_one]
    rw [add_assoc]
    norm_num
    rw [mul_add]
    rw [Nat.add_div_of_dvd_left (Nat.dvd_mul_left 2 (n + 1))]
    rw [Nat.mul_div_left _ (by norm_num)]
    rw [Finset.range_succ]
    rw [Finset.sum_insert]
    · rw [ih]
      rw [add_comm, mul_comm]
    · intro contra
      rw [Finset.mem_range] at contra
      exact lt_irrefl (n+1) contra

-- Anatomy
#check Finset.sum
#check Finset.prod


-- Exercise
example (n : ℕ) : Even (∑ n in ((Finset.range n).filter Even), n) :=
  by
  sorry

#check Finset.filter_insert
#check Finset.range_succ
#check Finset.sum_empty
#check Finset.sum_insert
#check Finset.range_zero
#check Finset.filter_empty
#check Finset.not_mem_range_self
#check Finset.mem_filter
#check Even.add

/-- Function that maps a natrual number different of 1
to one of its prime divisors -/
noncomputable
def my_func (n : ℕ) (hn : n ≠ 1) :=
  Classical.choose (Nat.exists_prime_and_dvd hn)

#check ∑ x in Finset.Icc 2 5, my_func x (_)

-- Fails!
--example : 1 ≤ ∑ x in Finset.Icc 2 5, my_func x (_) := by sorry


#check Subtype
-- are defined as:
structure subtype (α : Type) (p : α → Prop) where
  val : α
  prop : p val

-- Notation
#check {n : ℕ // n.Prime}

-- Attach operation
#check Finset.attach

-- Now it works
example : 1 ≤ ∑ x in Finset.attach (Finset.Icc 2 5),
              my_func x (by
                         have h := x.prop
                         rw [Finset.mem_Icc] at h
                         linarith
                         ) :=
  by
  sorry

-- API for attach operation
#check Finset.sum_attach

-- Alternative
#check List.pmap

-- Anantomy
def Pmap {p : α → Prop} (f : ∀ a, p a → β) : ∀ l : List α, (∀ a ∈ l, p a) → List β
| [], _ => []
| a :: l, H => f a (H a (List.mem_cons_self a l) ) :: Pmap f l (fun x xl => H x (List.mem_cons_of_mem a xl))

def my_func' (n : ℕ) (hn : n ≠ 1) := n+3

def pprod {p : α → Prop} [CommMonoid β] (s : Finset α) (f : (a : α) → p a → β) (h : ∀ a ∈ s, p a) : β :=
  (s.1.pmap f h).prod

#eval pprod {2,3} my_func' (by intro x xl ; fin_cases xl <;> decide)
