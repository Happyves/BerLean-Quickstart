/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic


-- # Basics (reminder) and some logic

-- **Note to self** : expect people to have played NNG, so familiar with the basics

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






-- # Functions

-- Two syntaxes for functions

def first_ver (n : ℕ) := n^2

def second_ver := fun n : ℕ => n^2

#check (first_ver)
#check (second_ver)


-- No partial functions. Instead, we use:

def pf_1 (n : ℕ) (hn : Odd n) : ℕ := n^2

def pf_2 : {n : ℕ | Odd n} → ℕ := fun n => n^2

#check (pf_1)
#check (pf_2)

-- What do we need partial functions for ?

#eval List.get [1,2,3] ⟨1 , (by decide)⟩

#eval pf_2 ⟨3, (by decide)⟩

#eval pf_1 3 (by decide)


-- "Piecewise" definition

def ite_fn (n : ℕ) := if Odd n then 1 else 0

#eval ite_fn 0
#eval ite_fn 1
#eval ite_fn 2
#eval ite_fn 3

def match_fn (n : ℕ) :=
  match n with
  | 42 => 42
  | _ => 0

#eval match_fn 0
#eval match_fn 37
#eval match_fn 42

def match_fn_2 (n : ℤ) :=
  match decide (n > 0) with
  | true => 42
  | false => 0

#eval match_fn_2 (-4)
#eval match_fn_2 37
#eval match_fn_2 42



def Fermat (n : ℕ) := ∃ x : ℕ, x > 0 ∧ ∃ y > 0, ∃ z > 0, x^n +y^n = z^n

open Classical in
noncomputable
def match_fn_3 (n : ℕ) :=
  match decide (Fermat n) with
  | true => 42
  | false => 0



-- # Functions in action

#print Function.Bijective
#print Function.Injective
#print Function.Surjective


lemma exercise_1 :
  let f := fun x : ℤ => x + 1
  Function.Bijective f :=
  by
  intro f
  constructor
  · intro a b eq
    dsimp [f] at eq
    exact add_right_cancel eq
  · intro b
    use (b-1)
    dsimp [f]
    rw [Int.sub_add_cancel]

#print Continuous

lemma exercise_2 :
  let f := fun x : ℤ => x + 1
  Continuous f :=
  by
  rw [Metric.continuous_iff]
  -- sorry here
  intro b ε epos
  use ε
  constructor
  · exact epos
  · intro a dab
    rw [dist_add_right]
    exact dab



-- # Sets
-- exercises taken from Kevin Buzzards "Formalising Math 2024"

#print Set

example : 74 ∈ {n : ℕ | Even n} :=
  by
  rw [Set.mem_setOf]
  decide

#print Set.union
#print Set.Subset

example (A B: Set ℕ) : A ⊆ A ∪ B := by
  intro x hx
  left
  exact hx

lemma exercise_3 (A B C: Set ℕ) : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
  by
  intro hBA hCA x h
  cases' h with hxB hxC
  · exact hBA hxB
  · exact hCA hxC

#print Set.image
#print Set.preimage


example (X Y : Type) (f : X → Y) (T : Set Y) :
  f '' (f ⁻¹' T) ⊆ T :=
  by
  intro y h
  obtain ⟨x, hx, rfl⟩ := h
  exact hx


lemma exercise_4 (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y):
  f '' S ⊆ T ↔ S ⊆ f ⁻¹' T :=
  by
  constructor
  · intro h x hxS
    apply h
    use x
  · intro h x hx
    obtain ⟨y , hyS, hy⟩ := hx
    rw [← hy]
    specialize h hyS
    apply h


-- # Finite sets

open Finset

#check ({1,2,3} : Finset ℕ)

#eval ({1,2,3} : Finset ℕ).card

#eval ({1,2,3} : Finset ℕ).powerset

#check Finset.card_powerset

#eval insert 4 ({1,2,3} : Finset ℕ)

#eval insert 2 ({1,2,3} : Finset ℕ)



-- # Mini-project: proving `Finset.card_powerset`

lemma exercise_5
  (s : Finset ℕ) :
  card (Finset.powerset s) = 2 ^ card s :=
  by
  revert s
  apply Finset.induction
  · -- sorry here
    rw [powerset_empty]
    rw [card_empty]
    rw [card_singleton]
    norm_num
  · intro a s ans ih
    rw [powerset_insert]

    have d : Disjoint (Finset.powerset s) (Finset.image (insert a) (Finset.powerset s)) :=
      by
      -- sorry here
      rw [disjoint_iff_ne]
      intro x hx y hy
      rw [mem_image] at hy
      obtain ⟨z, _, hzy⟩ := hy
      rw [mem_powerset] at *
      intro con
      apply ans
      apply hx
      rw [con]
      rw [← hzy]
      exact mem_insert_self a z

    rw [card_union_eq d]
    rw [card_insert_of_not_mem ans]
    rw [ih]
    rw [pow_add, pow_one, mul_two, Nat.add_left_cancel_iff]
    rw [← ih]
    rw [Finset.card_image_iff]
    intro x hx y hy eq
    rw [insert_eq, insert_eq] at eq
    rw [union_eq_union_iff_left] at eq

    have lem (z w: Finset ℕ) (hz1 : z ∈ powerset s) (hz2 : z ⊆ {a} ∪ w) :
      z ⊆ w :=
      by
      -- sorry here
      intro e ez
      specialize hz2 ez
      rw [mem_union] at hz2
      rw [mem_powerset] at hz1
      cases' hz2 with l r
      · exfalso
        rw [mem_singleton] at l
        rw [l] at ez
        specialize hz1 ez
        exact ans hz1
      · exact r

    apply Finset.Subset.antisymm
    · exact lem x y hx eq.1
    · exact lem y x hy eq.2





-- # Discrete math
-- This is for the second phase in the afternoon
-- TODO : add sorries for exercises


lemma succ_coprime
  (n m : Nat) (h : n = m+1) :
  Nat.Coprime n m :=
  by
  rw [h]
  rw [Nat.coprime_self_add_left]
  exact Nat.coprime_one_left m

open Finset

lemma claim_1
  (n : ℕ) (h : 1 ≤ n)
  (A : Finset ℕ) (Adef : A ∈ (powersetCard (n+1) (Icc 1 (2*n)))) :
  ∃ a ∈ A, ∃ b ∈ A, (a≠b) ∧ (Nat.Coprime a b) :=
  by
  rw [mem_powersetCard] at Adef
  /-
  This will follow from `succ_coprime` once we find
  a pair of successors in A.
  For this purpose, we group elements as {1,2}, {3,4}, etc.
  A function achieving this grouping is `(λ (x : ℕ), (x+1) / 2)`
  -/
  have Lem1 :
    ∃ a ∈ A, ∃ b ∈ A, (a≠b) ∧
    ((fun (x : ℕ) => (x+1) / 2) a = (fun (x : ℕ) => (x+1) / 2) b) :=
    by
    let group_fn := (fun x => (x+1) / 2)
        -- A condition to apply `exists_ne_map_eq_of_card_lt_of_maps_to`
    have map_condition : (∀ a, a ∈ A → group_fn a ∈ (Icc 1 n)) :=
      by
      intro x xdef
      dsimp [group_fn]
      replace xdef := Adef.1 xdef
      rw [mem_Icc] at *
      constructor
      · rw [Nat.le_div_iff_mul_le]
        linarith
        norm_num
      · rw [Nat.div_le_iff_le_mul_add_pred]
        linarith
        norm_num

    apply exists_ne_map_eq_of_card_lt_of_maps_to _ map_condition
          -- this is the pigeonhole principle
    -- We're left to show the condition on the sizes
    rw [Nat.card_Icc]
    simp only [add_tsub_cancel_right]
    rw [Adef.2]
    --apply nat.lt_succ, -- but `nat.le_succ` is a thing
    simp only [lt_add_iff_pos_right, eq_self_iff_true, Nat.lt_one_iff]
  rcases Lem1 with ⟨a, aA, b, bA, anb, abeq⟩
  dsimp at abeq
  use a ; constructor ; use aA ;
  use b ; constructor ; use bA ;
  constructor ; exact anb ;
  -- To determine which of a and b is the successor,
  -- we investigate the remainders
  have Lem2 :
    (a+1)%2 ≠ (b+1)%2 :=
    by
    intro con
    have : a+1 = b+1 :=
      by
      rw [← Nat.div_add_mod (a+1) 2]
      rw [← Nat.div_add_mod (b+1) 2]
      rw [abeq, con]
    apply anb
    exact Nat.add_right_cancel this
  -- We may order the remainders wlog
  wlog H : (a+1)%2 < (b+1)%2 with Sym
  · push_neg at H
    rw [ne_comm] at *
    rw [eq_comm] at abeq
    replace H := lt_of_le_of_ne H Lem2
    specialize Sym n h A Adef
    specialize Sym b bA a aA anb abeq Lem2 H
    rw [Nat.coprime_comm]
    exact Sym
  -- Next, we go over the possibilities for (b+1)%2
  · have := Nat.mod_lt (b+1) (show 0<2 from by {norm_num})
    interval_cases bcase : ((b+1)%2)
    · exfalso
      exact (Nat.not_lt_zero _) H
    · --rw [bcase] at H
      rw [Nat.lt_one_iff] at H
      rw [Nat.coprime_comm]
      apply succ_coprime b a -- we may now put out plan to action
      apply @Nat.add_right_cancel _ 1 _
      rw [← Nat.div_add_mod (a+1) 2]
      rw [← Nat.div_add_mod (b+1) 2]
      rw [abeq, bcase, H]

-- maybe add insertion sort ?
