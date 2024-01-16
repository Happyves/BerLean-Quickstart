/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic

/-- Property of two lists having common permmuted entries-/
inductive perm : List α → List α → Prop
  | nil : perm [] []
  | cons (x : α) {l₁ l₂ : List α} : perm l₁ l₂ → perm (x :: l₁) (x :: l₂)
  | swap (x y : α) (l : List α) : perm (y :: x :: l) (x :: y :: l)
  | trans {l₁ l₂ l₃ : List α} : perm l₁ l₂ → perm l₂ l₃ → perm l₁ l₃

-- Mathlib version
#check List.Perm

-- Proving the property
open List in
example : [1,2,3] ~ [1,3,2] :=
  by
  apply Perm.cons
  apply Perm.swap

-- Automation!
open List in
example : [1,2,3] ~ [1,3,2] :=
  by
  decide

-- A nice enumertion algorithm
#eval List.permutations [1,2,3]

-- Equivalence relations
#check Equivalence

/-- Having same remainder mod 3-/
def my_rel : ℤ → ℤ → Prop := fun a b => a % 3 = b % 3

/-- Unidiomatic alternative-/
example {α : Type u} {r : α → α → Prop} : Prop :=
  (∀ (x : α), r x x) ∧ (∀ {x y : α}, r x y → r y x) ∧
  (∀ {x y z : α}, r x y → r y z → r x z)

/-- the relation is trnasitive -/
lemma as_lemma : ∀ {x y z : ℤ}, my_rel x y → my_rel y z → my_rel x z :=
  by
  intro x y z hxy hyz
  rw [my_rel] at *
  exact Eq.trans hxy hyz

/-- Having same remainder mod 3 is an equivalence relation -/
def my_equiv : Equivalence my_rel where
  refl :=
    by
    intro x
    dsimp [my_rel]
  symm :=
    by
    intro x y h
    rw [my_rel] at *
    exact Eq.symm h
  trans :=
    as_lemma

-- It's a type
#check my_equiv

-- Access attributes of structures with infix notation
#check my_equiv.trans

-- Permutations of lists form an equivalence relation
#check List.Perm.eqv

-- A type with an equivalence relation
#check Setoid

instance my_inst : Setoid ℤ where
  r := my_rel
  iseqv := my_equiv

-- A new way of making types, based on setoids
#check Quotient

-- How to form elements of that type
#check (⟦2⟧ : Quotient my_inst)

-- Equality in quotients
example : (⟦2⟧ : Quotient my_inst) = ⟦5⟧ :=
  by
  apply Quotient.sound
  dsimp [HasEquiv.Equiv, instHasEquiv, Setoid.r, my_inst, my_rel]
  decide

-- Definitional equality at work
example : (⟦2⟧ : Quotient my_inst) = ⟦5⟧ :=
  by
  apply Quotient.sound
  rfl

-- Equality in quotients
#check Quotient.eq
#check Quotient.sound

-- Multisets as a quotient on Lists
#check Multiset

example : (⟦[1,2,3,3]⟧ : Multiset ℕ) = ⟦[1,3,2,3]⟧ :=
  by
  rw [Quotient.eq]
  apply List.Perm.cons
  apply List.Perm.swap

example : (⟦[1,2,3,3]⟧ : Multiset ℕ) = ⟦[1,3,2,3]⟧ :=
  by
  decide


-- Lifting operations to quotients
#check Quot.lift

-- Membership
#check Multiset.Mem

-- Lifting list membership
example (x : ℕ) (m : Multiset ℕ) : Prop :=
  Quot.lift
  (List.Mem x)
  (by
   intro a b arb
   dsimp [Setoid.r] at arb
   apply propext
   exact List.Perm.mem_iff arb
   )
  (m)

-- Decidable
example : Multiset.Mem 2 (⟦[1,2,3,3]⟧ : Multiset ℕ) :=
  by
  rw [Multiset.Mem]
  decide

-- List union
#check List.union
#eval List.union [1,2,2,3] [4,3,3]

-- List insertion
#check List.insert
#eval List.insert 3 [2,1]
#eval List.insert 1 [2,1]

-- Lifting unions
example (m M : Multiset ℕ) : Multiset ℕ :=
  Quot.lift₂
  (fun l L => ⟦List.union l L⟧)
  (by
   intro a b c brc
   rw [Quotient.eq]
   apply List.Perm.union
   · exact List.perm_rfl
   · exact brc
   )
  (by
   intro a b c arb
   rw [Quotient.eq]
   apply List.Perm.union
   · exact arb
   · exact List.perm_rfl
   )
  (m) (M)

-- Mathlib's version
#check Multiset.ndunion

-- It's evaluable
#eval Multiset.ndunion (⟦[1,2,3,3]⟧ : Multiset ℕ) (⟦[4,4,3]⟧ : Multiset ℕ)

def Multi_append (m M : Multiset ℕ) : Multiset ℕ :=
  Quot.lift₂
  (fun l L => ⟦List.append l L⟧)
  (by
   intro a b c brc
   rw [Quotient.eq]
   sorry
   )
  (by
   intro a b c arb
   rw [Quotient.eq]
   sorry
   )
  (m) (M)
