
/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Tactic

open CategoryTheory

/-
Introduces notations in the `CategoryTheory` scope
* `X ⟶ Y` for the morphism spaces (type as `\hom`),
* `𝟙 X` for the identity morphism on `X` (type as `\b1`),
* `f ≫ g` for composition in the 'arrows' convention (type as `\gg`).
-/

-- Mathlib.CategoryTheory.Category.Basic has discussion on universes for category types


/- A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `Quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `Quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `Category` will later extend this class, we call the field `Hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
#check Quiver
-- class Quiver (V : Type u) where
--   /-- The type of edges/arrows/morphisms between a given source and target. -/
--   Hom : V → V → Sort v

/- A preliminary structure on the way to defining a category,
containing the data, but none of the axioms. -/
#check CategoryStruct
-- class CategoryStruct (obj : Type u) extends Quiver.{v + 1} obj : Type max u (v + 1) where
--   /-- The identity morphism on an object. -/
--   id : ∀ X : obj, Hom X X
--   /-- Composition of morphisms in a category, written `f ≫ g`. -/
--   comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z)

/- The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `Category.{v} C`. (See also `LargeCategory` and `SmallCategory`.)

See <https://stacks.math.columbia.edu/tag/0014>.
-/
#check Category
-- class Category (obj : Type u) extends CategoryStruct.{v} obj : Type max u (v + 1) where
--   /-- Identity morphisms are left identities for composition. -/
--   id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by aesop_cat
--   /-- Identity morphisms are right identities for composition. -/
--   comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by aesop_cat
--   /-- Composition in a category is associative. -/
--   assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h :=
--     by aesop_cat

-- example of the category of finite sets

--instance : Category (Finset ℕ) := by infer_instance -- works

instance optional_name : Category (Finset ℕ) :=
{Hom := (fun S T => (S → T))
 id := (fun S => (fun x => x))
 comp := (fun f g => (fun x => g (f x)))}

set_option pp.explicit true in
#print optional_name

#print optional_name.proof_2

#check Category.assoc

#check 𝟙 ({1,2,3} : Finset ℕ)

#check ({1,2,3} : Finset ℕ)


def frist_morph : ({1,2,3} : Finset ℕ) ⟶ ({3,4,5} : Finset ℕ):=
  fun x => ⟨(x.val + 2), by fin_cases x <;> norm_num ⟩

def second_morph : ({3,4,5} : Finset ℕ) ⟶ ({2,3,4} : Finset ℕ):=
  fun x => ⟨(x.val - 1), by fin_cases x <;> norm_num ⟩

#check frist_morph ≫ second_morph

#eval (frist_morph ≫ second_morph) ⟨1, by norm_num⟩
