
/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic


def Multi_append (m M : Multiset ℕ) : Multiset ℕ :=
  Quot.lift₂
  (fun l L => ⟦List.append l L⟧)
  (by
   intro a b c brc
   rw [Quotient.eq]
   apply List.Perm.append
   · exact List.perm_rfl
   · exact brc
   )
  (by
   intro a b c arb
   rw [Quotient.eq]
   apply List.Perm.append
   · exact arb
   · exact List.perm_rfl
   )
  (m) (M)

#eval Multi_append (⟦[1,2,3,3]⟧ : Multiset ℕ) (⟦[1,2,3,3]⟧ : Multiset ℕ)
