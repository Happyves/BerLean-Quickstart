/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic

open Finset in
example (a b : Finset ℕ ): a ∩ b = a.filter (fun x => x ∈ b) :=
  by
  ext x
  constructor
  · intro xi
    rw [mem_filter]
    rw [mem_inter] at xi
    exact xi
  · intro xf
    rw [mem_filter] at xf
    rw [mem_inter]
    exact xf
