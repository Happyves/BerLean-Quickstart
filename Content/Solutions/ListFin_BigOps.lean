/-
Copyright (c) 2024 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/

import Mathlib.Tactic

open BigOperators in
example (n : ℕ) : Even (∑ n in ((Finset.range n).filter Even), n) :=
  by
  induction' n with n ih
  · rw [Finset.range_zero]
    rw [Finset.filter_empty]
    rw [Finset.sum_empty]
    decide
  · rw [Finset.range_succ]
    rw [Finset.filter_insert]
    split_ifs with q
    · rw [Finset.sum_insert]
      · exact Even.add q ih
      · intro con
        rw [Finset.mem_filter] at con
        exact Finset.not_mem_range_self con.left
    · exact ih
