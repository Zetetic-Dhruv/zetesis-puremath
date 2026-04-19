/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Def

/-!
# FintypePMF.empirical: empirical distribution of a finite sequence

Given a length-`T` sequence `rs : Fin T → α`, the empirical PMF puts
weight `(count of a in rs) / T` on each `a`. Used to turn an MWU row
sequence into a row mixture.
-/

noncomputable section

namespace ProbabilityTheory.FintypePMF

open Finset

/-- Empirical `FintypePMF` from a length-`T` sequence. -/
def empirical {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℕ} (hT : 0 < T) (rs : Fin T → α) : FintypePMF α where
  prob a := (univ.filter (fun t => rs t = a)).card / (T : ℝ)
  prob_nonneg a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  prob_sum_one := by
    rw [← Finset.sum_div]
    suffices h : (∑ a : α, ((univ.filter (fun t : Fin T => rs t = a)).card : ℝ)) = T by
      rw [h]; exact div_self (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT))
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := rs) (s := univ) (t := univ)
      (fun t _ => mem_univ (rs t))
    simp only [card_univ, Fintype.card_fin] at hfib
    exact_mod_cast hfib.symm

end ProbabilityTheory.FintypePMF

end
