/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Def

/-!
# FintypePMF.normalize: normalize a positive weight vector

Canonical `FintypePMF` constructor from a strictly-positive weight function.
The divisor is a `Finset.sum`, which makes the constructor a computable
definition (`noncomputable` only because of the strict-positivity proof
threading, not because of any upstream noncomputability).
-/

noncomputable section

namespace ProbabilityTheory.FintypePMF

open Finset

/-- Normalize a strictly-positive weight vector to a `FintypePMF`. -/
def normalize {α : Type*} [Fintype α] [Nonempty α]
    (w : α → ℝ) (hw : ∀ a, 0 < w a) : FintypePMF α where
  prob a := w a / ∑ a' : α, w a'
  prob_nonneg a :=
    div_nonneg (le_of_lt (hw a))
      (Finset.sum_nonneg fun a' _ => le_of_lt (hw a'))
  prob_sum_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (Finset.sum_pos (fun a _ => hw a) univ_nonempty))

/-- `(normalize w hw).prob a = w a / ∑ a', w a'`. -/
lemma normalize_prob {α : Type*} [Fintype α] [Nonempty α]
    (w : α → ℝ) (hw : ∀ a, 0 < w a) (a : α) :
    (normalize w hw).prob a = w a / ∑ a' : α, w a' := rfl

end ProbabilityTheory.FintypePMF

end
