/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Def
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Bridge: `FintypePMF` ↔ `Mathlib.PMF` (on Fintype)

Converts between the ℝ-valued `FintypePMF` type used by the MWU analysis
and Mathlib's ℝ≥0∞-valued `PMF` type used by the measure-theoretic
framework. The bridge is the contract that justifies the coexistence of
the two types under the repository's duplicate-rule exception.

`ENNReal.ofReal` clamps negatives to `0`, but `FintypePMF.prob_nonneg`
rules out negatives anyway, so the clamp is invisible on valid inputs.
-/

noncomputable section

namespace ProbabilityTheory.FintypePMF

open Finset

/-- Convert a `FintypePMF` to a `Mathlib.PMF` via `ENNReal.ofReal`. -/
def toPMF {α : Type*} [Fintype α] (p : FintypePMF α) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (p.prob a)) <| by
    have h1 : (∑ a : α, ENNReal.ofReal (p.prob a)) =
        ENNReal.ofReal (∑ a : α, p.prob a) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => p.prob_nonneg a)]
    rw [h1, p.prob_sum_one, ENNReal.ofReal_one]

/-- The PMF image of a `FintypePMF` evaluates to the `ENNReal.ofReal`
coercion of the original weight. -/
lemma toPMF_apply {α : Type*} [Fintype α] (p : FintypePMF α) (a : α) :
    p.toPMF a = ENNReal.ofReal (p.prob a) := by
  simp [toPMF]

end ProbabilityTheory.FintypePMF

end
