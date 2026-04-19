/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Def
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Cross-entropy on `FintypePMF`

`FintypePMF.crossEntropy Q P = ∑ h, Q.prob h · log (1 / P.prob h)`, the
Fintype-indexed ℝ-valued cross-entropy. Related to KL by
`H(Q, P) = H(Q) + KL(Q ‖ P)` where `H(Q)` is Shannon entropy.
-/

noncomputable section

namespace ProbabilityTheory.FintypePMF

open Finset

/-- Cross-entropy between two `FintypePMF`s: `H(Q, P) = ∑ h, Q.prob h · log(1/P.prob h)`. -/
def crossEntropy {α : Type*} [Fintype α] (Q P : FintypePMF α) : ℝ :=
  ∑ h : α, if Q.prob h = 0 then 0
    else Q.prob h * Real.log (1 / P.prob h)

end ProbabilityTheory.FintypePMF

end
