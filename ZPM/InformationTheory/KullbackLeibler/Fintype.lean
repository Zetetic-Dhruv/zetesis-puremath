/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Def
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kullback-Leibler divergence on `FintypePMF`

`FintypePMF.klDiv Q P = ∑ h, Q.prob h · log (Q.prob h / P.prob h)` with
the convention `0 · log(0 / anything) = 0`. An ℝ-valued, `Finset.sum`-
based specialization of `Mathlib.InformationTheory.klDiv` to the
`Fintype`-indexed setting, admitted under the proof-engineering
specialization clause of `CHARTER.md` for the same reason as
`FintypePMF` itself.
-/

noncomputable section

namespace ProbabilityTheory.FintypePMF

open Finset

/-- Kullback-Leibler divergence between two `FintypePMF`s (ℝ-valued, discrete).

`klDiv Q P = ∑ h, Q.prob h · log (Q.prob h / P.prob h)`, with the
convention `0 · log(0 / anything) = 0`. -/
def klDiv {α : Type*} [Fintype α] (Q P : FintypePMF α) : ℝ :=
  ∑ h : α, if Q.prob h = 0 then 0
    else Q.prob h * Real.log (Q.prob h / P.prob h)

end ProbabilityTheory.FintypePMF

end
