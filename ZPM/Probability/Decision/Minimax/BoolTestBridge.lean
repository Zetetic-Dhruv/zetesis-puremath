/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Decision.Minimax.BoolGame
import ZPM.Probability.FintypePMF.Expectation

/-!
# Bridge between game payoff and test expectation

`boolGamePayoff M p c` (a row-distribution payoff against a fixed column) is
the same quantity as `boolTestExpectation p (fun r => M r c)`. The
identification lets MWU regret bounds and TV-based transfer results live
in a single distributional framework.
-/

noncomputable section

namespace ProbabilityTheory

open FintypePMF

/-- Game payoff of a row distribution equals the row-test expectation of the column
indicator `fun r => M r c`. -/
lemma boolGamePayoff_eq_boolTestExpectation
    {R : Type*} [Fintype R] [DecidableEq R]
    {C : Type*} (M : R → C → Bool) (p : FintypePMF R) (c : C) :
    boolGamePayoff M p c = boolTestExpectation p (fun r => M r c) := by
  simp only [boolGamePayoff, boolTestExpectation, trueExpectation]

end ProbabilityTheory

end
