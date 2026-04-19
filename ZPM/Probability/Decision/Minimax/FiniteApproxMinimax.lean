/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Decision.Minimax.Covering

/-!
# Approximate minimax via the covering argument

A feasibility-style approximate minimax statement: combining
`covering_minimax` with the hypothesis `v - ε ≤ 1 / |C|` yields a row
mixture with payoff at least `v - ε` against every pure column.
Complementary to the MWU-based quantitative bound.
-/

noncomputable section

namespace ProbabilityTheory

open FintypePMF

/-- **Approximate minimax (covering route).** If the minimax value is `v`, the slack `ε`
is positive, and `v - ε ≤ 1 / |C|`, then a row mixture exists whose payoff is at least
`v - ε` against every pure column. -/
theorem finite_approx_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C] [Nonempty R]
    [DecidableEq R] [DecidableEq C]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (hε_feasible : v - ε ≤ 1 / Fintype.card C) :
    ∃ p : FintypePMF R, ∀ c : C,
      v - ε ≤ boolGamePayoff M p c := by
  by_cases hv : v ≤ 0
  · exact ⟨FintypePMF.uniform R, fun c => le_trans (by linarith) (boolGamePayoff_nonneg M _ c)⟩
  · push Not at hv
    obtain ⟨p, hp⟩ := covering_minimax M v hv hrow
    exact ⟨p, fun c => le_trans hε_feasible (hp c)⟩

end ProbabilityTheory

end
