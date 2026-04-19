/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Decision.Minimax.BoolGame

/-!
# Covering-row lemma

If the minimax value is strictly positive, every column has a row that
`Bool`-covers it. Used as the starting point for the covering-based
minimax bound.
-/

noncomputable section

namespace ProbabilityTheory

open Finset FintypePMF

/-- If the minimax value is positive, every column admits a pure row with payoff one. -/
lemma exists_covering_row {R C : Type*} [Fintype R] [Fintype C] [DecidableEq C]
    [Nonempty C]
    (M : R → C → Bool) (v : ℝ) (hv : 0 < v)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ c₀ : C, ∃ r : R, M r c₀ = true := by
  intro c₀
  obtain ⟨r, hr⟩ := hrow (FintypePMF.pointMass c₀)
  refine ⟨r, ?_⟩
  by_contra h
  have hf : M r c₀ = false := Bool.eq_false_iff.mpr h
  have : (∑ c : C, (FintypePMF.pointMass c₀).prob c *
      (if M r c then (1 : ℝ) else 0)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro c _
    simp only [FintypePMF.pointMass]
    split_ifs with h1 h2
    · subst h1; rw [hf] at h2; exact absurd h2 Bool.false_ne_true
    · simp
    · simp
    · simp
  linarith

end ProbabilityTheory

end
