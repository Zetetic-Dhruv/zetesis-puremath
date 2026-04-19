/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Basic

/-!
# Expected payoff of a `FintypePMF` in a Bool-valued game

Infrastructure for minimax analysis over finite Boolean games:
`boolGamePayoff` is the inner-product pairing between a row distribution
and an indicator column. Supporting lemmas prove it is `[0, 1]`-bounded,
evaluates correctly on point masses, and implies the minimax value is
at most `1`.
-/

noncomputable section

namespace ProbabilityTheory

open Finset FintypePMF

/-- Expected payoff of distribution `p` against column `c` in a `Bool`-valued game
defined by `M : R → C → Bool`. -/
def boolGamePayoff {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FintypePMF R) (c : C) : ℝ :=
  ∑ r : R, p.prob r * (if M r c then (1 : ℝ) else 0)

lemma boolGamePayoff_nonneg {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FintypePMF R) (c : C) :
    0 ≤ boolGamePayoff M p c :=
  Finset.sum_nonneg fun r _ =>
    mul_nonneg (p.prob_nonneg r) (by split_ifs <;> norm_num)

lemma boolGamePayoff_le_one {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FintypePMF R) (c : C) :
    boolGamePayoff M p c ≤ 1 := by
  calc boolGamePayoff M p c
      ≤ ∑ r : R, p.prob r := Finset.sum_le_sum fun r _ => by
        calc p.prob r * (if M r c then (1 : ℝ) else 0)
            ≤ p.prob r * 1 := mul_le_mul_of_nonneg_left
              (by split_ifs <;> norm_num) (p.prob_nonneg r)
          _ = p.prob r := mul_one _
    _ = 1 := p.prob_sum_one

/-- Payoff on a point mass is the pointwise game value. -/
lemma boolGamePayoff_pointMass {R C : Type*} [Fintype R] [DecidableEq R]
    (M : R → C → Bool) (r₀ : R) (c : C) :
    boolGamePayoff M (FintypePMF.pointMass r₀) c = if M r₀ c then 1 else 0 := by
  simp only [boolGamePayoff, FintypePMF.pointMass]
  conv_lhs =>
    arg 2; ext r
    rw [show (if r = r₀ then (1 : ℝ) else 0) * (if M r c then (1 : ℝ) else 0) =
      if r = r₀ then (if M r c then 1 else 0) else 0 from by
        split_ifs <;> simp]
  simp

/-- If a row player can achieve expected payoff at least `v` against every column
mixture, then `v ≤ 1`. -/
lemma minimax_value_le_one {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    v ≤ 1 := by
  obtain ⟨r, hr⟩ := hrow (FintypePMF.uniform C)
  calc v ≤ ∑ c : C, (FintypePMF.uniform C).prob c *
      (if M r c then (1 : ℝ) else 0) := hr
    _ ≤ ∑ c : C, (FintypePMF.uniform C).prob c := Finset.sum_le_sum fun c _ =>
        mul_le_of_le_one_right ((FintypePMF.uniform C).prob_nonneg c)
          (by split_ifs <;> norm_num)
    _ = 1 := (FintypePMF.uniform C).prob_sum_one

end ProbabilityTheory

end
