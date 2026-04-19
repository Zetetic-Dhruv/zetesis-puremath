/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Decision.Minimax.MWU.Run
import Mathlib.Algebra.BigOperators.Fin

/-!
# Individual-weight tracking for MWU

Tracks each column's weight through the T-round run. The hit counter
`mwuHitCount T c` records the number of rounds `t < T` in which column
`c` was hit by the selected row. The weight of `c` after `T` rounds is
exactly `(1 - η)^(hitCount T c)`.

Declarations here are internal infrastructure for the MWU analysis
(shared across the `ApproxMinimax` headline proof) and not intended as
standalone API.
-/

noncomputable section

namespace ProbabilityTheory

open Finset FintypePMF

/-- Number of rounds (in the first `T`) in which column `c` was hit by the selected row. -/
def mwuHitCount
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    (T : ℕ) → C → ℕ
  | 0, _ => 0
  | T + 1, c =>
      let cfg := mwuConfig M η hη1 v hrow T
      let r := (hrow cfg.toPMF).choose
      mwuHitCount M η hη1 v hrow T c + if M r c then 1 else 0

/-- A single weight is bounded above by the configuration's total potential. -/
lemma weight_le_potential
    {C : Type*} [Fintype C] (cfg : MWUConfig C) (c : C) :
    cfg.weights c ≤ cfg.potential := by
  unfold MWUConfig.potential
  exact Finset.single_le_sum
    (fun c _ => le_of_lt (cfg.weights_pos c))
    (by simp)

/-- Individual-weight closed form: after `T` rounds, `weights c = (1 - η)^(hitCount T c)`. -/
lemma mwu_weight_eq_pow_hitCount
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ (T : ℕ) (c : C),
      (mwuConfig M η hη1 v hrow T).weights c =
        (1 - η) ^ (mwuHitCount M η hη1 v hrow T c)
  | 0, c => by
      simp [mwuConfig, mwuRun, mwuHitCount, mwuInit]
  | T + 1, c => by
      simp [mwuConfig, mwuRun, mwuHitCount, mwuUpdateWeights,
        mwu_weight_eq_pow_hitCount M η hη1 v hrow T c,
        mul_comm]
      split_ifs <;> ring

/-- The hit counter agrees with the sum of Boolean indicators over the row sequence. -/
lemma mwuHitCount_eq_sum_indicator
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∀ (T : ℕ) (c : C),
      (mwuHitCount M η hη1 v hrow T c : ℝ) =
        ∑ t : Fin T, if M (mwuRows M η hη1 v hrow T t) c then (1 : ℝ) else 0
  | 0, c => by
      simp [mwuHitCount, mwuRows, mwuRun]
  | T + 1, c => by
      simp only [mwuHitCount, mwuRows, mwuRun]
      push_cast
      rw [mwuHitCount_eq_sum_indicator M η hη1 v hrow T c]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      try ring

end ProbabilityTheory

end
