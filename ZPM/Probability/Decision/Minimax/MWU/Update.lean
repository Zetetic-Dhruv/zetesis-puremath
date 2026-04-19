/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Decision.Minimax.BoolGame
import ZPM.Probability.Decision.Minimax.MWU.Config

/-!
# MWU update step and one-step potential bound

Given a column `c` that the row player hits (`M r c = true`), the MWU
update multiplies `weights c` by `1 - η` and leaves all other weights
unchanged. The one-step potential bound `Φ' ≤ Φ · (1 - η · v)` follows
from the row player's best-response property composed with the hypothesis
that every PMF-valued column mixture admits a pure response with payoff
at least `v`.
-/

noncomputable section

namespace ProbabilityTheory

open Finset FintypePMF

/-- One step of the multiplicative-weights update: columns `c` with `M r c = true` have
their weights scaled by `1 - η`; all other weights are unchanged. -/
def mwuUpdateWeights {C : Type*} [Fintype C] {R : Type*}
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1)
    (cfg : MWUConfig C) (r : R) : MWUConfig C where
  weights c := cfg.weights c * (if M r c then (1 - η) else 1)
  weights_pos c := mul_pos (cfg.weights_pos c) (by split_ifs <;> linarith)

/-- Best-response payoff in terms of weights: a pure response against the normalized PMF
gives expected payoff at least `v · Φ` when weighed by the un-normalized weight vector. -/
lemma best_response_payoff_weights
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (cfg : MWUConfig C) :
    v * cfg.potential ≤
    ∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) := by
  have hr := (hrow cfg.toPMF).choose_spec
  have hΦ_pos := cfg.potential_pos
  have key : (∑ c : C, cfg.toPMF.prob c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0)) =
    (∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0)) / cfg.potential := by
    simp only [MWUConfig.toPMF, FintypePMF.normalize, MWUConfig.potential]
    rw [Finset.sum_div]; congr 1; ext c; field_simp
  rw [key] at hr
  rwa [le_div_iff₀ hΦ_pos] at hr

/-- **One-step MWU potential bound**: after one update, the potential is multiplied by
`(1 - η · v)` or less. -/
lemma potential_one_step_bound
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη : 0 ≤ η) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (cfg : MWUConfig C) :
    (mwuUpdateWeights M η hη1 cfg (hrow cfg.toPMF).choose).potential ≤
    cfg.potential * (1 - η * v) := by
  simp only [MWUConfig.potential, mwuUpdateWeights]
  have hsum_eq : (∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then 1 - η else 1)) =
    (∑ c : C, cfg.weights c) -
    η * ∑ c : C, cfg.weights c *
      (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) := by
    have : ∀ c : C, cfg.weights c *
        (if M (hrow cfg.toPMF).choose c then 1 - η else 1) =
      cfg.weights c - η * (cfg.weights c *
        (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0)) := by
      intro c; split_ifs <;> ring
    simp_rw [this, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum_eq]
  have hbr := best_response_payoff_weights M v hrow cfg
  set S := ∑ c : C, cfg.weights c *
    (if M (hrow cfg.toPMF).choose c then (1 : ℝ) else 0) with hS_def
  have h1 : η * (v * cfg.potential) ≤ η * S := mul_le_mul_of_nonneg_left hbr hη
  unfold MWUConfig.potential at h1 hbr
  linarith

end ProbabilityTheory

end
