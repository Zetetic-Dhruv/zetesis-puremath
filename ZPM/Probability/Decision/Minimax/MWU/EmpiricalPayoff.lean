/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Decision.Minimax.BoolGame
import ZPM.Probability.Decision.Minimax.MWU.WeightTracking

/-!
# Empirical payoff of the MWU row sequence

Bridges the empirical `FintypePMF` of the MWU row sequence to the column-level
hit counter: the payoff `boolGamePayoff M (empirical hT rows) c` equals
`hitCount T c / T`. Used to convert the analytic T-step potential bound
into a per-column payoff statement for the final approximate-minimax
theorem.
-/

noncomputable section

namespace ProbabilityTheory

open Finset FintypePMF

/-- The empirical `FintypePMF` payoff equals the average indicator along the sequence. -/
lemma boolGamePayoff_empirical_eq_avg
    {R C : Type*} [Fintype R] [DecidableEq R]
    {T : ℕ} (hT : 0 < T) (rs : Fin T → R) (M : R → C → Bool) (c : C) :
    boolGamePayoff M (FintypePMF.empirical hT rs) c =
      (∑ t : Fin T, if M (rs t) c then (1 : ℝ) else 0) / T := by
  simp only [boolGamePayoff, FintypePMF.empirical]
  conv_lhs => arg 2; ext r; rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  symm
  conv_lhs =>
    rw [show (∑ t : Fin T, if M (rs t) c then (1 : ℝ) else 0) =
      ∑ r : R, ∑ t ∈ univ.filter (fun t => rs t = r),
        (if M (rs t) c then (1 : ℝ) else 0) from by
      rw [← Finset.sum_biUnion (s := univ)]
      · congr 1; ext t; simp
      · intro r₁ _ r₂ _ hne
        simp only [Function.onFun, Finset.disjoint_filter]
        intro t _ ht1 ht2
        exact hne (ht1.symm.trans ht2)]
  congr 1
  ext r
  rw [Finset.sum_congr rfl (fun t ht => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- Empirical payoff of the MWU row sequence equals the normalized hit count. -/
lemma boolGamePayoff_empirical_eq_hitCount
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    [DecidableEq R]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    {T : ℕ} (hT : 0 < T) (c : C) :
    boolGamePayoff M (FintypePMF.empirical hT (mwuRows M η hη1 v hrow T)) c =
      (mwuHitCount M η hη1 v hrow T c : ℝ) / T := by
  rw [boolGamePayoff_empirical_eq_avg]
  rw [← mwuHitCount_eq_sum_indicator M η hη1 v hrow T c]

end ProbabilityTheory

end
