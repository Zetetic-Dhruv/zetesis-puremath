/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Arithmetic core: hit-rate lower bound from the potential bound

The real-analytic step of the MWU regret argument. Starting from the T-step
potential upper bound `(1 - η)^H ≤ N · (1 - η · v)^T` on an individual
column, together with sufficiently small `η` and sufficiently large `T`,
deduce the per-column hit-rate lower bound `v - ε ≤ H / T`.

Pure real-analysis: `Real.log` monotonicity + `log (1-x) ≤ -x` +
`-η/(1-η) ≤ log(1-η)` + `linarith`/`nlinarith` bookkeeping.
-/

namespace ProbabilityTheory

/-- Arithmetic core of the MWU regret bound. From the potential bound plus the step-size
feasibility conditions, deduce `v - ε ≤ H / T`. -/
lemma hitRate_from_potential
    {N H T : ℕ} {η v ε : ℝ}
    (hNpos : 0 < (N : ℝ))
    (hη : 0 < η) (hη1 : η < 1)
    (hv1 : v ≤ 1)
    (hTpos : 0 < T)
    (hpot :
      (1 - η) ^ H ≤ (N : ℝ) * (1 - η * v) ^ T)
    (hηsmall : η ≤ ε / 4)
    (hlargeT : Real.log (N : ℝ) / (η * T) ≤ ε / 4) :
    v - ε ≤ (H : ℝ) / T := by
  have hbase : 0 < 1 - η := by linarith
  have hbasev : 0 < 1 - η * v := by
    have hηv_le : η * v ≤ η := mul_le_of_le_one_right (le_of_lt hη) hv1
    linarith
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hHnonneg : 0 ≤ (H : ℝ) := by positivity
  have hlog :
      (H : ℝ) * Real.log (1 - η) ≤
        Real.log (N : ℝ) + (T : ℝ) * Real.log (1 - η * v) := by
    have h0 :
        Real.log ((1 - η) ^ H) ≤
          Real.log ((N : ℝ) * (1 - η * v) ^ T) := by
      exact Real.log_le_log (pow_pos hbase H) hpot
    rw [Real.log_pow,
      Real.log_mul hNne (pow_ne_zero T (ne_of_gt hbasev)),
      Real.log_pow] at h0
    simpa [mul_comm, mul_left_comm, mul_assoc] using h0
  have hlog_up : Real.log (1 - η * v) ≤ -η * v :=
    by linarith [Real.log_le_sub_one_of_pos hbasev]
  have hlog_down : -η / (1 - η) ≤ Real.log (1 - η) := by
    have h := Real.one_sub_inv_le_log_of_pos hbase
    have hne : 1 - η ≠ 0 := by linarith
    have hrew : 1 - (1 - η)⁻¹ = -η / (1 - η) := by field_simp [hne]; ring
    simpa [hrew] using h
  have hTreal_nonneg : (0 : ℝ) ≤ T := by positivity
  have hanti :
      (T : ℝ) * η * v - Real.log (N : ℝ) ≤
        (H : ℝ) * (-Real.log (1 - η)) := by
    by_cases hv_sign : 0 ≤ v
    · nlinarith [mul_nonneg hTreal_nonneg (mul_nonneg (le_of_lt hη) hv_sign)]
    · push Not at hv_sign
      have hlog_neg : Real.log (1 - η) < 0 := Real.log_neg (by linarith) (by linarith)
      have h_rhs_nn : 0 ≤ (H : ℝ) * (-Real.log (1 - η)) := mul_nonneg hHnonneg (by linarith)
      have hTreal_pos : (0 : ℝ) < T := by exact_mod_cast hTpos
      have h_Tηv_neg : (T : ℝ) * η * v < 0 := by
        have := mul_neg_of_pos_of_neg hη hv_sign
        nlinarith
      linarith [Real.log_natCast_nonneg N]
  have hcoef : -Real.log (1 - η) ≤ η / (1 - η) := by
    have : -η / (1 - η) = -(η / (1 - η)) := by ring
    linarith
  have hanti' :
      (T : ℝ) * η * v - Real.log (N : ℝ) ≤
        (H : ℝ) * (η / (1 - η)) :=
    le_trans hanti (mul_le_mul_of_nonneg_left hcoef hHnonneg)
  have hnum :
      (1 - η) * ((T : ℝ) * η * v - Real.log (N : ℝ)) ≤ (H : ℝ) * η := by
    have h1η_nonneg : 0 ≤ 1 - η := by linarith
    calc (1 - η) * ((T : ℝ) * η * v - Real.log (N : ℝ))
        ≤ (1 - η) * ((H : ℝ) * (η / (1 - η))) :=
          mul_le_mul_of_nonneg_left hanti' h1η_nonneg
      _ = (H : ℝ) * η := by field_simp [show (1 : ℝ) - η ≠ 0 by linarith]; try ring
  have hηTpos : 0 < η * (T : ℝ) := by positivity
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hTpos)
  have hrate0 :
      (1 - η) * v - ((1 - η) * Real.log (N : ℝ)) / (η * T) ≤ (H : ℝ) / T := by
    have hdiv :=
      div_le_div_of_nonneg_right hnum (show 0 ≤ η * (T : ℝ) by positivity)
    have hsimpL :
        ((1 - η) * ((T : ℝ) * η * v - Real.log (N : ℝ))) / (η * T) =
          (1 - η) * v - ((1 - η) * Real.log (N : ℝ)) / (η * T) := by
      field_simp [show η ≠ 0 from ne_of_gt hη, hTne]; try ring
    have hsimpR :
        ((H : ℝ) * η) / (η * T) = (H : ℝ) / T := by
      field_simp [show η ≠ 0 from ne_of_gt hη, hTne]; try ring
    simpa [hsimpL, hsimpR] using hdiv
  have hterm1 : v - ε / 4 ≤ (1 - η) * v := by nlinarith [hηsmall, hv1]
  have hlog_nonneg : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have haux : Real.log (N : ℝ) ≤ (ε / 4) * (η * T) := (div_le_iff₀ hηTpos).mp hlargeT
  have hterm2 :
      ((1 - η) * Real.log (N : ℝ)) / (η * T) ≤ ε / 4 := by
    apply (div_le_iff₀ hηTpos).2
    nlinarith [haux, hlog_nonneg]
  linarith

end ProbabilityTheory
