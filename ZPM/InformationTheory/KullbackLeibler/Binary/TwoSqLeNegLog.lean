/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Boundary inequality: `2 q² ≤ -log(1 - q)` on `[0, 1)`

The two variants `two_sq_le_neg_log_one_sub` and `two_sq_le_neg_log`
handle the `p = 0` and `p = 1` boundary cases of the binary Pinsker
theorem. Proved via monotonicity of `h(q) = -log(1-q) - 2 q²` on `[0, 1)`;
the derivative `1/(1-q) - 4q = (2q-1)²/(1-q) ≥ 0`.
-/

namespace InformationTheory

open Set

/-- Derivative of `h(q) = -log(1-q) - 2 q²` at `q < 1`. -/
private lemma hasDerivAt_h_zero (q : ℝ) (hq₁ : q < 1) :
    HasDerivAt (fun q : ℝ => -Real.log (1 - q) - 2 * q^2) ((2*q - 1)^2 / (1 - q)) q := by
  have h1q_ne : (1 - q) ≠ 0 := by linarith
  have h1q_pos : 0 < 1 - q := by linarith
  have h_sub : HasDerivAt (fun q : ℝ => 1 - q) (-1 : ℝ) q := by
    simpa using (hasDerivAt_id q).const_sub 1
  have h_log := Real.hasDerivAt_log h1q_ne
  have hlog1q := h_log.comp q h_sub
  have hneg_log : HasDerivAt (fun q : ℝ => -Real.log (1 - q)) ((1 - q)⁻¹) q := by
    convert hlog1q.neg using 1
    ring
  have hsq : HasDerivAt (fun q : ℝ => 2 * q^2) (4 * q) q := by
    have h_id : HasDerivAt (fun x : ℝ => x) (1 : ℝ) q := hasDerivAt_id q
    have h_pow := h_id.pow 2
    have h_mul := h_pow.const_mul 2
    convert h_mul using 1
    ring
  have hsum := hneg_log.sub hsq
  convert hsum using 1
  field_simp
  ring

/-- `h(q) = -log(1-q) - 2 q²` is monotone on `[0, 1)`. -/
private lemma monotoneOn_h_zero : MonotoneOn (fun q : ℝ => -Real.log (1 - q) - 2 * q^2)
    (Set.Ico (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico 0 1)
  · intro q hq
    have hq₁ : q < 1 := hq.2
    exact (hasDerivAt_h_zero q hq₁).continuousAt.continuousWithinAt
  · rw [interior_Ico]
    intro q hq
    exact (hasDerivAt_h_zero q hq.2).differentiableAt.differentiableWithinAt
  · rw [interior_Ico]
    intro q hq
    rw [(hasDerivAt_h_zero q hq.2).deriv]
    apply div_nonneg (sq_nonneg _)
    linarith [hq.2]

/-- `2 q² ≤ -log(1 - q)` for `q ∈ [0, 1)`. -/
lemma two_sq_le_neg_log_one_sub (q : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    2 * q^2 ≤ -Real.log (1 - q) := by
  have h0_mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) 1 := ⟨le_refl 0, one_pos⟩
  have hq_mem : q ∈ Set.Ico (0 : ℝ) 1 := ⟨hq₀, hq₁⟩
  have hmono := monotoneOn_h_zero h0_mem hq_mem hq₀
  simp at hmono
  linarith

/-- `2 (1 - q)² ≤ -log q` for `q ∈ (0, 1]`. Substitute `r = 1 - q` into the previous. -/
lemma two_sq_le_neg_log (q : ℝ) (hq₀ : 0 < q) (hq₁ : q ≤ 1) :
    2 * (1 - q)^2 ≤ -Real.log q := by
  have hr₀ : (0 : ℝ) ≤ 1 - q := by linarith
  have hr₁ : (1 - q) < 1 := by linarith
  have := two_sq_le_neg_log_one_sub (1 - q) hr₀ hr₁
  have h_sub : (1 : ℝ) - (1 - q) = q := by ring
  rw [h_sub] at this
  exact this

end InformationTheory
