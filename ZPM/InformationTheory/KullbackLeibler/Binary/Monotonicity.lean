/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.InformationTheory.KullbackLeibler.Binary.Derivatives
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Monotonicity of `g(q) = klBin p q − 2 (p − q)²` on `(0, p]` and `[p, 1)`

The derivative factor `(1 − 2q)² / (q (1 − q))` is nonnegative on `(0, 1)`,
so the sign of the derivative of `g` reduces to `sign(q − p)`. This makes
`g` antitone on `(0, p]` and monotone on `[p, 1)`. These are the two
intervals that the binary Pinsker proof reduces to via case split on
`p ≤ q` vs `q ≤ p`.
-/

noncomputable section

namespace InformationTheory

open Set

/-- The derivative factor `(1 − 2q)² / (q (1 − q))` is nonnegative on `(0, 1)`. -/
lemma deriv_factor_nonneg (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    0 ≤ (1 - 2*q)^2 / (q * (1 - q)) := by
  apply div_nonneg (sq_nonneg _)
  exact (mul_pos hq₀ (by linarith : (0 : ℝ) < 1 - q)).le

/-- On `[p, 1)`: derivative of `g` is nonnegative. -/
lemma deriv_g_nonneg_of_ge (p q : ℝ) (hpq : p ≤ q) (hq₀ : 0 < q) (hq₁ : q < 1) :
    0 ≤ (q - p) * (1 - 2*q)^2 / (q * (1 - q)) := by
  have hf : 0 ≤ (1 - 2*q)^2 / (q * (1 - q)) := deriv_factor_nonneg q hq₀ hq₁
  have hqp : 0 ≤ q - p := by linarith
  rw [mul_div_assoc]
  exact mul_nonneg hqp hf

/-- On `(0, p]`: derivative of `g` is nonpositive. -/
lemma deriv_g_nonpos_of_le (p q : ℝ) (hqp : q ≤ p) (hq₀ : 0 < q) (hq₁ : q < 1) :
    (q - p) * (1 - 2*q)^2 / (q * (1 - q)) ≤ 0 := by
  have hf : 0 ≤ (1 - 2*q)^2 / (q * (1 - q)) := deriv_factor_nonneg q hq₀ hq₁
  have hqp' : q - p ≤ 0 := by linarith
  rw [mul_div_assoc]
  exact mul_nonpos_of_nonpos_of_nonneg hqp' hf

/-- Continuity of `klBin p ·` on `Ico p 1`. -/
private lemma continuousOn_klBin_Ico (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ContinuousOn (fun q => klBin p q) (Set.Ico p 1) := by
  intro q hq
  have hq₀ : 0 < q := lt_of_lt_of_le hp₀ hq.1
  have hq₁ : q < 1 := hq.2
  exact (hasDerivAt_klBin_q p q hp₀ hp₁ hq₀ hq₁).continuousAt.continuousWithinAt

/-- Continuity of `klBin p ·` on `Ioc 0 p`. -/
private lemma continuousOn_klBin_Ioc (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ContinuousOn (fun q => klBin p q) (Set.Ioc 0 p) := by
  intro q hq
  have hq₀ : 0 < q := hq.1
  have hq₁ : q < 1 := lt_of_le_of_lt hq.2 hp₁
  exact (hasDerivAt_klBin_q p q hp₀ hp₁ hq₀ hq₁).continuousAt.continuousWithinAt

/-- Continuity of `fun q => (p - q)²` on any set. -/
private lemma continuousOn_sub_sq (p : ℝ) (s : Set ℝ) :
    ContinuousOn (fun q : ℝ => (p - q)^2) s :=
  (Continuous.continuousOn (by continuity))

/-- Continuity of `g` on `Ico p 1`. -/
private lemma continuousOn_g_Ico (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ContinuousOn (fun q => klBin p q - 2 * (p - q)^2) (Set.Ico p 1) := by
  apply ContinuousOn.sub (continuousOn_klBin_Ico p hp₀ hp₁)
  exact continuousOn_const.mul (continuousOn_sub_sq p _)

/-- Continuity of `g` on `Ioc 0 p`. -/
private lemma continuousOn_g_Ioc (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ContinuousOn (fun q => klBin p q - 2 * (p - q)^2) (Set.Ioc 0 p) := by
  apply ContinuousOn.sub (continuousOn_klBin_Ioc p hp₀ hp₁)
  exact continuousOn_const.mul (continuousOn_sub_sq p _)

/-- `g(q) = klBin p q − 2 (p − q)²` is monotone on `[p, 1)`. -/
lemma monotoneOn_g (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    MonotoneOn (fun q => klBin p q - 2 * (p - q)^2) (Set.Ico p 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ico p 1)
  · exact continuousOn_g_Ico p hp₀ hp₁
  · rw [interior_Ico]
    intro q hq
    have hq₀ : 0 < q := lt_trans hp₀ hq.1
    exact (hasDerivAt_g p q hp₀ hp₁ hq₀ hq.2).differentiableAt.differentiableWithinAt
  · rw [interior_Ico]
    intro q hq
    have hq₀ : 0 < q := lt_trans hp₀ hq.1
    rw [(hasDerivAt_g p q hp₀ hp₁ hq₀ hq.2).deriv]
    exact deriv_g_nonneg_of_ge p q hq.1.le hq₀ hq.2

/-- `g(q) = klBin p q − 2 (p − q)²` is antitone on `(0, p]`. -/
lemma antitoneOn_g (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    AntitoneOn (fun q => klBin p q - 2 * (p - q)^2) (Set.Ioc 0 p) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioc 0 p)
  · exact continuousOn_g_Ioc p hp₀ hp₁
  · rw [interior_Ioc]
    intro q hq
    have hq₁ : q < 1 := lt_trans hq.2 hp₁
    exact (hasDerivAt_g p q hp₀ hp₁ hq.1 hq₁).differentiableAt.differentiableWithinAt
  · rw [interior_Ioc]
    intro q hq
    have hq₁ : q < 1 := lt_trans hq.2 hp₁
    rw [(hasDerivAt_g p q hp₀ hp₁ hq.1 hq₁).deriv]
    exact deriv_g_nonpos_of_le p q hq.2.le hq.1 hq₁

end InformationTheory

end
