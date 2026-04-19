/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Binary KL divergence and its boundary values

`klBin p q = p·log(p/q) + (1 − p)·log((1 − p)/(1 − q))`, the KL divergence
between `Bernoulli(p)` and `Bernoulli(q)`. Well-defined for `q ∈ (0, 1)`;
the boundary values at `p = 0`, `p = 1`, and `p = q` reduce to explicit
log-terms via the conventional `log 0 = 0`.
-/

namespace InformationTheory

/-- Binary KL divergence between `Bernoulli(p)` and `Bernoulli(q)`. -/
noncomputable def klBin (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- `klBin p p = 0` for `p ∈ (0, 1)`. -/
lemma klBin_self (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    klBin p p = 0 := by
  unfold klBin
  have h1 : p / p = 1 := div_self hp₀.ne'
  have h2 : (1 - p) / (1 - p) = 1 := div_self (by linarith : (1 - p) ≠ 0)
  rw [h1, h2, Real.log_one]
  ring

/-- Boundary case: `klBin 0 q = -log(1 - q)`. -/
lemma klBin_zero_left (q : ℝ) :
    klBin 0 q = -Real.log (1 - q) := by
  unfold klBin
  rw [zero_mul, zero_add, sub_zero]
  have h1 : (1 : ℝ) / (1 - q) = (1 - q)⁻¹ := one_div (1 - q)
  rw [h1, Real.log_inv]
  ring

/-- Boundary case: `klBin 1 q = -log q`. -/
lemma klBin_one_left (q : ℝ) :
    klBin 1 q = -Real.log q := by
  unfold klBin
  rw [sub_self, zero_mul, add_zero, one_mul]
  have h1 : (1 : ℝ) / q = q⁻¹ := one_div q
  rw [h1, Real.log_inv]

/-- Expanded form: split into constants and `q`-dependent pieces. Used to compute the
derivative via `HasDerivAt` in the next shard. -/
lemma klBin_expand (p q : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    klBin p q = p * Real.log p - p * Real.log q
              + (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - q) := by
  unfold klBin
  rw [Real.log_div hp₀.ne' hq₀.ne',
      Real.log_div (by linarith : (1 - p) ≠ 0) (by linarith : (1 - q) ≠ 0)]
  ring

end InformationTheory
