/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.InformationTheory.KullbackLeibler.Binary.Def
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Derivatives of `klBin` and the auxiliary function `g(q) = klBin p q − 2 (p − q)²`

The derivative of `klBin p q` with respect to `q` is `(q − p) / (q (1 − q))`.
The derivative of `(p − q)²` is `−2 (p − q)`. Their difference gives the
factored form `(q − p) · (1 − 2q)² / (q (1 − q))`, whose sign reduces to
`sign(q − p)`.
-/

noncomputable section

namespace InformationTheory

/-- Derivative of `klBin p ·` at a point `q ∈ (0, 1)` with `p ∈ (0, 1)`. -/
lemma hasDerivAt_klBin_q (p q : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    HasDerivAt (fun q => klBin p q) ((q - p) / (q * (1 - q))) q := by
  have h_eq : (fun q : ℝ => klBin p q) =ᶠ[nhds q]
              (fun q : ℝ => p * Real.log p - p * Real.log q
                    + (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - q)) := by
    filter_upwards [Ioo_mem_nhds hq₀ hq₁] with x hx
    exact klBin_expand p x hp₀ hp₁ hx.1 hx.2
  refine HasDerivAt.congr_of_eventuallyEq ?_ h_eq
  have h1 : HasDerivAt (fun q => Real.log q) q⁻¹ q := Real.hasDerivAt_log hq₀.ne'
  have h2 : HasDerivAt (fun q => Real.log (1 - q)) (-(1 - q)⁻¹) q := by
    have h_sub : HasDerivAt (fun q : ℝ => 1 - q) (-1 : ℝ) q := by
      simpa using (hasDerivAt_id q).const_sub 1
    have h_log := Real.hasDerivAt_log (by linarith : (1 - q) ≠ 0)
    have hcomp := h_log.comp q h_sub
    convert hcomp using 1
    ring
  have hd1 : HasDerivAt (fun q => p * Real.log p) 0 q :=
    hasDerivAt_const q _
  have hd2 : HasDerivAt (fun q => p * Real.log q) (p * q⁻¹) q := h1.const_mul p
  have hd3 : HasDerivAt (fun q => (1 - p) * Real.log (1 - p)) 0 q :=
    hasDerivAt_const q _
  have hd4 : HasDerivAt (fun q => (1 - p) * Real.log (1 - q))
      ((1 - p) * (-(1 - q)⁻¹)) q := h2.const_mul (1 - p)
  have hsum := ((hd1.sub hd2).add hd3).sub hd4
  convert hsum using 1
  have hq_ne : q ≠ 0 := hq₀.ne'
  have hq1_ne : (1 - q) ≠ 0 := by linarith
  field_simp
  ring

/-- Derivative of `(p − q)²` with respect to `q`. -/
lemma hasDerivAt_sub_sq (p q : ℝ) :
    HasDerivAt (fun q : ℝ => (p - q)^2) (-2 * (p - q)) q := by
  have h1 : HasDerivAt (fun q : ℝ => p - q) (-1 : ℝ) q := by
    simpa using (hasDerivAt_id q).const_sub p
  have := h1.pow 2
  convert this using 1
  ring

/-- **Factored derivative identity.** Derivative of `g(q) := klBin(p, q) − 2 (p − q)²`
has the factored form `(q − p) · (1 − 2q)² / (q · (1 − q))`, reducing the sign of
the derivative to `sign(q − p)`. -/
lemma hasDerivAt_g (p q : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    HasDerivAt
      (fun q => klBin p q - 2 * (p - q)^2)
      ((q - p) * (1 - 2*q)^2 / (q * (1 - q)))
      q := by
  have h1 := hasDerivAt_klBin_q p q hp₀ hp₁ hq₀ hq₁
  have h2 : HasDerivAt (fun q : ℝ => 2 * (p - q)^2) (2 * (-2 * (p - q))) q :=
    (hasDerivAt_sub_sq p q).const_mul 2
  have h3 := h1.sub h2
  convert h3 using 1
  have hq_ne : q ≠ 0 := hq₀.ne'
  have hq1_ne : (1 - q) ≠ 0 := by linarith
  field_simp
  ring

end InformationTheory

end
