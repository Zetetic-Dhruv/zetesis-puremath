/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.InformationTheory.KullbackLeibler.Binary.Def
import ZPM.InformationTheory.KullbackLeibler.Real
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.Convex.Integral

/-!
# Bridging `klBin` to the general KL: Jensen + DPI for indicators

Three steps bridge the binary KL to the full KL via `klFun`:

1. Algebraic identity: `klBin p q = q · klFun(p/q) + (1 − q) · klFun((1 − p)/(1 − q))`.
2. Jensen on a subset: `Q(A) · klFun(avg_A f) ≤ ∫_A klFun(f) dQ`.
3. Data-processing inequality for indicators:
   `klBin(P(A), Q(A)) ≤ (klDiv P Q).toReal`.

These are the three pieces that assemble into the per-set squared bound
`2 (P(A) − Q(A))² ≤ klDivReal P Q` in the next shard.
-/

noncomputable section

namespace InformationTheory

open MeasureTheory Real Set Classical

variable {α : Type*} [MeasurableSpace α]

/-- **Algebraic identity.** The binary KL factors through `klFun`:
`klBin p q = q · klFun(p/q) + (1 − q) · klFun((1 − p)/(1 − q))`. -/
lemma klBin_eq_klFun_sum (p q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    klBin p q = q * klFun (p / q) + (1 - q) * klFun ((1 - p) / (1 - q)) := by
  unfold klBin klFun
  have hq_ne : q ≠ 0 := hq₀.ne'
  have h1q_ne : (1 - q) ≠ 0 := by linarith
  field_simp
  ring

/-- **Jensen on a subset.** For a finite measure `Q` and a measurable set `A` with
positive mass, if `f` and `klFun ∘ f` are integrable and `f ≥ 0` almost everywhere,
then `Q(A) · klFun((1/Q(A)) · ∫_A f dQ) ≤ ∫_A klFun(f) dQ`. -/
lemma klFun_integral_ge_of_measurableSet
    {Q : Measure α} [IsFiniteMeasure Q]
    (f : α → ℝ) (hf_int : Integrable f Q)
    (hf_int_kl : Integrable (fun x => klFun (f x)) Q)
    (hf_nn : ∀ᵐ x ∂Q, 0 ≤ f x)
    {A : Set α} (hQA_pos : 0 < Q.real A) :
    Q.real A * klFun ((Q.real A)⁻¹ * ∫ x in A, f x ∂Q) ≤ ∫ x in A, klFun (f x) ∂Q := by
  have hQA_ne_zero : Q A ≠ 0 := by
    rw [measureReal_def] at hQA_pos
    intro h
    rw [h, ENNReal.toReal_zero] at hQA_pos
    exact absurd hQA_pos (lt_irrefl _)
  have hQA_ne_top : Q A ≠ ⊤ := measure_ne_top Q A
  have hf_int_on : IntegrableOn f A Q := hf_int.integrableOn
  have hf_int_kl_on : IntegrableOn (fun x => klFun (f x)) A Q := hf_int_kl.integrableOn
  have hf_nn_on : ∀ᵐ x ∂(Q.restrict A), f x ∈ Set.Ici (0 : ℝ) := by
    have : ∀ᵐ x ∂(Q.restrict A), 0 ≤ f x := ae_restrict_of_ae hf_nn
    filter_upwards [this] with x hx
    exact hx
  have hjensen := convexOn_klFun.map_set_average_le
    continuous_klFun.continuousOn isClosed_Ici hQA_ne_zero hQA_ne_top hf_nn_on hf_int_on hf_int_kl_on
  rw [setAverage_eq, setAverage_eq] at hjensen
  simp only [smul_eq_mul] at hjensen
  calc Q.real A * klFun ((Q.real A)⁻¹ * ∫ x in A, f x ∂Q)
      ≤ Q.real A * ((Q.real A)⁻¹ * ∫ x in A, klFun (f x) ∂Q) := by
        exact mul_le_mul_of_nonneg_left hjensen hQA_pos.le
    _ = ∫ x in A, klFun (f x) ∂Q := by
        rw [← mul_assoc, mul_inv_cancel₀ hQA_pos.ne', one_mul]

/-- **Data processing inequality for indicators.** For probability measures `P ≪ Q`
with finite KL divergence and any measurable set `A`, the binary KL between the
marginals on `(A, Aᶜ)` is bounded by the full KL:
`klBin(P(A), Q(A)) ≤ klDivReal P Q`. -/
theorem klBin_le_klDivReal
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q) (h_int : Integrable (llr P Q) P)
    (A : Set α) (hA : MeasurableSet A) :
    klBin (P.real A) (Q.real A) ≤ klDivReal P Q := by
  have hkl_eq : klDivReal P Q = ∫ x, klFun ((P.rnDeriv Q x).toReal) ∂Q := by
    rw [klDivReal_eq_toReal_klDiv P Q hac, toReal_klDiv_eq_integral_klFun hac]
  rw [hkl_eq]
  set f : α → ℝ := fun x => (P.rnDeriv Q x).toReal with hf_def
  have hf_nn : ∀ᵐ x ∂Q, 0 ≤ f x := ae_of_all _ fun x => ENNReal.toReal_nonneg
  have hf_int : Integrable f Q := Measure.integrable_toReal_rnDeriv
  have hf_int_kl : Integrable (fun x => klFun (f x)) Q := by
    exact (integrable_klFun_rnDeriv_iff hac).mpr h_int
  have hf_int_A : ∫ x in A, f x ∂Q = P.real A :=
    Measure.setIntegral_toReal_rnDeriv hac A
  have hf_int_Ac : ∫ x in Aᶜ, f x ∂Q = P.real Aᶜ :=
    Measure.setIntegral_toReal_rnDeriv hac Aᶜ
  have h_split : ∫ x, klFun (f x) ∂Q = ∫ x in A, klFun (f x) ∂Q + ∫ x in Aᶜ, klFun (f x) ∂Q :=
    (integral_add_compl hA hf_int_kl).symm
  rw [h_split]
  have hQA_nn : 0 ≤ Q.real A := measureReal_nonneg
  have hQAc_nn : 0 ≤ Q.real Aᶜ := measureReal_nonneg
  have hP_sum : P.real A + P.real Aᶜ = 1 := by
    have := measureReal_add_measureReal_compl (μ := P) hA
    simp [measureReal_def, IsProbabilityMeasure.measure_univ] at this
    exact this
  have hQ_sum : Q.real A + Q.real Aᶜ = 1 := by
    have := measureReal_add_measureReal_compl (μ := Q) hA
    simp [measureReal_def, IsProbabilityMeasure.measure_univ] at this
    exact this
  have h_int_A_nn : 0 ≤ ∫ x in A, klFun (f x) ∂Q := by
    apply setIntegral_nonneg hA
    intro x _
    exact klFun_nonneg ENNReal.toReal_nonneg
  have h_int_Ac_nn : 0 ≤ ∫ x in Aᶜ, klFun (f x) ∂Q := by
    apply setIntegral_nonneg hA.compl
    intro x _
    exact klFun_nonneg ENNReal.toReal_nonneg
  rcases eq_or_lt_of_le hQA_nn with hQA_zero | hQA_pos
  · have hQA_eq : Q.real A = 0 := hQA_zero.symm
    have hQA_ennreal : Q A = 0 := by
      have := measureReal_eq_zero_iff (μ := Q) (s := A) (measure_ne_top Q A)
      exact this.mp hQA_eq
    have hPA_zero : P A = 0 := hac hQA_ennreal
    have hPA_eq : P.real A = 0 := by rw [measureReal_def, hPA_zero, ENNReal.toReal_zero]
    have hQAc_eq : Q.real Aᶜ = 1 := by linarith
    have hPAc_eq : P.real Aᶜ = 1 := by linarith
    have hklBin_eq : klBin (P.real A) (Q.real A) = 0 := by
      rw [hPA_eq, hQA_eq]
      unfold klBin
      simp
    rw [hklBin_eq]
    have : ∫ x in A, klFun (f x) ∂Q = 0 := by
      rw [setIntegral_measure_zero _ hQA_ennreal]
    linarith
  rcases eq_or_lt_of_le hQAc_nn with hQAc_zero | hQAc_pos
  · have hQAc_eq : Q.real Aᶜ = 0 := hQAc_zero.symm
    have hQA_eq : Q.real A = 1 := by linarith
    have hQAc_ennreal : Q Aᶜ = 0 := by
      have := measureReal_eq_zero_iff (μ := Q) (s := Aᶜ) (measure_ne_top Q Aᶜ)
      exact this.mp hQAc_eq
    have hPAc_zero : P Aᶜ = 0 := hac hQAc_ennreal
    have hPAc_eq : P.real Aᶜ = 0 := by rw [measureReal_def, hPAc_zero, ENNReal.toReal_zero]
    have hPA_eq : P.real A = 1 := by linarith
    have hklBin_eq : klBin (P.real A) (Q.real A) = 0 := by
      rw [hPA_eq, hQA_eq]
      unfold klBin
      simp
    rw [hklBin_eq]
    have : ∫ x in Aᶜ, klFun (f x) ∂Q = 0 := by
      rw [setIntegral_measure_zero _ hQAc_ennreal]
    linarith
  have hQA_lt_one : Q.real A < 1 := by linarith
  have hklBin_expand : klBin (P.real A) (Q.real A)
      = Q.real A * klFun (P.real A / Q.real A)
        + (1 - Q.real A) * klFun ((1 - P.real A) / (1 - Q.real A)) :=
    klBin_eq_klFun_sum (P.real A) (Q.real A) hQA_pos hQA_lt_one
  have hjensen_A := klFun_integral_ge_of_measurableSet
    f hf_int hf_int_kl hf_nn hQA_pos
  rw [hf_int_A] at hjensen_A
  have h_rewrite_A : (Q.real A)⁻¹ * P.real A = P.real A / Q.real A := by
    rw [div_eq_inv_mul]
  rw [h_rewrite_A] at hjensen_A
  have hQAc_eq : Q.real Aᶜ = 1 - Q.real A := by linarith
  have hPAc_eq : P.real Aᶜ = 1 - P.real A := by linarith
  have hjensen_Ac := klFun_integral_ge_of_measurableSet
    f hf_int hf_int_kl hf_nn (A := Aᶜ) (by rw [hQAc_eq]; linarith)
  rw [hf_int_Ac] at hjensen_Ac
  have h_rewrite_Ac : (Q.real Aᶜ)⁻¹ * P.real Aᶜ = (1 - P.real A) / (1 - Q.real A) := by
    rw [hQAc_eq, hPAc_eq, div_eq_inv_mul]
  rw [h_rewrite_Ac, hQAc_eq] at hjensen_Ac
  rw [hklBin_expand]
  linarith

end InformationTheory

end
