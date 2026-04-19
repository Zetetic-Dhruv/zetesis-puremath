/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.InformationTheory.Pinsker.Binary
import ZPM.InformationTheory.Pinsker.Bridge
import ZPM.MeasureTheory.ProbabilityMeasure.TotalVariation.Real

/-!
# Pinsker's inequality (general, sharp constant)

Assembles the three layers:

- **Binary Pinsker** gives `2 (p − q)² ≤ klBin p q`.
- **DPI for indicators** gives `klBin(P(A), Q(A)) ≤ klDivReal P Q`.
- Combining them gives the per-set squared bound
  `2 (P(A) − Q(A))² ≤ klDivReal P Q` for every measurable `A`.

Taking `sSup` over measurable sets gives
`tvDistReal P Q ≤ sqrt(klDivReal P Q / 2)`, Pinsker's inequality with
the sharp constant.
-/

noncomputable section

namespace InformationTheory

open MeasureTheory Real Set Classical

variable {α : Type*} [MeasurableSpace α]

/-- **Per-set squared bound.** `2 (P(A) − Q(A))² ≤ klDivReal P Q` for any measurable
set `A`, given `P ≪ Q` and finite KL. -/
theorem two_sq_sub_le_klDivReal
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q) (h_int : Integrable (llr P Q) P)
    (A : Set α) (hA : MeasurableSet A) :
    2 * (P.real A - Q.real A)^2 ≤ klDivReal P Q := by
  have hkl_nn : 0 ≤ klDivReal P Q := klDivReal_nonneg P Q
  have hPA_nn : 0 ≤ P.real A := measureReal_nonneg
  have hQA_nn : 0 ≤ Q.real A := measureReal_nonneg
  have hPA_le_one : P.real A ≤ 1 := by
    have h := measureReal_mono (μ := P) (s₁ := A) (s₂ := Set.univ) (subset_univ _)
      (measure_ne_top P _)
    simpa [IsProbabilityMeasure.measure_univ, measureReal_def] using h
  have hQA_le_one : Q.real A ≤ 1 := by
    have h := measureReal_mono (μ := Q) (s₁ := A) (s₂ := Set.univ) (subset_univ _)
      (measure_ne_top Q _)
    simpa [IsProbabilityMeasure.measure_univ, measureReal_def] using h
  rcases eq_or_lt_of_le hQA_nn with hQA_zero | hQA_pos
  · have hQA_eq : Q.real A = 0 := hQA_zero.symm
    have hQA_ennreal : Q A = 0 := (measureReal_eq_zero_iff (measure_ne_top Q A)).mp hQA_eq
    have hPA_ennreal : P A = 0 := hac hQA_ennreal
    have hPA_eq : P.real A = 0 := by rw [measureReal_def, hPA_ennreal, ENNReal.toReal_zero]
    rw [hPA_eq, hQA_eq]
    simp
    exact hkl_nn
  rcases eq_or_lt_of_le hQA_le_one with hQA_one | hQA_lt
  · have hQ_sum : Q.real A + Q.real Aᶜ = 1 := by
      have := measureReal_add_measureReal_compl (μ := Q) hA
      simp [measureReal_def, IsProbabilityMeasure.measure_univ] at this
      exact this
    have hQAc_eq : Q.real Aᶜ = 0 := by linarith
    have hQAc_ennreal : Q Aᶜ = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top Q Aᶜ)).mp hQAc_eq
    have hPAc_ennreal : P Aᶜ = 0 := hac hQAc_ennreal
    have hPAc_eq : P.real Aᶜ = 0 := by rw [measureReal_def, hPAc_ennreal, ENNReal.toReal_zero]
    have hP_sum : P.real A + P.real Aᶜ = 1 := by
      have := measureReal_add_measureReal_compl (μ := P) hA
      simp [measureReal_def, IsProbabilityMeasure.measure_univ] at this
      exact this
    have hPA_eq : P.real A = 1 := by linarith
    rw [hPA_eq, ← hQA_one]
    simp
    exact hkl_nn
  have h1 : 2 * (P.real A - Q.real A)^2 ≤ klBin (P.real A) (Q.real A) :=
    binary_pinsker (P.real A) (Q.real A) hPA_nn hPA_le_one hQA_pos hQA_lt
  have h2 : klBin (P.real A) (Q.real A) ≤ klDivReal P Q :=
    klBin_le_klDivReal P Q hac h_int A hA
  linarith

/-- **Pinsker's inequality** with the sharp constant.
`tvDistReal P Q ≤ sqrt(klDivReal P Q / 2)` for probability measures `P ≪ Q` with
finite KL divergence. -/
theorem pinsker_proof
    (P Q : Measure α) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q) (h_int : Integrable (llr P Q) P) :
    tvDistReal P Q ≤ Real.sqrt (klDivReal P Q / 2) := by
  have hkl_nn : 0 ≤ klDivReal P Q := klDivReal_nonneg P Q
  have hkl_half_nn : 0 ≤ klDivReal P Q / 2 := by linarith
  unfold tvDistReal
  apply csSup_le (tvDistReal_set_nonempty P Q)
  rintro x ⟨A, hA, rfl⟩
  rw [show |(P A).toReal - (Q A).toReal|
      = Real.sqrt (((P A).toReal - (Q A).toReal)^2) from
    (Real.sqrt_sq_eq_abs _).symm]
  apply Real.sqrt_le_sqrt
  have h := two_sq_sub_le_klDivReal P Q hac h_int A hA
  have hPA : P.real A = (P A).toReal := rfl
  have hQA : Q.real A = (Q A).toReal := rfl
  rw [hPA, hQA] at h
  linarith

end InformationTheory

end
