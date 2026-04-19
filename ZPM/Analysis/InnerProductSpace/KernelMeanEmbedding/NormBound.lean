/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Analysis.InnerProductSpace.KernelMeanEmbedding.Reproducing

/-!
# Norm bounds for RKHS functions and the kernel mean embedding

Point-evaluation bound: `‖f x‖ ≤ C · ‖f‖` where `C = BoundedKernel.bound`.
RKHS functions are continuous and integrable under finite measures.
The kernel mean embedding of a probability measure has norm at most `C`.
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H X ℝ]
variable [BoundedKernel H (X := X)]

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] in
/-- Pointwise bound on RKHS function evaluations via Cauchy-Schwarz. -/
lemma norm_apply_le_bound_mul_norm (f : H) (x : X) :
    ‖f x‖ ≤ BoundedKernel.bound (H := H) (X := X) * ‖f‖ := by
  rw [Real.norm_eq_abs, rkhs_eval_eq_inner f x]
  calc |@inner ℝ H _ (kerFun H x (1 : ℝ)) f|
      ≤ ‖kerFun H x (1 : ℝ)‖ * ‖f‖ := abs_real_inner_le_norm _ _
    _ ≤ BoundedKernel.bound (H := H) (X := X) * ‖f‖ :=
        mul_le_mul_of_nonneg_right (BoundedKernel.norm_kerFun_le x) (norm_nonneg _)

omit [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology H]
  [BoundedKernel H] in
/-- `x ↦ f x` is continuous whenever the kernel section map is. -/
lemma continuous_rkhs_apply
    (hcont : Continuous (fun x => kerFun H x (1 : ℝ)))
    (f : H) :
    Continuous (fun x => f x) := by
  have heq : (fun x => f x) = (fun x => @inner ℝ H _ (kerFun H x (1 : ℝ)) f) := by
    ext x; exact rkhs_eval_eq_inner f x
  rw [heq]
  exact hcont.inner continuous_const

omit [SecondCountableTopology H] in
/-- RKHS functions are integrable under any finite measure when the kernel is bounded. -/
lemma rkhs_fun_integrable
    (P : Measure X) [IsFiniteMeasure P]
    (hcont : Continuous (fun x => kerFun H x (1 : ℝ)))
    (f : H) :
    Integrable (fun x => f x) P := by
  apply MemLp.integrable le_top
  exact memLp_top_of_bound
    (continuous_rkhs_apply hcont f).aestronglyMeasurable
    (BoundedKernel.bound (H := H) (X := X) * ‖f‖)
    (Filter.Eventually.of_forall (norm_apply_le_bound_mul_norm f))

omit [TopologicalSpace X] [OpensMeasurableSpace X] [SecondCountableTopology H] in
/-- Norm of the kernel mean embedding of a probability measure is bounded by the
kernel bound. -/
theorem kernelMeanEmbedding_norm_le
    (P : Measure X) [IsProbabilityMeasure P] :
    ‖kernelMeanEmbedding (H := H) P‖ ≤ BoundedKernel.bound (H := H) (X := X) := by
  unfold kernelMeanEmbedding
  calc ‖∫ x, kerFun H x (1 : ℝ) ∂P‖
      ≤ ∫ x, ‖kerFun H x (1 : ℝ)‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ _, BoundedKernel.bound (H := H) (X := X) ∂P := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun _ => norm_nonneg _)
        · exact integrable_const _
        · exact Filter.Eventually.of_forall (BoundedKernel.norm_kerFun_le (H := H) (X := X))
    _ = BoundedKernel.bound (H := H) (X := X) := by
        rw [integral_const, probReal_univ, one_smul]

end
