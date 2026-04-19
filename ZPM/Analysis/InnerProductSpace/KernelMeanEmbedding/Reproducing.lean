/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Analysis.InnerProductSpace.KernelMeanEmbedding.Integrable

/-!
# Reproducing property of the kernel mean embedding

`⟪μ_P, f⟫ = ∫ f dP` for every `f ∈ H`: the inner product of a function
with the kernel mean embedding of `P` equals the expectation of the
function under `P`. The proof routes through Mathlib's `integral_inner`
and the RKHS reproducing property `inner_kerFun`.
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H X ℝ]
variable [BoundedKernel H (X := X)]

/-- **Reproducing property of the kernel mean embedding.**
`⟪μ_P, f⟫ = ∫ f dP` for `f ∈ H` and `P` finite. -/
theorem kernelMeanEmbedding_reproducing
    (P : Measure X) [IsFiniteMeasure P]
    (hcont : Continuous (fun x => kerFun H x (1 : ℝ)))
    (f : H) :
    @inner ℝ H _ (kernelMeanEmbedding (H := H) P) f = ∫ x, f x ∂P := by
  unfold kernelMeanEmbedding
  rw [real_inner_comm]
  rw [← integral_inner (kernelMeanEmbedding_integrable P hcont)]
  congr 1
  ext x
  rw [inner_kerFun, inner_real_one_right]

omit [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- Pointwise reproducing identity: `f x = ⟪kerFun H x 1, f⟫`. -/
lemma rkhs_eval_eq_inner (f : H) (x : X) :
    (f x : ℝ) = @inner ℝ H _ (kerFun H x (1 : ℝ)) f := by
  rw [← inner_real_one_left (f x)]
  exact (kerFun_inner (𝕜 := ℝ) (H := H) (V := ℝ) x 1 f).symm

end
