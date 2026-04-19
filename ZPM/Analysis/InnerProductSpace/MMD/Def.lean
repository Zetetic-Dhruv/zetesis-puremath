/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Analysis.InnerProductSpace.KernelMeanEmbedding.Basic

/-!
# Maximum Mean Discrepancy (MMD²)

`mmdSq P Q := ‖μ_P − μ_Q‖²` where `μ_·` is the kernel mean embedding.
Basic properties: nonnegativity, `mmdSq P P = 0`, symmetry.
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H X ℝ]
variable [BoundedKernel H (X := X)]

/-- Squared MMD between two measures `P` and `Q` via their kernel mean embeddings. -/
def mmdSq (P Q : Measure X) : ℝ :=
  ‖kernelMeanEmbedding (H := H) P - kernelMeanEmbedding (H := H) Q‖ ^ 2

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- MMD² is nonnegative. -/
theorem mmdSq_nonneg (P Q : Measure X) : 0 ≤ mmdSq (H := H) P Q :=
  sq_nonneg _

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- MMD²(P, P) = 0. -/
theorem mmdSq_self (P : Measure X) : mmdSq (H := H) P P = 0 := by
  unfold mmdSq
  rw [sub_self, norm_zero, sq, mul_zero]

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- MMD² is symmetric. -/
theorem mmdSq_comm (P Q : Measure X) : mmdSq (H := H) P Q = mmdSq (H := H) Q P := by
  unfold mmdSq
  rw [norm_sub_rev]

end
