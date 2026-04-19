/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Analysis.InnerProductSpace.MMD.Def

/-!
# Characteristic kernels and the MMD zero-iff-equal theorem

A kernel is characteristic when its kernel mean embedding is injective.
Under such a kernel, `mmdSq P Q = 0 ↔ P = Q`, making the MMD a genuine
metric on probability measures.
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H X ℝ]
variable [BoundedKernel H (X := X)]

/-- A kernel is *characteristic* when its kernel mean embedding is injective. -/
def IsCharacteristic : Prop :=
  Function.Injective (kernelMeanEmbedding (H := H) (X := X))

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- Under a characteristic kernel, `mmdSq P Q = 0 ↔ P = Q`. -/
theorem mmdSq_zero_iff
    (hchar : IsCharacteristic (H := H) (X := X))
    (P Q : Measure X) :
    mmdSq (H := H) P Q = 0 ↔ P = Q := by
  constructor
  · intro h
    have h1 : ‖kernelMeanEmbedding (H := H) P - kernelMeanEmbedding (H := H) Q‖ = 0 := by
      unfold mmdSq at h
      rwa [sq_eq_zero_iff] at h
    have h2 : kernelMeanEmbedding (H := H) P - kernelMeanEmbedding (H := H) Q = 0 :=
      norm_eq_zero.mp h1
    have h3 : kernelMeanEmbedding (H := H) P = kernelMeanEmbedding (H := H) Q :=
      sub_eq_zero.mp h2
    exact hchar h3
  · intro h
    rw [h]
    exact mmdSq_self Q

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- Forward direction of `mmdSq_zero_iff`. -/
theorem mmdSq_eq_zero
    (hchar : IsCharacteristic (H := H) (X := X))
    {P Q : Measure X}
    (h : mmdSq (H := H) P Q = 0) :
    P = Q :=
  (mmdSq_zero_iff hchar P Q).mp h

end
