/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Analysis.InnerProductSpace.KernelMeanEmbedding.Def
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrability of kernel sections under finite measures

Bounded kernel sections have a uniform norm bound via `BoundedKernel`, and
finite measures bound the integral of constants. Together these give
`Integrable (fun x => kerFun H x 1) P` for any finite measure `P`.
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H X ℝ]
variable [BoundedKernel H (X := X)]

/-- Bounded kernel sections are integrable under any finite measure. -/
lemma kernelMeanEmbedding_integrable
    (P : Measure X) [IsFiniteMeasure P]
    (hcont : Continuous (fun x => kerFun H x (1 : ℝ))) :
    Integrable (fun x => kerFun H x (1 : ℝ)) P := by
  apply MemLp.integrable le_top
  exact memLp_top_of_bound
    hcont.aestronglyMeasurable
    (BoundedKernel.bound (H := H) (X := X))
    (Filter.Eventually.of_forall (BoundedKernel.norm_kerFun_le (H := H) (X := X)))

/-- `⟪a, 1⟫_ℝ = a` in the real inner product space. -/
lemma inner_real_one_right (a : ℝ) : @inner ℝ ℝ _ a 1 = a := by
  change 1 * starRingEnd ℝ a = a
  simp

/-- `⟪1, a⟫_ℝ = a` in the real inner product space. -/
lemma inner_real_one_left (a : ℝ) : @inner ℝ ℝ _ 1 a = a := by
  rw [real_inner_comm]
  exact inner_real_one_right a

end
