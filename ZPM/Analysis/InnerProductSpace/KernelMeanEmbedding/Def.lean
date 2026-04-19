/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Kernel mean embedding: definition and `BoundedKernel` class

`BoundedKernel` is the integrability certificate: its instance carries a
uniform bound `C` on the kernel sections `x ↦ kerFun H x 1`, which is
what lets Bochner integration on a finite measure converge.

`kernelMeanEmbedding P := ∫ x, kerFun H x 1 ∂P` is the Bochner integral of
the kernel sections against `P`; it lives in the RKHS `H`.
-/

noncomputable section

open MeasureTheory RKHS

/-- An RKHS with a uniform norm bound on its kernel sections. Integrability
of the kernel sections under any finite measure reduces to this bound plus
`AEStronglyMeasurable`. -/
class BoundedKernel (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {X : Type*} [RKHS ℝ H X ℝ] where
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_kerFun_le : ∀ x : X, ‖kerFun H x (1 : ℝ)‖ ≤ bound

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H X ℝ]
variable [BoundedKernel H (X := X)]

/-- The kernel mean embedding of a measure `P` into the RKHS `H`, defined as
the Bochner integral of the kernel sections. -/
def kernelMeanEmbedding (P : Measure X) : H :=
  ∫ x, kerFun H x (1 : ℝ) ∂P

end
