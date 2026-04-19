/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Analysis.InnerProductSpace.MMD.Def
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Hilbert-Schmidt Independence Criterion (HSIC): definition

`hsicDef P := MMD²(P, P_X ⊗ P_Y)` where `P_X` and `P_Y` are the marginals
of `P` on `X × Y`. Nonnegative; zero when `P` factors as an independent
product.
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H (X × Y) ℝ]
variable [BoundedKernel H (X := X × Y)]

/-- Hilbert-Schmidt Independence Criterion: `MMD²(P, P_X ⊗ P_Y)`. -/
def hsicDef (P : Measure (X × Y)) : ℝ :=
  mmdSq (H := H) P ((P.map Prod.fst).prod (P.map Prod.snd))

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- HSIC is nonnegative. -/
theorem hsicDef_nonneg (P : Measure (X × Y)) : 0 ≤ hsicDef (H := H) P :=
  mmdSq_nonneg _ _

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- If the joint distribution is an independent product, HSIC vanishes. -/
theorem hsicDef_eq_zero_of_independent
    (P : Measure (X × Y))
    (hind : P = (P.map Prod.fst).prod (P.map Prod.snd)) :
    hsicDef (H := H) P = 0 := by
  unfold hsicDef
  have : mmdSq (H := H) P ((P.map Prod.fst).prod (P.map Prod.snd)) =
      mmdSq (H := H) ((P.map Prod.fst).prod (P.map Prod.snd))
        ((P.map Prod.fst).prod (P.map Prod.snd)) :=
    congr_arg (mmdSq (H := H) · _) hind
  rw [this]
  exact mmdSq_self (H := H) _

end
