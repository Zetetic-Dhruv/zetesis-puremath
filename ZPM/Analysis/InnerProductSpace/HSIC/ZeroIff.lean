/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Analysis.InnerProductSpace.HSIC.Def
import ZPM.Analysis.InnerProductSpace.MMD.Characteristic

/-!
# HSIC zero-iff-independent theorem

Under a characteristic kernel on the product space, HSIC vanishes
exactly when the joint distribution equals the product of its marginals.
-/

noncomputable section

open MeasureTheory RKHS

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [SecondCountableTopology H]
variable [RKHS ℝ H (X × Y) ℝ]
variable [BoundedKernel H (X := X × Y)]

omit [TopologicalSpace X] [OpensMeasurableSpace X]
  [TopologicalSpace Y] [OpensMeasurableSpace Y]
  [SecondCountableTopology H] [BoundedKernel H] in
/-- **HSIC characterises independence** under a characteristic kernel.
`hsicDef P = 0 ↔ P = P_X ⊗ P_Y`. -/
theorem hsicDef_zero_iff_independent
    (hchar : IsCharacteristic (H := H) (X := X × Y))
    (P : Measure (X × Y)) :
    hsicDef (H := H) P = 0 ↔ P = (P.map Prod.fst).prod (P.map Prod.snd) := by
  unfold hsicDef
  exact mmdSq_zero_iff hchar P _

end
