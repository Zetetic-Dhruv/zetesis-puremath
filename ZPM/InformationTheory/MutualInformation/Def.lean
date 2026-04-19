/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.InformationTheory.KullbackLeibler.Real

/-!
# Mutual information between two components of a joint distribution

`mutualInformationReal P = klDivReal P (P_A ⊗ P_B)` where
`P_A = P.map Prod.fst` and `P_B = P.map Prod.snd`. ℝ-valued throughout,
so downstream `linarith` / `nlinarith` / `field_simp` work directly.
-/

noncomputable section

namespace InformationTheory

open MeasureTheory

/-- ℝ-valued mutual information of a joint measure. -/
def mutualInformationReal {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure (α × β)) : ℝ :=
  klDivReal P ((P.map Prod.fst).prod (P.map Prod.snd))

end InformationTheory

end
