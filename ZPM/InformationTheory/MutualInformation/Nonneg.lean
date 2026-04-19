/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.InformationTheory.MutualInformation.Def

/-!
# Nonnegativity of mutual information

Delegates to `klDivReal_nonneg` after establishing that the product of
marginals of a probability measure is itself a probability measure.
-/

noncomputable section

namespace InformationTheory

open MeasureTheory

/-- Mutual information is nonnegative for probability measures. -/
theorem mutualInformationReal_nonneg {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure (α × β)) [IsProbabilityMeasure P] :
    0 ≤ mutualInformationReal P := by
  unfold mutualInformationReal
  haveI : IsProbabilityMeasure (P.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (P.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact klDivReal_nonneg P _

end InformationTheory

end
