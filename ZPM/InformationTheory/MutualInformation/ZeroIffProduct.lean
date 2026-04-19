/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.InformationTheory.MutualInformation.Def

/-!
# MI = 0 ↔ joint equals product of marginals

Under absolute continuity of the joint with respect to the product of its
marginals, and finite KL, MI vanishes iff the joint is the independent
product. The finite-KL hypothesis is mathematically necessary for the
forward direction: without it, a non-integrable log-likelihood ratio
collapses the Bochner integral to 0 even when the measures differ.
-/

noncomputable section

namespace InformationTheory

open MeasureTheory

/-- MI vanishes iff the joint is the product of its marginals, under
absolute continuity and finite KL. -/
theorem mutualInformationReal_eq_zero_iff_product {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (P : Measure (α × β)) [IsProbabilityMeasure P]
    (hac : P.AbsolutelyContinuous ((P.map Prod.fst).prod (P.map Prod.snd)))
    (hfin : InformationTheory.klDiv P ((P.map Prod.fst).prod (P.map Prod.snd)) ≠ ⊤) :
    mutualInformationReal P = 0 ↔ P = (P.map Prod.fst).prod (P.map Prod.snd) := by
  unfold mutualInformationReal
  haveI : IsProbabilityMeasure (P.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  haveI : IsProbabilityMeasure (P.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  exact klDivReal_eq_zero_iff P _ hac hfin

end InformationTheory

end
