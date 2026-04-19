/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Def

/-!
# Strictly-positive-prior typeclass

`HasPositivePrior P` certifies that every weight of the `FintypePMF` `P`
is strictly positive. Useful for divergence computations where
`log(0/·)` conventions would otherwise need case-splits.
-/

namespace ProbabilityTheory.FintypePMF

/-- A `FintypePMF` with strictly positive weights on every element. -/
class HasPositivePrior {α : Type*} [Fintype α] (P : FintypePMF α) : Prop where
  pos : ∀ a, 0 < P.prob a

end ProbabilityTheory.FintypePMF
