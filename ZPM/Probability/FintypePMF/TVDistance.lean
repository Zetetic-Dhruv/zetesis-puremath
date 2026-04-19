/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Def

/-!
# Total variation distance between FintypePMFs (L1 form)

`tvDistance p q = ∑ a, |p.prob a - q.prob a|`. This is the L1 form of
total variation; the probabilists' normalised TV is half this quantity.
The L1 form is what the transfer principle composes with directly.
-/

noncomputable section

namespace ProbabilityTheory.FintypePMF

open Finset

/-- L1 total variation distance between two `FintypePMF`s. -/
def tvDistance {α : Type*} [Fintype α]
    (p q : FintypePMF α) : ℝ :=
  ∑ a : α, |p.prob a - q.prob a|

lemma tvDistance_nonneg {α : Type*} [Fintype α]
    (p q : FintypePMF α) :
    0 ≤ tvDistance p q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma tvDistance_comm {α : Type*} [Fintype α]
    (p q : FintypePMF α) :
    tvDistance p q = tvDistance q p := by
  simp only [tvDistance, abs_sub_comm]

lemma tvDistance_self {α : Type*} [Fintype α]
    (p : FintypePMF α) :
    tvDistance p p = 0 := by
  simp [tvDistance]

end ProbabilityTheory.FintypePMF

end
