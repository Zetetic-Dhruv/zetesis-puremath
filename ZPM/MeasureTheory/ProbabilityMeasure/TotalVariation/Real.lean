/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Total variation distance between probability measures (ℝ-valued, metric form)

`tvDistReal P Q = sup { |P(A).toReal - Q(A).toReal| | A measurable }`.
The supremum form used by the Pinsker argument; equivalent to the L1 form
on discrete supports up to a factor of 2.

This is distinct from `ProbabilityTheory.FintypePMF.tvDistance`, which is
the Fintype L1 form.
-/

noncomputable section

namespace MeasureTheory

open Set

variable {α : Type*} [MeasurableSpace α]

/-- Total variation distance between two probability measures, metric form.

Defined as the supremum of `|P(A).toReal - Q(A).toReal|` over measurable
sets `A`. -/
def tvDistReal (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] : ℝ :=
  sSup {x : ℝ | ∃ A : Set α, MeasurableSet A ∧ x = |(P A).toReal - (Q A).toReal|}

lemma tvDistReal_set_nonempty (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    {x : ℝ | ∃ A : Set α, MeasurableSet A ∧ x = |(P A).toReal - (Q A).toReal|}.Nonempty :=
  ⟨0, ∅, MeasurableSet.empty, by simp⟩

lemma tvDistReal_set_bddAbove (P Q : Measure α) [IsFiniteMeasure P] [IsFiniteMeasure Q] :
    BddAbove {x : ℝ | ∃ A : Set α, MeasurableSet A ∧ x = |(P A).toReal - (Q A).toReal|} := by
  refine ⟨(P univ).toReal + (Q univ).toReal, ?_⟩
  rintro x ⟨A, _, rfl⟩
  have h1 := ENNReal.toReal_nonneg (a := P A)
  have h2 := ENNReal.toReal_nonneg (a := Q A)
  have h3 := ENNReal.toReal_mono (measure_ne_top P _) (measure_mono (subset_univ A))
  have h4 := ENNReal.toReal_mono (measure_ne_top Q _) (measure_mono (subset_univ A))
  rw [abs_le]
  constructor <;> linarith

end MeasureTheory

end
