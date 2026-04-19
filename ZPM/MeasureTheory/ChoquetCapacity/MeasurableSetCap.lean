/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.MeasureTheory.ChoquetCapacity.Def

/-!
# Compact capacity equals measure on measurable sets

The easy half of the Choquet capacitability statement: for Borel-measurable
sets `s`, `compactCap μ s = μ s`. The analytic-set half requires the
cylinder machinery and lives in `AnalyticCompactCap.lean`.
-/

open MeasureTheory Set

/-- For Borel-measurable sets, compact capacity equals measure. Two-sided
bound via monotonicity and Mathlib's `MeasurableSet.exists_isCompact_lt_add`. -/
theorem MeasureTheory.MeasurableSet.compactCap_eq
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasurableSet s) :
    MeasureTheory.compactCap μ s = μ s := by
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨K, _, hKs, rfl⟩
    exact measure_mono hKs
  · show μ s ≤ MeasureTheory.compactCap μ s
    unfold MeasureTheory.compactCap
    have hbdd : BddAbove {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K} :=
      ⟨μ Set.univ, fun _ ⟨_, _, hLs, hr⟩ => hr ▸ measure_mono (hLs.trans (Set.subset_univ _))⟩
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hε_ne : (ε : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hε.ne'
    obtain ⟨K, hKs, hKc, hlt⟩ := hs.exists_isCompact_lt_add (measure_ne_top μ s) hε_ne
    calc μ s ≤ μ K + ε := le_of_lt hlt
      _ ≤ sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} + ε := by
        gcongr
        exact le_csSup hbdd ⟨K, hKc, hKs, rfl⟩
