/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.MeasureTheory.ChoquetCapacity.Def
import ZPM.MeasureTheory.ChoquetCapacity.Capacitability

/-!
# Analytic sets: compact capacity equals measure

Headline corollary of Choquet capacitability. For any finite Borel measure on
a Polish space and any analytic `s`, `compactCap μ s = μ s`.
-/

open MeasureTheory Set

private lemma compactCap_eq_iSup_isCompact
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (s : Set α) :
    MeasureTheory.compactCap μ s =
      ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), μ K := by
  unfold MeasureTheory.compactCap
  apply le_antisymm
  · apply sSup_le
    rintro r ⟨K, hKc, hKs, rfl⟩
    exact le_iSup_of_le K (le_iSup_of_le hKc (le_iSup_of_le hKs le_rfl))
  · apply iSup_le; intro K
    apply iSup_le; intro hKc
    apply iSup_le; intro hKs
    apply le_csSup
    · exact ⟨μ Set.univ, fun _ ⟨_, _, _, hr⟩ => hr ▸ measure_mono (Set.subset_univ _)⟩
    · exact ⟨K, hKc, hKs, rfl⟩

/-- For analytic sets, compact capacity equals measure. -/
theorem MeasureTheory.AnalyticSet.compactCap_eq
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    MeasureTheory.compactCap μ s = μ s := by
  rw [compactCap_eq_iSup_isCompact]
  exact (hs.cap_eq_iSup_isCompact (measure_isChoquetCapacity μ)).symm
