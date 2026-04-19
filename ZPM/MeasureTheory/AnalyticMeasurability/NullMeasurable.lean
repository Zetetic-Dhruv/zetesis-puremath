/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.MeasureTheory.ChoquetCapacity.AnalyticCompactCap
import Mathlib.MeasureTheory.Measure.NullMeasurable
import Mathlib.MeasureTheory.Measure.Real

/-!
# Analytic sets are NullMeasurableSet

Bridge from analytic sets to null-measurability via Choquet capacity theory.
One atomic concept: the AnalyticSet → NullMeasurableSet bridge, consisting
of an inner-approximation lemma and the main theorem.

## Main results

- `MeasureTheory.AnalyticSet.exists_isCompact_measureReal_gt`: inner
  approximation of analytic sets by compacts, in real-valued measure
- `MeasureTheory.AnalyticSet.nullMeasurableSet`: analytic sets are
  null-measurable for finite Borel measures on Polish spaces
-/

open MeasureTheory Set

/-- Inner regularity for analytic sets: any analytic subset of a Polish
space can be approximated from inside by a compact subset in measure, by
any slack `ε > 0`. Specialisation of Choquet capacitability (Kechris 30.13)
to the measure-as-capacity instance. -/
theorem MeasureTheory.AnalyticSet.exists_isCompact_measureReal_gt
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ μ.real s < μ.real K + ε := by
  intro ε hε
  have hcap := hs.compactCap_eq (μ := μ)
  have hfin : μ s ≠ ⊤ := measure_ne_top μ s
  have hε_ennreal : (0 : ENNReal) < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hε_ne_top : ENNReal.ofReal ε ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmem : ∃ r ∈ {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K},
      μ s < r + ENNReal.ofReal ε := by
    by_contra h
    push Not at h
    have hbound : sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} ≤ μ s - ENNReal.ofReal ε := by
      apply sSup_le
      intro r hr
      exact ENNReal.le_sub_of_add_le_right hε_ne_top (h r hr)
    have : MeasureTheory.compactCap μ s = sSup {r | ∃ K, IsCompact K ∧ K ⊆ s ∧ r = μ K} := rfl
    rw [← this, hcap] at hbound
    by_cases hμs : μ s = 0
    · have hmem : (0 : ENNReal) ∈ {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K} :=
        ⟨∅, isCompact_empty, Set.empty_subset _, by simp⟩
      have hle := h 0 hmem
      rw [hμs, zero_add] at hle
      exact absurd hle (not_le.mpr hε_ennreal)
    · exact absurd hbound (not_le.mpr (ENNReal.sub_lt_self hfin hμs hε_ennreal.ne'))
  obtain ⟨r, ⟨K, hKc, hKs, rfl⟩, hlt⟩ := hmem
  refine ⟨K, hKc, hKs, ?_⟩
  have hKfin : μ K ≠ ⊤ := ne_top_of_le_ne_top hfin (measure_mono hKs)
  have hadd_ne_top : μ K + ENNReal.ofReal ε ≠ ⊤ := by
    exact ENNReal.add_ne_top.mpr ⟨hKfin, hε_ne_top⟩
  rw [Measure.real, Measure.real]
  calc (μ s).toReal < (μ K + ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_lt_toReal hfin hadd_ne_top).mpr hlt
    _ = (μ K).toReal + ε := by
        rw [ENNReal.toReal_add hKfin hε_ne_top, ENNReal.toReal_ofReal hε.le]

/-- **Analytic sets are null-measurable.** For any finite Borel measure on
a Polish space, every analytic set is `NullMeasurableSet`. Proof inner-
approximates the analytic set by compacts, takes the union of approximators
(a Borel set), and shows the difference is contained in a Borel null set.

This is the abstract bridge that the entire Borel-analytic measurability
layer of downstream learning-theory kernels rests on. -/
theorem MeasureTheory.AnalyticSet.nullMeasurableSet
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    MeasureTheory.NullMeasurableSet s μ := by
  classical
  obtain ⟨t, hst, ht_meas, ht_eq⟩ := MeasureTheory.exists_measurable_superset μ s
  have hzero : μ (t \ s) = 0 := by
    by_contra hne
    have hfin_diff : μ (t \ s) ≠ ⊤ := measure_ne_top μ _
    have hpos : 0 < μ.real (t \ s) := ENNReal.toReal_pos hne hfin_diff
    obtain ⟨K, hKc, hKs, hKapprox⟩ :=
      hs.exists_isCompact_measureReal_gt (μ := μ) (μ.real (t \ s) / 2) (by positivity)
    have hKt : K ⊆ t := fun x hx => hst (hKs hx)
    have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
    have hdiff_eq : μ.real (t \ K) = μ.real t - μ.real K :=
      measureReal_diff hKt hKmeas
    have ht_real : μ.real t = μ.real s := by
      simp only [Measure.real]; rw [ht_eq]
    have hsub : t \ s ⊆ t \ K := Set.diff_subset_diff_right hKs
    have hle : μ.real (t \ s) ≤ μ.real (t \ K) :=
      measureReal_mono hsub
    linarith
  have h_ae : s =ᵐ[μ] t := by
    rw [Filter.eventuallyEq_comm, ae_eq_set]
    exact ⟨hzero, by simp [Set.diff_eq_empty.mpr hst]⟩
  exact ht_meas.nullMeasurableSet.congr h_ae.symm
