/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Choquet capacity: definition and instance on finite Borel measures

Defines the compact capacity functional and the bundled `IsChoquetCapacity`
structure. Proves that every finite Borel measure on a Polish space is a
Choquet capacity.
-/

universe u

open MeasureTheory Set Filter Topology

/-- Compact capacity of a set `s` relative to a measure `μ`: the supremum of
`μ K` over compact subsets `K ⊆ s`. The inner-regularity functional whose
equality with `μ s` characterises measurability for analytic sets. -/
noncomputable def MeasureTheory.compactCap
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (s : Set α) : ENNReal :=
  sSup {r : ENNReal | ∃ K : Set α, IsCompact K ∧ K ⊆ s ∧ r = μ K}

/-- Compact capacity is monotone in its set argument. -/
theorem MeasureTheory.compactCap_mono
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {s t : Set α} (hst : s ⊆ t) :
    MeasureTheory.compactCap μ s ≤ MeasureTheory.compactCap μ t := by
  apply sSup_le_sSup
  rintro r ⟨K, hKc, hKs, rfl⟩
  exact ⟨K, hKc, hKs.trans hst, rfl⟩

/-- Bundled record of the three Choquet capacity axioms: monotonicity,
sequential continuity from below along increasing unions, and sequential
continuity from above along decreasing intersections of *closed* sets.
The third axiom distinguishes a capacity from a general outer measure. -/
structure MeasureTheory.IsChoquetCapacity
    {α : Type*} [TopologicalSpace α]
    (cap : Set α → ENNReal) : Prop where
  mono : ∀ {s t : Set α}, s ⊆ t → cap s ≤ cap t
  iUnion_nat : ∀ (f : ℕ → Set α), Monotone f →
    cap (⋃ n, f n) = ⨆ n, cap (f n)
  iInter_closed : ∀ (f : ℕ → Set α), Antitone f →
    (∀ n, IsClosed (f n)) →
    cap (⋂ n, f n) = ⨅ n, cap (f n)

/-- Every finite Borel measure on a Polish space is a Choquet capacity. -/
theorem MeasureTheory.measure_isChoquetCapacity
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    (μ : MeasureTheory.Measure α) [MeasureTheory.IsFiniteMeasure μ] :
    MeasureTheory.IsChoquetCapacity (fun s : Set α => μ s) := by
  constructor
  · intro s t hst; exact measure_mono hst
  · intro f hf; exact hf.measure_iUnion
  · intro f hf hclosed
    exact hf.measure_iInter
      (fun n => (hclosed n).measurableSet.nullMeasurableSet)
      ⟨0, measure_ne_top μ (f 0)⟩
