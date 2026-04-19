/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Double-sample measure and merge/split isomorphism

Core constructions for the symmetrization / exchangeability pipeline:
an `ExchangeableSample` bundle, the `DoubleSampleMeasure` product, the
`MergedSample` abbrev on `Fin (2*m) → X`, and the `mergeSamples` /
`splitMergedSample` isomorphism between `(Fin m → X) × (Fin m → X)` and
`Fin (2*m) → X`.
-/

universe u

open MeasureTheory ENNReal

/-- Bundle: sample size, measure, and probability-measure proof. -/
structure ProbabilityTheory.ExchangeableSample {X : Type*} [MeasurableSpace X] where
  m : ℕ
  μ : MeasureTheory.Measure X
  hμ : MeasureTheory.IsProbabilityMeasure μ

/-- The double sample measure `D^m ⊗ D^m`: the product of two independent
`m`-fold product measures. Joint distribution of training + ghost samples. -/
noncomputable def ProbabilityTheory.DoubleSampleMeasure
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) (m : ℕ) :
    MeasureTheory.Measure ((Fin m → X) × (Fin m → X)) :=
  (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
    (MeasureTheory.Measure.pi (fun _ : Fin m => D))

/-- Type alias for a merged sample of `2m` points from `X`. -/
abbrev ProbabilityTheory.MergedSample (X : Type u) (m : ℕ) := Fin (2 * m) → X

/-- Merge two samples of size `m` into a single sample of size `2m`. -/
noncomputable def ProbabilityTheory.mergeSamples {X : Type u} {m : ℕ}
    (p : (Fin m → X) × (Fin m → X)) : ProbabilityTheory.MergedSample X m :=
  fun i =>
    let j : Fin (m + m) := i.cast (two_mul m)
    if h : j.val < m
    then p.1 ⟨j.val, h⟩
    else p.2 ⟨j.val - m, by omega⟩

/-- Split a merged sample of `2m` points back into two samples of size `m`.
Inverse of `mergeSamples`. -/
noncomputable def ProbabilityTheory.splitMergedSample {X : Type u} {m : ℕ}
    (z : ProbabilityTheory.MergedSample X m) : (Fin m → X) × (Fin m → X) :=
  (fun i => z (Fin.castAdd m i |>.cast (two_mul m).symm),
   fun i => z (Fin.natAdd m i |>.cast (two_mul m).symm))
