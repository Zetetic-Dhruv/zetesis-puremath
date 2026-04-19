/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Exchangeability.DoubleSample
import ZPM.Probability.Exchangeability.ValidSplit
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# SplitMeasure: uniform measure on valid splits, with first/second projections

Conditioning a `D^{2m}` sample on the merged sample `z` and averaging over
all `ValidSplit m` outcomes recovers `D^m ⊗ D^m`, because `D^{2m}` is
invariant under coordinate permutations. `SplitMeasure m` assigns weight
`1 / C(2m, m)` to each valid split.
-/

universe u

open MeasureTheory ENNReal ProbabilityTheory

/-- Uniform measure over all valid splits of `2m` into two groups of `m`.

The core construction for the exchangeability argument: with weight
`1 / Fintype.card (ValidSplit m)` on each split, the Dirac sum gives a
probability measure on the finite, discrete space `ValidSplit m`. -/
noncomputable def ProbabilityTheory.SplitMeasure (m : ℕ) :
    MeasureTheory.Measure (ProbabilityTheory.ValidSplit m) :=
  if _h : Fintype.card (ProbabilityTheory.ValidSplit m) = 0 then 0
  else (Fintype.card (ProbabilityTheory.ValidSplit m) : ENNReal)⁻¹ •
    ∑ vs : ProbabilityTheory.ValidSplit m, MeasureTheory.Measure.dirac vs

/-- First-group projection of a merged sample under a valid split. -/
def ProbabilityTheory.splitFirst {X : Type u} {m : ℕ}
    (z : ProbabilityTheory.MergedSample X m) (_vs : ProbabilityTheory.ValidSplit m) :
    Fin m → X := by
  exact fun i => z (Fin.castAdd m i |>.cast (two_mul m).symm)

/-- Second-group projection of a merged sample under a valid split. -/
def ProbabilityTheory.splitSecond {X : Type u} {m : ℕ}
    (z : ProbabilityTheory.MergedSample X m) (_vs : ProbabilityTheory.ValidSplit m) :
    Fin m → X := by
  exact fun i => z (Fin.natAdd m i |>.cast (two_mul m).symm)
