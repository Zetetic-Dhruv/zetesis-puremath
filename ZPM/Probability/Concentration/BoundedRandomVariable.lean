/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bounded random variables

A typeclass for random variables `f : Ω → ℝ` bounded in `[a, b]` almost
everywhere under a measure `μ`, plus measurability of `f`.
-/

open MeasureTheory

/-- A random variable `f : Ω → ℝ` is bounded in `[a, b]` almost everywhere
under `μ`, with `f` itself measurable. -/
class ProbabilityTheory.BoundedRandomVariable
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (a b : ℝ) : Prop where
  ae_mem_Icc : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc a b
  measurable : Measurable f
