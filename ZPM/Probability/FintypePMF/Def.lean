/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# FintypePMF: an ℝ-valued, Fintype-indexed probability mass function

`ProbabilityTheory.FintypePMF α` is a probability mass function over a
finite type `α`, with `ℝ`-valued weights and the summation axiom phrased
via `Finset.sum`. It coexists with `Mathlib.PMF α` rather than duplicates
it: the `ℝ`-valued / `Finset.sum`-based encoding is what lets
`linarith` / `nlinarith` / `field_simp` compose in arithmetic-heavy
proofs (for example the multiplicative-weights-update analysis), where
the `ℝ≥0∞`-valued Mathlib `PMF` would require `toReal` round-trips at
every step.

The precedent for this coexistence is documented in the repository
`CHARTER.md` under "Duplicate rule exception: proof-engineering
specializations."
-/

/-- An ℝ-valued probability mass function over a finite type.

Fields:
- `prob`: the weight assigned to each element.
- `prob_nonneg`: weights are non-negative.
- `prob_sum_one`: weights sum to 1.
-/
structure ProbabilityTheory.FintypePMF (α : Type*) [Fintype α] where
  /-- Probability weight assigned to each element. -/
  prob : α → ℝ
  /-- Weights are non-negative. -/
  prob_nonneg : ∀ a, 0 ≤ prob a
  /-- Weights sum to 1. -/
  prob_sum_one : ∑ a : α, prob a = 1
