/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# ValidSplit: combinatorial splits of 2m into two groups of m

A `ValidSplit m` is an assignment of each of `2m` indices to one of two
groups, with exactly `m` indices assigned to the first group. The type has
cardinality `Nat.choose (2 * m) m` and comes equipped with `Fintype` and
(discrete) `MeasurableSpace` instances.
-/

/-- A split of a `2m`-element set into two groups of `m`. -/
structure ProbabilityTheory.ValidSplit (m : ℕ) where
  /-- Assignment of each of `2 * m` indices to one of two groups. -/
  assign : Fin (2 * m) → Bool
  /-- Exactly `m` indices are assigned to the first group. -/
  card_true : (Finset.univ.filter (fun i => assign i = true)).card = m
  deriving DecidableEq

/-- `ValidSplit m` is finite: a subtype of the finite type `Fin (2*m) → Bool`. -/
noncomputable instance (m : ℕ) : Fintype (ProbabilityTheory.ValidSplit m) :=
  Fintype.ofInjective (fun vs => vs.assign)
    (fun a b h => by cases a; cases b; simp_all)

/-- Discrete measurable space on `ValidSplit m` (all sets measurable). -/
instance (m : ℕ) : MeasurableSpace (ProbabilityTheory.ValidSplit m) := ⊤
