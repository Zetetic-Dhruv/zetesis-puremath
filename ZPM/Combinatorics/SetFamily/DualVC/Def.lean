/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Fintype.BigOperators

/-!
# Binary matrices: shattering, transpose, VC dimension

Basic definitions for `BinaryMatrix m n := Fin m → Fin n → Bool`:
the row-centric `shatters` predicate, transpose, the Finset-family view,
and VC dimension via Mathlib's `Finset.vcDim`.
-/

open Classical Finset

universe u

/-- An `m × n` binary matrix, represented as `Fin m → Fin n → Bool`. -/
abbrev BinaryMatrix (m n : ℕ) := Fin m → Fin n → Bool

namespace BinaryMatrix

/-- `M` shatters a column set `S` if every subset `t ⊆ S` arises as the set
of `true` columns within `S` for some row. -/
def shatters {m n : ℕ} (M : BinaryMatrix m n) (S : Finset (Fin n)) : Prop :=
  ∀ t ⊆ S, ∃ i : Fin m, ∀ j ∈ S, (M i j = true) ↔ (j ∈ t)

/-- Transpose of a binary matrix. -/
def transpose {m n : ℕ} (M : BinaryMatrix m n) : BinaryMatrix n m :=
  fun j i => M i j

/-- Convert a binary matrix to a Finset family: each row becomes the set of
columns where that row is `true`. -/
def toFinsetFamily {m n : ℕ} (M : BinaryMatrix m n) :
    Finset (Finset (Fin n)) :=
  Finset.univ.image (fun i : Fin m => Finset.univ.filter (fun j => M i j = true))

/-- The VC dimension of a binary matrix, defined via the Mathlib Finset family. -/
noncomputable def vcDim {m n : ℕ} (M : BinaryMatrix m n) : ℕ :=
  M.toFinsetFamily.vcDim

end BinaryMatrix
