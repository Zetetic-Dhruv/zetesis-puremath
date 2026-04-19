/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Fintype.BigOperators

/-!
# VC dimension of a finite `Bool`-valued function family

Every finite family of `Bool`-valued functions `A : Finset (α → Bool)`
determines a Finset family of accepting sets, one per function. The VC
dimension of the function family is then defined as the `Finset.vcDim`
of its accepting-set image. This is the entry point from function-class
view to Mathlib's combinatorial VC machinery.
-/

open Classical Finset

/-- Accepting-set image: map each `Bool`-valued function to its accepting set
`{h | f h = true}`. -/
def Finset.boolFamilyToFinsetFamily {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset (α → Bool)) : Finset (Finset α) :=
  A.image (fun f => Finset.univ.filter (fun h => f h = true))

/-- VC dimension of a finite `Bool`-valued family, computed via the accepting-set
image and Mathlib's `Finset.vcDim`. -/
noncomputable def Finset.boolVCDim {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset (α → Bool)) : ℕ :=
  (Finset.boolFamilyToFinsetFamily A).vcDim
