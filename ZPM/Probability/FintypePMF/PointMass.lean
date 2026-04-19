/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Def

/-!
# FintypePMF.pointMass: Dirac point-mass PMF on a single element

Given a distinguished `a₀ : α`, `pointMass a₀` puts all the weight on `a₀`.
Used by the covering-row argument in `Probability/Decision/Minimax/`.
-/

namespace ProbabilityTheory.FintypePMF

open Finset

/-- Point-mass `FintypePMF` at a fixed element `a₀`. -/
def pointMass {α : Type*} [Fintype α] [DecidableEq α] (a₀ : α) :
    FintypePMF α where
  prob a := if a = a₀ then 1 else 0
  prob_nonneg a := by split_ifs <;> norm_num
  prob_sum_one := by simp [sum_ite_eq']

end ProbabilityTheory.FintypePMF
