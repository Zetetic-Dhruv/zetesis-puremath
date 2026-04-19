/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Basic

/-!
# MWU configuration state

`MWUConfig C` carries a strictly-positive weight vector and its potential
(the sum of the weights). The initial state sets all weights to `1`;
`toPMF` normalizes the weights to a `FintypePMF` distribution. These are
the structural primitives consumed by the multiplicative-weights update
and analysis in later shards.
-/

noncomputable section

namespace ProbabilityTheory

open Finset FintypePMF

/-- Multiplicative-weights-update state: a strictly-positive weight vector. -/
structure MWUConfig (C : Type*) [Fintype C] where
  /-- The weight assigned to each column. -/
  weights : C → ℝ
  /-- Weights are strictly positive. -/
  weights_pos : ∀ c, 0 < weights c

/-- The potential of an MWU state is the sum of its weights. -/
def MWUConfig.potential {C : Type*} [Fintype C] (cfg : MWUConfig C) : ℝ :=
  ∑ c : C, cfg.weights c

lemma MWUConfig.potential_pos {C : Type*} [Fintype C] [Nonempty C]
    (cfg : MWUConfig C) : 0 < cfg.potential :=
  Finset.sum_pos (fun c _ => cfg.weights_pos c) univ_nonempty

/-- Initial configuration: all weights equal to `1`. -/
def mwuInit (C : Type*) [Fintype C] : MWUConfig C where
  weights := fun _ => 1
  weights_pos := fun _ => one_pos

lemma mwuInit_potential (C : Type*) [Fintype C] :
    (mwuInit C).potential = Fintype.card C := by
  simp [MWUConfig.potential, mwuInit, sum_const, nsmul_eq_mul, mul_one]

/-- Normalize an MWU configuration to a `FintypePMF`. -/
def MWUConfig.toPMF {C : Type*} [Fintype C] [Nonempty C]
    (cfg : MWUConfig C) : FintypePMF C :=
  FintypePMF.normalize cfg.weights cfg.weights_pos

end ProbabilityTheory

end
