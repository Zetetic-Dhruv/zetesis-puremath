/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Decision.Minimax.MWU.Update

/-!
# Running MWU for T rounds and the T-step potential bound

`mwuRun` iterates `mwuUpdateWeights` for `T` rounds, threading the
best-response selector produced by the `hrow` hypothesis. The T-step
potential bound `Φ_T ≤ |C| · (1 - η · v)^T` follows by induction from
the one-step bound.
-/

noncomputable section

namespace ProbabilityTheory

open Finset FintypePMF

/-- Run MWU for `T` rounds: returns the final configuration and the row sequence. -/
def mwuRun {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    (T : ℕ) → MWUConfig C × (Fin T → R)
  | 0 => (mwuInit C, Fin.elim0)
  | T + 1 =>
    let ⟨cfg, rows⟩ := mwuRun M η hη1 v hrow T
    let r := (hrow cfg.toPMF).choose
    (mwuUpdateWeights M η hη1 cfg r, Fin.snoc rows r)

/-- The MWU configuration after `T` rounds. -/
abbrev mwuConfig {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) : MWUConfig C :=
  (mwuRun M η hη1 v hrow T).1

/-- The MWU row sequence after `T` rounds. -/
abbrev mwuRows {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) : Fin T → R :=
  (mwuRun M η hη1 v hrow T).2

/-- **T-step MWU potential bound**: after `T` rounds, `Φ_T ≤ |C| · (1 - η · v)^T`. -/
theorem mwu_potential_T_bound
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη : 0 ≤ η) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) :
    (mwuConfig M η hη1 v hrow T).potential ≤
    Fintype.card C * (1 - η * v) ^ T := by
  induction T with
  | zero =>
    simp only [mwuConfig, mwuRun, mwuInit_potential, pow_zero, mul_one, le_refl]
  | succ T ih =>
    simp only [mwuConfig, mwuRun] at ih ⊢
    set run_T := mwuRun M η hη1 v hrow T
    set cfg_T := run_T.1
    set r := (hrow cfg_T.toPMF).choose
    have hstep := potential_one_step_bound M η hη hη1 v hrow cfg_T
    simp only [cfg_T] at hstep
    have hv1 : v ≤ 1 := minimax_value_le_one M v hrow
    have h1ηv : 0 ≤ 1 - η * v := by nlinarith [mul_le_of_le_one_left hη hv1]
    calc (mwuUpdateWeights M η hη1 cfg_T
            ((hrow cfg_T.toPMF).choose)).potential
        ≤ cfg_T.potential * (1 - η * v) := hstep
      _ ≤ (↑(Fintype.card C) * (1 - η * v) ^ T) * (1 - η * v) :=
          mul_le_mul_of_nonneg_right ih h1ηv
      _ = ↑(Fintype.card C) * (1 - η * v) ^ (T + 1) := by ring

end ProbabilityTheory

end
