/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Decision.Minimax.MWU.EmpiricalPayoff
import ZPM.Probability.Decision.Minimax.MWU.HitRate

/-!
# MWU approximate minimax: headline theorem

The full MWU-based approximate minimax theorem: if every column mixture
admits a pure row with expected payoff at least `v`, then some row mixture
achieves payoff at least `v - ε` against every pure column.

Chooses `η = ε / 4` and `T = max 1 ⌈16 log N / ε²⌉` so that the potential
bound, the hit-rate-from-potential lemma, and the feasibility conditions
combine into the per-column guarantee.
-/

noncomputable section

namespace ProbabilityTheory

open Finset FintypePMF

/-- **MWU approximate minimax.** If every column mixture admits a pure row with expected
payoff at least `v`, then some row mixture achieves payoff at least `v - ε` against every
pure column. -/
theorem mwu_approx_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty R] [Nonempty C]
    [DecidableEq R] [DecidableEq C]
    (M : R → C → Bool) (v ε : ℝ) (hε : 0 < ε)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FintypePMF R, ∀ c : C, v - ε ≤ boolGamePayoff M p c := by
  by_cases htriv : v ≤ ε
  · exact ⟨FintypePMF.uniform R, fun c =>
      le_trans (sub_nonpos.mpr htriv) (boolGamePayoff_nonneg M _ c)⟩
  have hεv : ε < v := lt_of_not_ge htriv
  have hv : 0 < v := lt_trans hε hεv
  have hv1 : v ≤ 1 := minimax_value_le_one M v hrow
  let η : ℝ := ε / 4
  have hη : 0 < η := by positivity
  have hη1 : η < 1 := by dsimp [η]; linarith
  let N : ℕ := Fintype.card C
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast @Fintype.card_pos C _ _
  let T : ℕ := max 1 (Nat.ceil (16 * Real.log (N : ℝ) / ε ^ 2))
  have hTpos : 0 < T := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
  have hTlarge0 : 16 * Real.log (N : ℝ) / ε ^ 2 ≤ (T : ℝ) := by
    refine le_trans (Nat.le_ceil _) ?_
    exact_mod_cast Nat.le_max_right 1 _
  have hlargeT : Real.log (N : ℝ) / (η * T) ≤ ε / 4 := by
    have hηTpos : 0 < η * (T : ℝ) := by positivity
    apply (div_le_iff₀ hηTpos).2
    have hε2pos : 0 < ε ^ 2 := by positivity
    have htmp : 16 * Real.log (N : ℝ) ≤ (T : ℝ) * ε ^ 2 := (div_le_iff₀ hε2pos).mp hTlarge0
    dsimp [η]; nlinarith
  let rows := mwuRows M η hη1 v hrow T
  let p := FintypePMF.empirical hTpos rows
  refine ⟨p, fun c => ?_⟩
  have hpot :
      (1 - η) ^ (mwuHitCount M η hη1 v hrow T c) ≤
        (N : ℝ) * (1 - η * v) ^ T := by
    calc (1 - η) ^ (mwuHitCount M η hη1 v hrow T c)
        = (mwuConfig M η hη1 v hrow T).weights c :=
            (mwu_weight_eq_pow_hitCount M η hη1 v hrow T c).symm
      _ ≤ (mwuConfig M η hη1 v hrow T).potential := weight_le_potential _ c
      _ ≤ (N : ℝ) * (1 - η * v) ^ T := mwu_potential_T_bound M η (le_of_lt hη) hη1 v hrow T
  rw [boolGamePayoff_empirical_eq_hitCount M η hη1 v hrow hTpos c]
  exact hitRate_from_potential hNpos hη hη1 hv1 hTpos hpot (by dsimp [η]; linarith) hlargeT

end ProbabilityTheory

end
