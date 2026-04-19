/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.Decision.Minimax.CoveringRow

/-!
# Covering-based minimax

From the covering-row lemma, construct a row distribution whose payoff is
at least `1 / |C|` against every column.
-/

noncomputable section

namespace ProbabilityTheory

open Finset FintypePMF

/-- **Covering-based minimax**: if the minimax value is strictly positive, there is a row
distribution whose payoff against every column is at least `1 / |C|`. -/
theorem covering_minimax
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    [DecidableEq R] [DecidableEq C]
    (M : R → C → Bool) (v : ℝ) (hv : 0 < v)
    (hrow : ∀ q : FintypePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FintypePMF R, ∀ c : C,
      (1 : ℝ) / Fintype.card C ≤ boolGamePayoff M p c := by
  have hcover := exists_covering_row M v hv hrow
  choose r_c hr_c using hcover
  let n := Fintype.card C
  have hn : 0 < n := Fintype.card_pos
  let eC := (Fintype.equivFin C).symm
  let rs : Fin n → R := fun i => r_c (eC i)
  refine ⟨FintypePMF.empirical hn rs, fun c₀ => ?_⟩
  simp only [boolGamePayoff]
  let i₀ : Fin n := (Fintype.equivFin C) c₀
  have hrs_i₀ : rs i₀ = r_c c₀ := by
    simp only [rs, eC, i₀, Equiv.symm_apply_apply]
  calc (1 : ℝ) / n
      = (1 : ℝ) / n * 1 := (mul_one _).symm
    _ ≤ (FintypePMF.empirical hn rs).prob (r_c c₀) * (if M (r_c c₀) c₀ then 1 else 0) := by
        simp only [hr_c c₀]
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        simp only [FintypePMF.empirical]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        rw [Nat.one_le_cast]
        apply Finset.card_pos.mpr
        exact ⟨i₀, by simp [hrs_i₀]⟩
    _ ≤ ∑ r : R, (FintypePMF.empirical hn rs).prob r * (if M r c₀ then 1 else 0) := by
        apply Finset.single_le_sum (f := fun r =>
          (FintypePMF.empirical hn rs).prob r * (if M r c₀ then (1 : ℝ) else 0))
        · intro r _
          exact mul_nonneg ((FintypePMF.empirical hn rs).prob_nonneg r) (by split_ifs <;> norm_num)
        · exact mem_univ _

end ProbabilityTheory

end
