/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Empirical

/-!
# Expectations under a FintypePMF

`trueExpectation` is the expectation of an ℝ-valued function under a
`FintypePMF`; `boolTestExpectation` is the specialisation to indicator
(`Bool`-valued) tests via the embedding `if · then 1 else 0`. The indicator
form is `[0, 1]`-bounded and evaluates to the sample-average on an
empirical PMF; these are the bricks used by the TV-based transfer
principle in the next shard.
-/

noncomputable section

namespace ProbabilityTheory.FintypePMF

open Finset

/-- Expected value `∑ h, p.prob h * f h` of a real-valued test under a `FintypePMF`. -/
def trueExpectation {α : Type*} [Fintype α]
    (p : FintypePMF α) (f : α → ℝ) : ℝ :=
  ∑ a : α, p.prob a * f a

/-- Expected value of a `Bool`-valued test under a `FintypePMF` via the indicator
embedding `if f a then 1 else 0`. -/
def boolTestExpectation {α : Type*} [Fintype α]
    (p : FintypePMF α) (f : α → Bool) : ℝ :=
  trueExpectation p (fun a => if f a then (1 : ℝ) else 0)

lemma boolTestExpectation_nonneg {α : Type*} [Fintype α]
    (p : FintypePMF α) (f : α → Bool) :
    0 ≤ boolTestExpectation p f :=
  Finset.sum_nonneg fun a _ =>
    mul_nonneg (p.prob_nonneg a) (by simp only; split_ifs <;> norm_num)

lemma boolTestExpectation_le_one {α : Type*} [Fintype α]
    (p : FintypePMF α) (f : α → Bool) :
    boolTestExpectation p f ≤ 1 := by
  simp only [boolTestExpectation, trueExpectation]
  calc ∑ a : α, p.prob a * (if f a then (1 : ℝ) else 0)
      ≤ ∑ a : α, p.prob a := Finset.sum_le_sum fun a _ =>
        mul_le_of_le_one_right (p.prob_nonneg a) (by split_ifs <;> norm_num)
    _ = 1 := p.prob_sum_one

/-- Expectation of a `Bool`-valued test under an empirical `FintypePMF` equals the
sample average along the underlying sequence. Bridges the distributional view to the
sample-average view used by the MWU argument. -/
lemma boolTestExpectation_empirical_eq_avg
    {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℕ} (hT : 0 < T) (rs : Fin T → α) (f : α → Bool) :
    boolTestExpectation (empirical hT rs) f =
    (∑ t : Fin T, if f (rs t) then (1 : ℝ) else 0) / T := by
  simp only [boolTestExpectation, trueExpectation, empirical]
  conv_lhs => arg 2; ext a; rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  symm
  have := Finset.card_eq_sum_card_fiberwise (f := rs)
    (s := univ) (t := univ) (fun _ _ => Finset.mem_univ _)
  conv_lhs => rw [show (∑ t : Fin T, if f (rs t) then (1 : ℝ) else 0) =
    ∑ a : α, ∑ t ∈ univ.filter (fun t => rs t = a),
      (if f (rs t) then (1 : ℝ) else 0) from by
    rw [← Finset.sum_biUnion (s := univ)]
    · congr 1; ext t; simp
    · intro a₁ _ a₂ _ hne
      simp only [Function.onFun]
      rw [Finset.disjoint_filter]
      intro t _ ht1 ht2; exact hne (ht1.symm.trans ht2)]
  congr 1; ext a
  rw [Finset.sum_congr rfl (fun t ht => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht
    rw [ht])]
  rw [Finset.sum_const, nsmul_eq_mul]

end ProbabilityTheory.FintypePMF

end
