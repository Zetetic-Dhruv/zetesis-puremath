/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Expectation
import ZPM.Probability.FintypePMF.TVDistance

/-!
# TV-based transfer principle for `Bool`-valued tests

If `tvDistance p q ≤ δ`, then for every `Bool`-valued test `f`,
`|E_p[f] - E_q[f]| ≤ δ`. A single TV bound therefore implies uniform
test-expectation approximation across any finite family of tests without
a union bound. This is the mechanism that lets a compression argument
swap a target distribution for an empirical one.
-/

noncomputable section

namespace ProbabilityTheory.FintypePMF

open Finset

/-- **Transfer principle.** If `tvDistance p q ≤ δ`, then for every `Bool`-valued test
`f`, the expectations under `p` and `q` differ by at most `δ`. -/
theorem expectation_approx_of_tv {α : Type*} [Fintype α]
    (p q : FintypePMF α) (f : α → Bool) (δ : ℝ)
    (hδ : tvDistance p q ≤ δ) :
    |boolTestExpectation p f - boolTestExpectation q f| ≤ δ := by
  simp only [boolTestExpectation, trueExpectation]
  calc |∑ a : α, p.prob a * (if f a then (1 : ℝ) else 0) -
        ∑ a : α, q.prob a * (if f a then (1 : ℝ) else 0)|
      = |∑ a : α, (p.prob a - q.prob a) *
          (if f a then (1 : ℝ) else 0)| := by
        congr 1
        simp_rw [sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ a : α, |(p.prob a - q.prob a) *
          (if f a then (1 : ℝ) else 0)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : α, |p.prob a - q.prob a| := by
        apply Finset.sum_le_sum; intro a _
        rw [abs_mul]
        calc |p.prob a - q.prob a| * |if f a then (1 : ℝ) else 0|
            ≤ |p.prob a - q.prob a| * 1 := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              split_ifs <;> simp [abs_of_nonneg]
          _ = |p.prob a - q.prob a| := mul_one _
    _ = tvDistance p q := rfl
    _ ≤ δ := hδ

/-- Uniform version of `expectation_approx_of_tv`: a single TV bound suffices for
every test in any finite family simultaneously, with no union bound. -/
theorem tv_bound_implies_all_tests {α : Type*} [Fintype α]
    (p q : FintypePMF α) (ε : ℝ)
    (hε : tvDistance p q ≤ ε)
    (tests : Finset (α → Bool)) :
    ∀ f ∈ tests, |boolTestExpectation p f - boolTestExpectation q f| ≤ ε :=
  fun f _ => expectation_approx_of_tv p q f ε hε

end ProbabilityTheory.FintypePMF

end
