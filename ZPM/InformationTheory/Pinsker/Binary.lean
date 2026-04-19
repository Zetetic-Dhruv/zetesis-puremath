/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.InformationTheory.KullbackLeibler.Binary.Basic

/-!
# Binary Pinsker inequality

`2 (p − q)² ≤ klBin p q` for `p ∈ [0, 1]` and `q ∈ (0, 1)`. Case-splits on
`p = 0`, `p = 1`, and `p ∈ (0, 1)`, with the middle case further reducing
to monotonicity of `g` on the appropriate half-interval around `p`.
-/

namespace InformationTheory

open Set

/-- **Binary Pinsker inequality.** `2 (p − q)² ≤ klBin p q` for `p ∈ [0, 1]`,
`q ∈ (0, 1)`. Sharp constant `2`. -/
theorem binary_pinsker (p q : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    2 * (p - q)^2 ≤ klBin p q := by
  suffices hg : 0 ≤ klBin p q - 2 * (p - q)^2 by linarith
  rcases eq_or_lt_of_le hp₀ with hp_eq | hp_pos
  · rw [← hp_eq]
    rw [klBin_zero_left q]
    have h := two_sq_le_neg_log_one_sub q hq₀.le hq₁
    have h_sq : (0 - q)^2 = q^2 := by ring
    rw [h_sq]
    linarith
  rcases eq_or_lt_of_le hp₁ with hp_eq | hp_lt
  · rw [hp_eq]
    rw [klBin_one_left q]
    have h := two_sq_le_neg_log q hq₀ hq₁.le
    have h_sq : (1 - q)^2 = (1 - q)^2 := rfl
    linarith
  rcases le_or_gt p q with hpq | hpq
  · have hmono := monotoneOn_g p hp_pos hp_lt
    have hp_mem : p ∈ Set.Ico p 1 := ⟨le_refl p, hp_lt⟩
    have hq_mem : q ∈ Set.Ico p 1 := ⟨hpq, hq₁⟩
    have h_ge := hmono hp_mem hq_mem hpq
    have h_self : klBin p p - 2 * (p - p)^2 = 0 := by
      rw [klBin_self p hp_pos hp_lt]; ring
    linarith
  · have hanti := antitoneOn_g p hp_pos hp_lt
    have hp_mem : p ∈ Set.Ioc 0 p := ⟨hp_pos, le_refl p⟩
    have hq_mem : q ∈ Set.Ioc 0 p := ⟨hq₀, hpq.le⟩
    have h_ge := hanti hq_mem hp_mem hpq.le
    have h_self : klBin p p - 2 * (p - p)^2 = 0 := by
      rw [klBin_self p hp_pos hp_lt]; ring
    linarith

end InformationTheory
