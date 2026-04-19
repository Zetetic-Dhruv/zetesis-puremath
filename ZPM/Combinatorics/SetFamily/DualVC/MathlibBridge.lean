/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Combinatorics.SetFamily.DualVC.Def

/-!
# Bridge to Mathlib's `Finset.Shatters`

Equates `BinaryMatrix.shatters` with Mathlib's `Finset.Shatters` via the
associated `toFinsetFamily` construction, plus an auxiliary uniqueness
lemma for Bool-valued functions on `Fin n` matched by their `true`-filter.
-/

open Classical Finset

namespace BinaryMatrix

/-- `shatters` coincides with Mathlib's `Finset.Shatters` on the associated
Finset family. -/
theorem shatters_iff {m n : ℕ} (M : BinaryMatrix m n) (S : Finset (Fin n)) :
    M.shatters S ↔ M.toFinsetFamily.Shatters S := by
  constructor
  · intro hM t ht
    obtain ⟨i, hi⟩ := hM t ht
    refine ⟨Finset.univ.filter (fun j => M i j = true), ?_, ?_⟩
    · simp only [toFinsetFamily, mem_image, mem_univ, true_and]
      exact ⟨i, rfl⟩
    · ext j
      simp only [mem_inter, mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨hj, hMij⟩
        exact (hi j hj).mp hMij
      · intro hjt
        have hjS := ht hjt
        exact ⟨hjS, (hi j hjS).mpr hjt⟩
  · intro hS t ht
    obtain ⟨u, hu, hut⟩ := hS ht
    simp only [toFinsetFamily, mem_image, mem_univ, true_and] at hu
    obtain ⟨i, rfl⟩ := hu
    refine ⟨i, fun j hj => ?_⟩
    constructor
    · intro hMij
      have : j ∈ S ∩ Finset.univ.filter (fun j => M i j = true) := by
        simp only [mem_inter, mem_filter, mem_univ, true_and]
        exact ⟨hj, hMij⟩
      rw [hut] at this
      exact this
    · intro hjt
      have : j ∈ S ∩ Finset.univ.filter (fun j => M i j = true) := by
        rw [hut]; exact hjt
      simp only [mem_inter, mem_filter, mem_univ, true_and] at this
      exact this.2

/-- Two Bool-valued functions on `Fin n` are equal if they have the same
`univ.filter`-set of true indices. -/
theorem bool_fun_eq_of_filter_eq {n : ℕ} (f g : Fin n → Bool)
    (h : Finset.univ.filter (fun j => f j = true) =
         Finset.univ.filter (fun j => g j = true)) :
    f = g := by
  funext j
  by_cases hf : f j = true <;> by_cases hg : g j = true
  · rw [hf, hg]
  · exfalso
    have : j ∈ Finset.univ.filter (fun j => f j = true) := by
      simp [hf]
    rw [h] at this
    simp [hg] at this
  · exfalso
    have : j ∈ Finset.univ.filter (fun j => g j = true) := by
      simp [hg]
    rw [← h] at this
    simp [hf] at this
  · simp only [Bool.not_eq_true] at hf hg
    rw [hf, hg]

end BinaryMatrix
