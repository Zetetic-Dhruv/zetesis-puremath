/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Combinatorics.SetFamily.DualVC.MathlibBridge
import ZPM.Combinatorics.SetFamily.DualVC.FinsetDual

/-!
# Bitstring coding: transpose-shattering implies column-shattering (matrix corollary)

Assouad's dual technique, stated in matrix form. This is now a corollary of
`Finset.dualFamily_shatters_imp_shatters` via `toFinsetFamily`.
-/

open Classical Finset

namespace BinaryMatrix

/-- If `M.transpose` shatters `S ⊆ Fin m` with `|S| ≥ 2^(d+1)`, then `M`
shatters some set of `d+1` columns. Matrix corollary of the Finset form. -/
theorem transpose_shatters_imp_shatters {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (S : Finset (Fin m)) (hS : M.transpose.shatters S)
    (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset (Fin n), T.card = d + 1 ∧ M.shatters T := by
  -- Row function: each `i : Fin m` gives `row i : Finset (Fin n)`.
  let row : Fin m → Finset (Fin n) := fun i => Finset.univ.filter (fun j => M i j = true)
  -- Rows are injective on `S` (distinct rows get separated by the shattering columns).
  have hrow_inj : ∀ ⦃i₁⦄, i₁ ∈ S → ∀ ⦃i₂⦄, i₂ ∈ S → row i₁ = row i₂ → i₁ = i₂ := by
    intro i₁ hi₁ i₂ hi₂ hrow
    by_contra hne
    -- Use shattering with `t := {i₁}` to separate them.
    obtain ⟨j, hj⟩ := hS {i₁} (by simp [hi₁])
    have h1 : M i₁ j = true := by
      have := (hj i₁ hi₁).mpr (by simp)
      simpa [transpose] using this
    have h2 : M i₂ j = false := by
      have hne' : i₂ ∉ ({i₁} : Finset (Fin m)) := by simp [Ne.symm hne]
      have hiff := hj i₂ hi₂
      simp only [transpose] at hiff
      have : M i₂ j ≠ true := fun h => hne' (hiff.mp h)
      exact Bool.eq_false_iff.mpr this
    -- But `row i₁ = row i₂` means `M i₁ j = true ↔ M i₂ j = true`.
    have : j ∈ row i₁ ↔ j ∈ row i₂ := by rw [hrow]
    simp only [row, mem_filter, mem_univ, true_and] at this
    rw [h1, h2] at this
    exact absurd (this.mp rfl) (by decide)
  -- Build the image family S' of rows.
  let S' : Finset (Finset (Fin n)) := S.image row
  -- Cardinality of S' matches S (via injectivity).
  have hS'_card : S'.card = S.card :=
    Finset.card_image_of_injOn (fun i hi j hj => hrow_inj hi hj)
  have hS'_ge : 2 ^ (d + 1) ≤ S'.card := hS'_card ▸ hcard
  -- Key: `(M.toFinsetFamily.dualFamily univ).Shatters S'`.
  have hS'_shat : (M.toFinsetFamily.dualFamily (Finset.univ : Finset (Fin n))).Shatters S' := by
    intro t' ht'_sub
    -- Define `t := S.filter (fun i => row i ∈ t')`.
    let t : Finset (Fin m) := S.filter (fun i => row i ∈ t')
    have ht_sub : t ⊆ S := Finset.filter_subset _ _
    -- Apply transpose-shattering on t to extract column j.
    obtain ⟨j, hj⟩ := hS t ht_sub
    -- Build `u := M.toFinsetFamily.filter (fun A => j ∈ A)`, which lies in the dualFamily.
    let u : Finset (Finset (Fin n)) :=
      M.toFinsetFamily.filter (fun A => j ∈ A)
    refine ⟨u, ?_, ?_⟩
    · -- u is in the dualFamily image.
      simp only [dualFamily, mem_image, mem_univ, true_and]
      exact ⟨j, rfl⟩
    · -- S' ∩ u = t'.
      ext A
      rw [mem_inter]
      constructor
      · rintro ⟨hAS', hAu⟩
        -- hAu : A ∈ u, unfold the filter
        rw [show u = M.toFinsetFamily.filter (fun A => j ∈ A) from rfl,
            Finset.mem_filter] at hAu
        obtain ⟨_hAfam, hjA⟩ := hAu
        -- A = row i for some i ∈ S.
        simp only [S', mem_image] at hAS'
        obtain ⟨i, hi, rfl⟩ := hAS'
        -- From j ∈ row i: M i j = true, so by `hj`, i ∈ t.
        have hMij : M i j = true := by
          simp only [row, mem_filter, mem_univ, true_and] at hjA
          exact hjA
        have hit : i ∈ t := by
          have hth := (hj i hi).mp
          simp only [transpose] at hth
          exact hth hMij
        simp only [t, mem_filter] at hit
        exact hit.2
      · intro hAt'
        -- A ∈ t' ⊆ S', so A = row i for some i ∈ S with row i ∈ t'.
        have hAS' : A ∈ S' := ht'_sub hAt'
        refine ⟨hAS', ?_⟩
        rw [show u = M.toFinsetFamily.filter (fun A => j ∈ A) from rfl,
            Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · -- A ∈ M.toFinsetFamily
          simp only [S', mem_image] at hAS'
          obtain ⟨i, _, rfl⟩ := hAS'
          simp only [toFinsetFamily, mem_image, mem_univ, true_and]
          exact ⟨i, rfl⟩
        · -- j ∈ A
          simp only [S', mem_image] at hAS'
          obtain ⟨i, hi, rfl⟩ := hAS'
          have hit : i ∈ t := by
            simp only [t, mem_filter]
            exact ⟨hi, hAt'⟩
          have hMij : M i j = true := by
            have hth := (hj i hi).mpr
            simp only [transpose] at hth
            exact hth hit
          simp only [row, mem_filter, mem_univ, true_and]
          exact hMij
  -- Invoke the Finset-level bitstring coding.
  obtain ⟨T, _hTuniv, hT_card, hT_shat⟩ :=
    Finset.dualFamily_shatters_imp_shatters M.toFinsetFamily Finset.univ S' hS'_shat hS'_ge
  -- Translate Mathlib-shatters on M.toFinsetFamily back to M.shatters.
  refine ⟨T, hT_card, ?_⟩
  exact (shatters_iff M T).mpr hT_shat

end BinaryMatrix
