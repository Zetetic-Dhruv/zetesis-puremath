/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Combinatorics.SetFamily.DualVC.Def
import Mathlib.Data.Fintype.EquivFin

/-!
# Bitstring coding: transpose-shattering implies column-shattering

Assouad's technique for the dual VC bound: if the transpose `Mᵀ` shatters a
set `S` with `|S| ≥ 2^(d+1)`, then `M` itself shatters a column set of size
`d + 1`. Each row is encoded as a bitstring over `d+1` distinguished
columns, extracted via `Mᵀ`-shattering of the coordinate projections.
-/

open Classical Finset

namespace BinaryMatrix

/-- If `M.transpose` shatters `S ⊆ Fin m` with `|S| ≥ 2^(d+1)`, then `M`
shatters some set of `d+1` columns. -/
theorem transpose_shatters_imp_shatters {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (S : Finset (Fin m)) (hS : M.transpose.shatters S)
    (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset (Fin n), T.card = d + 1 ∧ M.shatters T := by
  let eS := S.equivFin
  let eFun : (Fin (d + 1) → Bool) ≃ Fin (2 ^ (d + 1)) :=
    Fintype.equivOfCardEq (by simp)
  let eFin : Fin (2 ^ (d + 1)) ↪ Fin S.card := Fin.castLEEmb hcard
  let eFinS : Fin S.card ≃ ↥S := eS.symm
  let embed : (Fin (d + 1) → Bool) → ↥S := eFinS ∘ eFin ∘ eFun
  have hembed_inj : Function.Injective embed := by
    intro a b hab
    simp only [embed, Function.comp] at hab
    exact eFun.injective (eFin.injective (eFinS.injective hab))
  let T_k (k : Fin (d + 1)) : Finset (Fin m) :=
    S.filter (fun i => ∃ b : Fin (d + 1) → Bool, (embed b).val = i ∧ b k = true)
  have hT_k_sub : ∀ k, T_k k ⊆ S := fun k => Finset.filter_subset _ _
  have hcols : ∀ k : Fin (d + 1), ∃ c : Fin n, ∀ i ∈ S,
      (M i c = true ↔ i ∈ T_k k) := by
    intro k
    obtain ⟨c, hc⟩ := hS (T_k k) (hT_k_sub k)
    exact ⟨c, fun i hi => by
      have := hc i hi
      simp only [transpose] at this
      exact this⟩
  choose c hc using hcols
  have hM_embed : ∀ (b : Fin (d + 1) → Bool) (k : Fin (d + 1)),
      M (embed b).val (c k) = b k := by
    intro b k
    have hemb_mem : (embed b).val ∈ S := (embed b).property
    have := (hc k (embed b).val hemb_mem).mp
    have := (hc k (embed b).val hemb_mem).mpr
    by_cases hbk : b k = true
    · have hmem : (embed b).val ∈ T_k k := by
        simp only [T_k, Finset.mem_filter]
        exact ⟨hemb_mem, ⟨b, rfl, hbk⟩⟩
      rw [(hc k _ hemb_mem).mpr hmem, hbk]
    · simp only [Bool.not_eq_true] at hbk
      have hmem : (embed b).val ∉ T_k k := by
        simp only [T_k, Finset.mem_filter, not_and]
        intro _
        rintro ⟨b', hb'eq, hb'k⟩
        have : embed b' = embed b := by
          exact Subtype.val_injective (by rw [hb'eq])
        have := hembed_inj this
        rw [this] at hb'k
        rw [hbk] at hb'k
        exact Bool.noConfusion hb'k
      rw [Bool.eq_false_iff.mpr (mt (hc k _ hemb_mem).mp hmem), hbk]
  let T : Finset (Fin n) := Finset.univ.image c
  have hc_inj : Function.Injective c := by
    intro j k hjk
    by_contra hjk_ne
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    have h1 : M (embed b0).val (c j) = true := by
      rw [hM_embed b0 j]; simp [b0]
    have h2 : M (embed b0).val (c k) = false := by
      rw [hM_embed b0 k]; simp only [b0]
      cases hkj : (k == j)
      · rfl
      · exfalso; exact hjk_ne (beq_iff_eq.mp hkj).symm
    rw [hjk] at h1
    rw [h1] at h2
    exact Bool.noConfusion h2
  have hT_card : T.card = d + 1 := by
    simp only [T, card_image_of_injective _ hc_inj, card_univ, Fintype.card_fin]
  have hT_shatters : M.shatters T := by
    intro t ht
    let g : Fin (d + 1) → Bool := fun k => decide (c k ∈ t)
    refine ⟨(embed g).val, fun j hj => ?_⟩
    simp only [T] at hj
    rw [Finset.mem_image] at hj
    obtain ⟨k, _, rfl⟩ := hj
    constructor
    · intro hM
      rw [hM_embed g k] at hM
      simp only [g] at hM
      rwa [decide_eq_true_eq] at hM
    · intro hck
      rw [hM_embed g k]
      simp only [g]
      rwa [decide_eq_true_eq]
  exact ⟨T, hT_card, hT_shatters⟩

end BinaryMatrix
