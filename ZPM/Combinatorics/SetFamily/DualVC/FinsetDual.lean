/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Combinatorics.SetFamily.DualVC.Def
import Mathlib.Data.Fintype.EquivFin

/-!
# Assouad's dual VC bound at the `Finset (Finset α)` level

The bitstring-coding core and the headline VC bound, phrased directly on
`Finset (Finset α)` via `Finset.dualFamily`. These are the Mathlib-PR-facing
statements; the matrix-level statements in `TransposeCoding.lean` and
`Assouad.lean` are derived as corollaries.

Reference: Assouad 1983, *Densité et dimension*, Ann. Inst. Fourier **33** (3),
Thm 2.13.
-/

open Classical Finset

namespace Finset

/-- **Bitstring coding (Finset form).** If the dual family `𝒜.dualFamily X`
shatters a subfamily `S` of size at least `2^(d+1)`, then `𝒜` itself shatters
some `(d+1)`-element subset of `X`. -/
theorem dualFamily_shatters_imp_shatters {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (X : Finset α)
    (S : Finset (Finset α)) (hS : (𝒜.dualFamily X).Shatters S)
    {d : ℕ} (hcard : 2 ^ (d + 1) ≤ S.card) :
    ∃ T : Finset α, T ⊆ X ∧ T.card = d + 1 ∧ 𝒜.Shatters T := by
  -- Step 0: from `hS`, derive `S ⊆ 𝒜`. Taking `t := S` in the shattering
  -- produces `u ∈ 𝒜.dualFamily X` with `S ∩ u = S`, so `S ⊆ u ⊆ 𝒜`.
  have hS_sub_𝒜 : S ⊆ 𝒜 := by
    obtain ⟨u, hu_mem, hu_eq⟩ := hS (Finset.Subset.refl S)
    simp only [dualFamily, mem_image] at hu_mem
    obtain ⟨_, _, hxu⟩ := hu_mem
    have hSu : S ⊆ u := by
      rw [← hu_eq]; exact Finset.inter_subset_right
    intro A hA
    have : A ∈ u := hSu hA
    rw [← hxu, mem_filter] at this
    exact this.1
  -- Step 1: embed `(Fin (d+1) → Bool)` injectively into `S` via cardinality.
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
  -- Step 2: for each coordinate `k`, form the subfamily of `S` on which
  -- the `k`-th bit of the embedding is `true`.
  let T_k (k : Fin (d + 1)) : Finset (Finset α) :=
    S.filter (fun A => ∃ b : Fin (d + 1) → Bool, (embed b).val = A ∧ b k = true)
  have hT_k_sub : ∀ k, T_k k ⊆ S := fun k => Finset.filter_subset _ _
  -- Step 3: for each `k`, `(𝒜.dualFamily X).Shatters S` yields some
  -- `x_k ∈ X` with `x_k ∈ A ↔ A ∈ T_k k` for all `A ∈ S`.
  have hcols : ∀ k : Fin (d + 1), ∃ x : α, x ∈ X ∧ ∀ A ∈ S,
      (x ∈ A ↔ A ∈ T_k k) := by
    intro k
    obtain ⟨u, hu_mem, hu_eq⟩ := hS (hT_k_sub k)
    simp only [dualFamily, mem_image] at hu_mem
    obtain ⟨x, hxX, hxu⟩ := hu_mem
    refine ⟨x, hxX, fun A hA => ?_⟩
    -- A ∈ T_k k ↔ A ∈ S ∩ u ↔ (A ∈ S ∧ A ∈ u) ↔ (A ∈ S ∧ A ∈ 𝒜 ∧ x ∈ A)
    have hAu : A ∈ u ↔ x ∈ A := by
      rw [← hxu, mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨hS_sub_𝒜 hA, h⟩⟩
    constructor
    · intro hxA
      have : A ∈ S ∩ u := by
        rw [mem_inter]; exact ⟨hA, hAu.mpr hxA⟩
      rw [hu_eq] at this
      exact this
    · intro hAT
      have : A ∈ S ∩ u := by rw [hu_eq]; exact hAT
      rw [mem_inter] at this
      exact hAu.mp this.2
  choose x hxX hx using hcols
  -- Step 4: show embed agrees: `(embed b).val ∈ A` iff `b k = true` translates to
  -- `x k ∈ (embed b).val ↔ b k = true`.
  have hx_embed : ∀ (b : Fin (d + 1) → Bool) (k : Fin (d + 1)),
      (x k ∈ (embed b).val) ↔ (b k = true) := by
    intro b k
    have hemb_mem : (embed b).val ∈ S := (embed b).property
    by_cases hbk : b k = true
    · refine ⟨fun _ => hbk, fun _ => ?_⟩
      rw [(hx k (embed b).val hemb_mem)]
      simp only [T_k, mem_filter]
      exact ⟨hemb_mem, ⟨b, rfl, hbk⟩⟩
    · simp only [Bool.not_eq_true] at hbk
      refine ⟨fun hxA => ?_, fun h => by rw [hbk] at h; exact absurd h (by decide)⟩
      rw [(hx k (embed b).val hemb_mem)] at hxA
      simp only [T_k, mem_filter] at hxA
      obtain ⟨_, b', hb'eq, hb'k⟩ := hxA
      have hbb : b' = b := by
        apply hembed_inj
        apply Subtype.ext
        rw [hb'eq]
      rw [hbb, hbk] at hb'k
      exact absurd hb'k (by decide)
  -- Step 5: assemble T := {x k | k : Fin (d+1)} via image.
  let T : Finset α := Finset.univ.image x
  -- Step 6: x is injective, so |T| = d + 1.
  have hx_inj : Function.Injective x := by
    intro j k hjk
    by_contra hjk_ne
    let b0 : Fin (d + 1) → Bool := fun i => i == j
    have h1 : x j ∈ (embed b0).val := by
      rw [hx_embed b0 j]; simp [b0]
    have h2 : x k ∉ (embed b0).val := by
      intro hxk
      rw [hx_embed b0 k] at hxk
      simp only [b0] at hxk
      cases hkj : (k == j) with
      | true => exact hjk_ne (beq_iff_eq.mp hkj).symm
      | false => rw [hkj] at hxk; exact absurd hxk (by decide)
    rw [hjk] at h1
    exact h2 h1
  have hT_card : T.card = d + 1 := by
    simp only [T, card_image_of_injective _ hx_inj, card_univ, Fintype.card_fin]
  -- Step 7: T ⊆ X (each x k ∈ X).
  have hT_sub_X : T ⊆ X := by
    intro y hy
    simp only [T, mem_image, mem_univ, true_and] at hy
    obtain ⟨k, rfl⟩ := hy
    exact hxX k
  -- Step 8: 𝒜.Shatters T via the embedding.
  have hT_shatters : 𝒜.Shatters T := by
    intro t ht
    -- Build a Bool-vector g such that `embed g` realizes `t` within `T`.
    let g : Fin (d + 1) → Bool := fun k => decide (x k ∈ t)
    refine ⟨(embed g).val, hS_sub_𝒜 (embed g).property, ?_⟩
    -- Need T ∩ (embed g).val = t.
    ext y
    simp only [mem_inter]
    constructor
    · rintro ⟨hyT, hyE⟩
      simp only [T, mem_image, mem_univ, true_and] at hyT
      obtain ⟨k, rfl⟩ := hyT
      rw [hx_embed g k] at hyE
      simp only [g] at hyE
      exact of_decide_eq_true hyE
    · intro hyt
      have hyT : y ∈ T := ht hyt
      refine ⟨hyT, ?_⟩
      simp only [T, mem_image, mem_univ, true_and] at hyT
      obtain ⟨k, rfl⟩ := hyT
      rw [hx_embed g k]
      simp only [g]
      exact decide_eq_true hyt
  exact ⟨T, hT_sub_X, hT_card, hT_shatters⟩

/-- **Assouad's dual VC bound (Finset form).** If `𝒜.vcDim ≤ d`, then the
dual family has VC dimension at most `2^(d+1) - 1`. -/
theorem vcDim_dualFamily_le {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (X : Finset α)
    {d : ℕ} (hvc : 𝒜.vcDim ≤ d) :
    (𝒜.dualFamily X).vcDim ≤ 2 ^ (d + 1) - 1 := by
  by_contra hlt
  push Not at hlt
  have hge : 2 ^ (d + 1) ≤ (𝒜.dualFamily X).vcDim := by omega
  have hpos : 0 < 2 ^ (d + 1) := Nat.two_pow_pos (d + 1)
  have hge' : 2 ^ (d + 1) ≤ (𝒜.dualFamily X).shatterer.sup Finset.card := hge
  obtain ⟨S, hS_mem, hS_card⟩ := (Finset.le_sup_iff hpos).mp hge'
  rw [Finset.mem_shatterer] at hS_mem
  obtain ⟨T, _hTX, hT_card, hT_shat⟩ :=
    dualFamily_shatters_imp_shatters 𝒜 X S hS_mem hS_card
  have hvc_ge : d + 1 ≤ 𝒜.vcDim := by
    calc d + 1 = T.card := hT_card.symm
    _ ≤ 𝒜.vcDim := hT_shat.card_le_vcDim
  omega

end Finset
