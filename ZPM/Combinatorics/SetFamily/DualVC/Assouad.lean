/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Combinatorics.SetFamily.DualVC.MathlibBridge
import ZPM.Combinatorics.SetFamily.DualVC.TransposeCoding

/-!
# Assouad's dual VC bound

If a binary matrix `M` has VC dimension at most `d`, then its transpose
has VC dimension at most `2^(d+1) - 1`. Proof by the bitstring coding
argument (Assouad 1983): from a shattered set of size `2^(d+1)` in `Mᵀ`,
extract `d + 1` shattered columns of `M`, contradicting `M.vcDim ≤ d`.
-/

open Classical Finset

namespace BinaryMatrix

/-- **Assouad's dual VC bound (matrix form)**: `M.vcDim ≤ d` implies
`M.transpose.vcDim ≤ 2^(d+1) - 1`. -/
theorem assouad_transpose_vcDim {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (hd : M.vcDim ≤ d) :
    M.transpose.vcDim ≤ 2 ^ (d + 1) - 1 := by
  by_contra hlt
  push_neg at hlt
  have hge : 2 ^ (d + 1) ≤ M.transpose.vcDim := by omega
  have hpos : (⊥ : ℕ) < 2 ^ (d + 1) := by
    show 0 < 2 ^ (d + 1)
    exact Nat.two_pow_pos (d + 1)
  have hge' : 2 ^ (d + 1) ≤ M.transpose.toFinsetFamily.shatterer.sup Finset.card := hge
  obtain ⟨S, hS_mem, hS_card⟩ := (Finset.le_sup_iff hpos).mp hge'
  rw [Finset.mem_shatterer] at hS_mem
  have hS_shat : M.transpose.shatters S := (shatters_iff M.transpose S).mpr hS_mem
  obtain ⟨T, hT_card, hT_shat⟩ := transpose_shatters_imp_shatters M S hS_shat hS_card
  have hT_mathlib : M.toFinsetFamily.Shatters T := (shatters_iff M T).mp hT_shat
  have hvc_ge : d + 1 ≤ M.vcDim := by
    calc d + 1 = T.card := hT_card.symm
    _ ≤ M.vcDim := hT_mathlib.card_le_vcDim
  omega

end BinaryMatrix
