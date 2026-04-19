/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Combinatorics.SetFamily.DualVC.MathlibBridge
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Sauer-Shelah for binary matrices

Quantitative binomial-sum bound on the number of distinct rows in a binary
matrix, derived from Mathlib's `Finset.card_shatterer_le_sum_vcDim`.
-/

open Classical Finset

namespace BinaryMatrix

/-- **Sauer-Shelah for binary matrices**: the number of distinct rows in
the Finset family is bounded by `∑ k ∈ Iic d, n.choose k` whenever the VC
dimension is at most `d`. -/
theorem card_toFinsetFamily_le {m n : ℕ} (M : BinaryMatrix m n)
    {d : ℕ} (hd : M.toFinsetFamily.vcDim ≤ d) :
    M.toFinsetFamily.card ≤ ∑ k ∈ Finset.Iic d, n.choose k := by
  calc M.toFinsetFamily.card
      _ ≤ M.toFinsetFamily.shatterer.card := card_le_card_shatterer _
      _ ≤ ∑ k ∈ Iic M.toFinsetFamily.vcDim, (Fintype.card (Fin n)).choose k :=
          card_shatterer_le_sum_vcDim
      _ = ∑ k ∈ Iic M.toFinsetFamily.vcDim, n.choose k := by
          simp [Fintype.card_fin]
      _ ≤ ∑ k ∈ Iic d, n.choose k := by
          have hsub : Iic M.toFinsetFamily.vcDim ⊆ Iic d := Iic_subset_Iic.mpr hd
          exact le_trans (le_refl _)
            (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))

end BinaryMatrix
