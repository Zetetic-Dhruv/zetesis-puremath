/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.Probability.FintypePMF.Normalize

/-!
# FintypePMF.uniform: uniform distribution over a nonempty Fintype

Built on `FintypePMF.normalize` with the all-ones weight vector.
Functionally parallels `Mathlib.PMF.uniformOfFintype`, but lives in the
`ℝ`-valued world needed for the MWU arithmetic.
-/

noncomputable section

namespace ProbabilityTheory.FintypePMF

/-- Uniform `FintypePMF` over a nonempty Fintype. -/
def uniform (α : Type*) [Fintype α] [Nonempty α] : FintypePMF α :=
  normalize (fun _ : α => (1 : ℝ)) fun _ => one_pos

end ProbabilityTheory.FintypePMF

end
