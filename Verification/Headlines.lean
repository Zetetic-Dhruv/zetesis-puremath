/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/

import Lean
import ZPM

/-!
# Verification.Headlines

Curated list of ZPM theorems that act as crown-jewel headlines for the
Tier 3 comparator pipeline. Each entry becomes a challenge-statement
(with `sorry` proof position) and a matching solution-statement in the
generated `ChallengeCrown.lean` and `SolutionCrown.lean`.

This file is the single source of truth for the headline set. The
extractor `Verification/Extract.lean` reads `headlines` to regenerate the
Challenge / Solution / premise artifacts.
-/

namespace Verification.Headlines

/-- List of fully-qualified Lean names that ZPM exposes as crown-jewel
theorems. Populated incrementally as ZPM phases land. -/
def headlines : List Lean.Name := [
  ``MeasureTheory.AnalyticSet.nullMeasurableSet,
  ``MeasureTheory.AnalyticSet.compactCap_eq,
  ``MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact,
  ``ProbabilityTheory.chebyshev_majority_bound,
  ``BinaryMatrix.assouad_transpose_vcDim,
  ``ProbabilityTheory.covering_minimax,
  ``ProbabilityTheory.finite_approx_minimax,
  ``ProbabilityTheory.mwu_potential_T_bound,
  ``ProbabilityTheory.mwu_approx_minimax
]

end Verification.Headlines
