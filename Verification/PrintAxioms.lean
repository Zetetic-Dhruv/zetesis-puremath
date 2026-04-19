/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/

import Verification.SolutionCrown

/-!
# Verification.PrintAxioms

Runs `#print axioms` over every declaration in `Verification.SolutionCrown`
to enforce the Tier 1 invariant: only standard Lean kernel axioms
(`propext`, `Classical.choice`, `Quot.sound`) may appear, unless a
module is explicitly axiom-gated.

Phase 0 has no headline theorems, so this file performs no per-theorem
checks and serves as the scaffold for Phase 1 and onward.
-/

-- `#print axioms <name>` commands are inserted here by later phases,
-- one per entry in `Verification.Headlines.headlines`.
