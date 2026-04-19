import Lake
open Lake DSL

package ZPM where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib ZPM where
  roots := #[`ZPM]

lean_lib Verification where
  roots := #[
    `Verification.Definitions,
    `Verification.Headlines,
    `Verification.ChallengeCrown,
    `Verification.SolutionCrown
  ]

lean_exe verification_extract where
  root := `Verification.Extract
  supportInterpreter := true

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "2c53994ec06c7197a0f05dd85e8aae96e454efb8"
