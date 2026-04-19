# Charter

`zetesis-puremath` is a shared, project-agnostic, sorry-free, axiom-transparent staging repo for Mathlib-adjacent mathematics extracted from Zetesis formalization projects.

## Scope

A module belongs here if and only if its content is substrate-neutral pure mathematics of general use to multiple Zetesis projects, and is eligible for eventual contribution to Mathlib without Zetesis-specific dependencies. Project-specific utilities, learning-theoretic infrastructure, and control/proof-programming helpers belong in the project repos where they are used, not here.

## Duplicate rule

If Mathlib already contains a declaration and a Zetesis-side file is merely an ergonomic wrapper with no novel content, the file stays in its specialized project (for example, `formal-learning-theory-kernel` or `SMFE`). It is not migrated into this repo.

### Duplicate rule exception: proof-engineering specializations

A Zetesis-side type that nominally overlaps with a Mathlib type IS admitted to `zetesis-puremath` if and only if all three hold:

1. It is a specialization over a strictly-more-structured value or index type than the Mathlib counterpart (for example, an `ℝ`-valued PMF where Mathlib is `ℝ≥0∞`-valued, or a `Fintype`-indexed version where Mathlib is any type).
2. The specialization enables proof engineering that the Mathlib type cannot support (for example, `linarith`, `nlinarith`, `field_simp` on `ℝ` where Mathlib's `ℝ≥0∞`-valued counterpart would require manual `toReal` round-trips and break field-arithmetic tactics).
3. A bridge declaration linking the specialization back to the Mathlib counterpart is provided in the same subtree.

Precedent: `ZPM.Probability.FintypePMF` (`ℝ`-valued, `Fintype`-indexed, `Finset.sum`-based) coexists with `Mathlib.Probability.ProbabilityMassFunction` (`ℝ≥0∞`-valued, any-type, `HasSum`-based) because the multiplicative-weights-update proof chain uses `ℝ`-arithmetic tactics that do not transfer to `ℝ≥0∞` without proof-LOC blowup. The bridge lives at `ZPM.Probability.FintypePMF.Bridge`.

## Admission rule

A module enters `zetesis-puremath` only if it passes all four of:

- **Pl (Plausibility).** Fills a real gap in current Mathlib, or has demonstrated reuse across multiple Zetesis projects.
- **Coh (Coherence).** Imports only Mathlib or already-admitted modules in this repo. No FLT-, SMFE-, or TLT-specific types leak in.
- **Inv (Invariance).** Survives one Mathlib pin bump and one namespace refactor without semantic change.
- **Comp (Completeness).** Theorem inventory, axiom inventory, and downstream consumer list are documented.

## Invariants

- Zero `sorry` across the entire repo.
- Only the standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) appear in the transitive axiom closure of any declaration, unless a module is explicitly scoped as axiom-gated with a named mathematical axiom, documented in `META/AXIOMS.md` and surfaced via `Verification/PrintAxioms.lean`.
- Tier 0 (lake build), Tier 1 (#print axioms), and Tier 2 (lean4checker --fresh) pass on every commit to `main`.

## Release policy

This repo is Work In Progress until it stabilizes. The first tagged release is `v0.1.0`. Until then downstream projects must pin by commit hash if they adopt it early. Tag cadence after `v0.1.0` is decided per release.

## Dependency policy

This repo depends on Mathlib only. It does not depend on any Zetesis project. Downstream Zetesis projects depend on tagged releases of this repo, not on `main`.
