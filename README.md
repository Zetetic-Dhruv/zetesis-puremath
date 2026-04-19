# zetesis-puremath

> **Blueprint** (definitions + crown theorems, with clickable Lean cross-refs): <https://zetetic-dhruv.github.io/zetesis-puremath/blueprint/>
> &nbsp;&nbsp;**API docs**: <https://zetetic-dhruv.github.io/zetesis-puremath/docs/> &nbsp;&middot;&nbsp; **Landing**: <https://zetetic-dhruv.github.io/zetesis-puremath/>

A personal pure-mathematics reservoir in Lean 4: pieces of mathematics I have needed in my formalization projects (the [formal-learning-theory-kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel), SMFE, and others) that are absent from Mathlib, or that I have chosen to specialize in a way Mathlib's current formulation does not support directly.

Every declaration in this repo is proved in Lean 4. Zero `sorry`. Only the standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) appear in the axiom closure.

Open for anyone who wants to use it.

## Charter

See [CHARTER.md](CHARTER.md) for the admission rule, duplicate policy, and dependency policy.

## What is in here (today)

| Area | What |
|---|---|
| `ZPM/MeasureTheory/AnalyticMeasurability/` | Analytic sets are `NullMeasurableSet` under finite Borel measures on Polish spaces |
| `ZPM/MeasureTheory/ChoquetCapacity/` | Kechris 30.13 (capacitability for analytic sets), `compactCap`, `IsChoquetCapacity` |
| `ZPM/MeasureTheory/ProbabilityMeasure/TotalVariation/` | ℝ-valued metric TV distance `tvDistReal` |
| `ZPM/InformationTheory/KullbackLeibler/Real/` | ℝ-valued KL bridge to Mathlib's ENNReal `klDiv` |
| `ZPM/InformationTheory/KullbackLeibler/Binary/` | Binary KL `klBin` with its full derivative / monotonicity chain |
| `ZPM/InformationTheory/KullbackLeibler/Fintype` | Fintype-indexed ℝ-valued KL |
| `ZPM/InformationTheory/CrossEntropy/Fintype` | Fintype-indexed cross-entropy |
| `ZPM/InformationTheory/MutualInformation/` | ℝ-valued MI, nonnegativity, zero-iff-product |
| `ZPM/InformationTheory/Pinsker/` | Pinsker's inequality with the sharp constant |
| `ZPM/Probability/Concentration/` | `BoundedRandomVariable` typeclass, Chebyshev majority bound |
| `ZPM/Probability/Exchangeability/` | Double-sample, merge/split, `ValidSplit`, `SplitMeasure` |
| `ZPM/Probability/FintypePMF/` | ℝ-valued `Fintype`-indexed PMF with `linarith`-compatible arithmetic, bridge to `Mathlib.PMF` |
| `ZPM/Probability/Decision/Minimax/` | Covering-based minimax, MWU, approximate minimax via multiplicative-weights-update |
| `ZPM/Analysis/InnerProductSpace/KernelMeanEmbedding/` | Kernel mean embedding of a measure into an RKHS, with reproducing property |
| `ZPM/Analysis/InnerProductSpace/MMD/` | Maximum Mean Discrepancy, `IsCharacteristic`, zero-iff-equal |
| `ZPM/Analysis/InnerProductSpace/HSIC/` | Hilbert-Schmidt Independence Criterion, zero-iff-independent |
| `ZPM/Combinatorics/SetFamily/DualVC/` | Assouad's dual VC bound `VCDim(Mᵀ) ≤ 2^(d+1) − 1` for binary matrices |
| `ZPM/Combinatorics/SetFamily/BoolFamily` | VC dimension of a finite `Bool`-valued function family |

## Build

```bash
lake update
lake exe cache get
lake build
```

Lean `v4.30.0-rc2` | Mathlib4 pinned to a recent master commit (see `lakefile.lean`).

## Use it

```lean
-- In your lakefile.lean:
require «zetesis-puremath» from git
  "https://github.com/Zetetic-Dhruv/zetesis-puremath.git" @ "main"

-- In your .lean files:
import ZPM
-- or a specific submodule, e.g.:
import ZPM.InformationTheory.Pinsker.Basic
import ZPM.Probability.FintypePMF.Basic
```

Downstream projects should pin to a commit hash or a tagged release. The repo is work in progress and will have its first tagged release once the full verification suite (including the Tier 3 comparator) is wired up.

## Verification

| Tier | Status |
|---|---|
| 0: `lake build` | ✔ 0 errors, 0 warnings |
| 1: `#print axioms` on crown-jewel theorems | ✔ only `propext`, `Classical.choice`, `Quot.sound` |
| 2: `leanchecker --fresh` | ✔ available via `workflow_dispatch` |
| 3: comparator + Landlock sandbox | pending |

## License

Apache 2.0.
