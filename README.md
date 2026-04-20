# zetesis-puremath

[![CI](https://github.com/Zetetic-Dhruv/zetesis-puremath/actions/workflows/ci.yml/badge.svg)](https://github.com/Zetetic-Dhruv/zetesis-puremath/actions/workflows/ci.yml)
[![lean4checker](https://github.com/Zetetic-Dhruv/zetesis-puremath/actions/workflows/lean4checker.yml/badge.svg)](https://github.com/Zetetic-Dhruv/zetesis-puremath/actions/workflows/lean4checker.yml)
[![Docs](https://github.com/Zetetic-Dhruv/zetesis-puremath/actions/workflows/docs.yml/badge.svg)](https://github.com/Zetetic-Dhruv/zetesis-puremath/actions/workflows/docs.yml)
[![Blueprint](https://github.com/Zetetic-Dhruv/zetesis-puremath/actions/workflows/blueprint.yml/badge.svg)](https://github.com/Zetetic-Dhruv/zetesis-puremath/actions/workflows/blueprint.yml)
[![Comparator](https://img.shields.io/badge/comparator-PASS-brightgreen)](https://gitlab.com/Zetetic-Dhruv/zetesis-puremath-verification/-/pipelines/2463996501)

![Lean](https://img.shields.io/badge/Lean-v4.30.0--rc2-blue)
![Mathlib](https://img.shields.io/badge/mathlib4-2c53994-blue)
![Theorems](https://img.shields.io/badge/theorems-114-informational)
![sorry](https://img.shields.io/badge/sorry-0-brightgreen)
![Axioms](https://img.shields.io/badge/axioms-propext%20%7C%20Quot.sound%20%7C%20Classical.choice-brightgreen)
[![License](https://img.shields.io/badge/license-Apache_2.0-green)](./LICENSE)

**[Blueprint](https://zetetic-dhruv.github.io/zetesis-puremath/blueprint/)** &nbsp;·&nbsp;
**[API docs](https://zetetic-dhruv.github.io/zetesis-puremath/docs/)** &nbsp;·&nbsp;
**[Landing page](https://zetetic-dhruv.github.io/zetesis-puremath/)** &nbsp;·&nbsp;
**[Definitions review](./Verification/DEFINITIONS_REVIEW.md)** &nbsp;·&nbsp;
**[Comparator pipeline](https://gitlab.com/Zetetic-Dhruv/zetesis-puremath-verification)**

---

A personal pure-mathematics reservoir in Lean 4: pieces of mathematics I have needed in my formalization projects (the [formal-learning-theory-kernel](https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel), SMFE, and others) that are absent from Mathlib, or that I have chosen to specialize in a way Mathlib's current formulation does not support directly.

Every declaration in this repo is proved in Lean 4. Zero `sorry`. Only the standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) appear in the axiom closure.

Open for anyone who wants to use it.

## What is in here

| Area | What |
|---|---|
| `ZPM/MeasureTheory/AnalyticMeasurability/` | Analytic sets are `NullMeasurableSet` under finite Borel measures on Polish spaces |
| `ZPM/MeasureTheory/ChoquetCapacity/` | Kechris 30.13 (capacitability for analytic sets), `compactCap`, `IsChoquetCapacity` |
| `ZPM/MeasureTheory/ProbabilityMeasure/TotalVariation/` | ℝ-valued metric TV distance `tvDistReal` |
| `ZPM/InformationTheory/KullbackLeibler/Real/` | ℝ-valued KL bridge to Mathlib's ENNReal `klDiv` |
| `ZPM/InformationTheory/KullbackLeibler/Binary/` | Binary KL `klBin` with its full derivative / monotonicity chain |
| `ZPM/InformationTheory/KullbackLeibler/Fintype/` | Fintype-indexed ℝ-valued KL |
| `ZPM/InformationTheory/CrossEntropy/Fintype/` | Fintype-indexed cross-entropy |
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
| `ZPM/Combinatorics/SetFamily/BoolFamily/` | VC dimension of a finite `Bool`-valued function family |

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

Downstream projects should pin to a commit hash or a tagged release. The repo is work-in-progress and will have its first tagged release once the full verification suite is stable on a tagged Lean toolchain.

## Verification

| Tier | Check | Status |
|---|---|---|
| **0** | `lake build` | ![Tier 0](https://img.shields.io/badge/%E2%9C%94-PASS-brightgreen) &nbsp; 0 errors, 0 warnings, 0 `sorry` |
| **1** | `#print axioms` on every public theorem | ![Tier 1](https://img.shields.io/badge/%E2%9C%94-PASS-brightgreen) &nbsp; 113 / 114 use only `propext` + `Quot.sound` + `Classical.choice`; 1 uses none |
| **2** | `leanchecker --fresh` per module | ![Tier 2](https://img.shields.io/badge/workflow__dispatch-available-blue) &nbsp; [`lean4checker.yml`](.github/workflows/lean4checker.yml) |
| **3** | `comparator` + Landlock sandbox | ![Tier 3](https://img.shields.io/badge/%E2%9C%94-PASS-brightgreen) &nbsp; [pipeline #2463996501](https://gitlab.com/Zetetic-Dhruv/zetesis-puremath-verification/-/pipelines/2463996501): *"Lean default kernel accepts the solution. Your solution is okay!"* |

Raw CI artifacts committed under [`test/verification/CI/`](./test/verification/CI/). A literature review pinning every definition and headline theorem to its canonical source is at [`Verification/DEFINITIONS_REVIEW.md`](./Verification/DEFINITIONS_REVIEW.md).

## Cite this work

GitHub shows a "Cite this repository" button that reads from [`CITATION.cff`](./CITATION.cff) and emits BibTeX / APA / Chicago automatically. For direct BibTeX, pick whichever granularity fits the citing context.

### Whole repository

```bibtex
@software{gupta2026zpm,
  author  = {Gupta, Dhruv},
  title   = {{zetesis-puremath}: A {Lean 4} pure-mathematics reservoir},
  year    = {2026},
  url     = {https://github.com/Zetetic-Dhruv/zetesis-puremath},
  license = {Apache-2.0},
  version = {main}
}
```

### By concept class

Each cluster stands alone; cite the one closest to the result you actually use.

```bibtex
@software{gupta2026zpm-measure,
  author  = {Gupta, Dhruv},
  title   = {Analytic measurability, {Choquet} capacity, and real-valued total variation in {Lean 4}},
  year    = {2026},
  url     = {https://github.com/Zetetic-Dhruv/zetesis-puremath/tree/main/ZPM/MeasureTheory},
  note    = {Part of zetesis-puremath; includes {Kechris 30.13} capacitability},
  license = {Apache-2.0}
}

@software{gupta2026zpm-information,
  author  = {Gupta, Dhruv},
  title   = {Real-valued {Kullback}--{Leibler}, binary {KL}, {Pinsker}'s inequality, and mutual information in {Lean 4}},
  year    = {2026},
  url     = {https://github.com/Zetetic-Dhruv/zetesis-puremath/tree/main/ZPM/InformationTheory},
  note    = {Part of zetesis-puremath; sharp-constant binary Pinsker + measure-theoretic form},
  license = {Apache-2.0}
}

@software{gupta2026zpm-probability,
  author  = {Gupta, Dhruv},
  title   = {Concentration, double-sample exchangeability, and finite-type {PMF} infrastructure in {Lean 4}},
  year    = {2026},
  url     = {https://github.com/Zetetic-Dhruv/zetesis-puremath/tree/main/ZPM/Probability},
  note    = {Part of zetesis-puremath; BoundedRandomVariable, ValidSplit, FintypePMF},
  license = {Apache-2.0}
}

@software{gupta2026zpm-decision,
  author  = {Gupta, Dhruv},
  title   = {Multiplicative weights update and approximate minimax for {Boolean}-matrix games in {Lean 4}},
  year    = {2026},
  url     = {https://github.com/Zetetic-Dhruv/zetesis-puremath/tree/main/ZPM/Probability/Decision},
  note    = {Part of zetesis-puremath; Freund--Schapire Hedge analysis with T = O(log N / eps^2)},
  license = {Apache-2.0}
}

@software{gupta2026zpm-rkhs,
  author  = {Gupta, Dhruv},
  title   = {Kernel mean embedding, {MMD}, and {HSIC} in {Lean 4}},
  year    = {2026},
  url     = {https://github.com/Zetetic-Dhruv/zetesis-puremath/tree/main/ZPM/Analysis/InnerProductSpace},
  note    = {Part of zetesis-puremath; includes IsCharacteristic and MMD zero-iff},
  license = {Apache-2.0}
}

@software{gupta2026zpm-combinatorics,
  author  = {Gupta, Dhruv},
  title   = {{Assouad}'s dual {VC} bound for binary matrices in {Lean 4}},
  year    = {2026},
  url     = {https://github.com/Zetetic-Dhruv/zetesis-puremath/tree/main/ZPM/Combinatorics},
  note    = {Part of zetesis-puremath; VCDim(M^T) <= 2^(d+1) - 1},
  license = {Apache-2.0}
}
```

For reproducibility, please pin to a specific commit hash when citing (replace `version = {main}` with the hash you used).

## License

Apache 2.0; see [LICENSE](./LICENSE).
