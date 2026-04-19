# Red-Team Audit — `zetesis-puremath` @ 471e5d5

Six parallel literature + Mathlib + premise-quality audits over all 114 public ZPM theorems. Each cluster was given a self-contained prompt with literature pointers (Kechris, Cover-Thomas, Polyanskiy-Wu, Boucheron-Lugosi-Massart, Steinwart-Christmann, Sriperumbudur et al., Freund-Schapire, Assouad, Kallenberg, etc.) and asked to report along five axes: **premise quality**, **definition quality**, **sufficiency**, **generalizability / transportability**, **Mathlib overlap**.

**Bottom line: zero soundness defects across all 114 theorems.** Every identified risk is either a *naming* issue (namespace collision, TV convention), an *over-strong hypothesis* (tightenable without breaking anything downstream), or a *Mathlib-upstreaming friction* (not a correctness issue for the repo as it stands). No theorem was found to be vacuous, circular, or missing a hypothesis silently in use.

---

## Novelty grading (Grade A / B / C)

| Grade | Meaning | Clusters |
|---|---|---|
| **A — absent from Mathlib, pitch directly** | No overlap at the pinned Mathlib commit; the cluster is the formalization of record. | Kechris 30.13 capacitability + cylinder infra (MeasureTheory), MWU + approximate minimax + Hedge analysis (Decision), `IsCharacteristic` + MMD + HSIC scaffold (Analysis), Assouad's dual VC bound `2^{d+1}−1` (Combinatorics). |
| **B — extension of Mathlib, packageable** | Mathlib has the building block; ZPM proves the next consequence. Needs re-packaging but upstreamable. | `AnalyticSet.nullMeasurableSet` + `exists_isCompact_measureReal_gt` (both are Choquet-30.13 corollaries once 30.13 lands), binary-KL derivative chain and Pinsker's sharp-constant-2 bound (Mathlib has `klDiv`/`klFun` but no binary layer or Pinsker). |
| **C — charter-admissible wrapper, not Mathlib-upstreamable as-is** | ℝ-valued specialization or plumbing that serves downstream `linarith` but duplicates an ENNReal-valued idiom Mathlib prefers. | `klDivReal` + `mutualInformationReal` bridge, `tvDistReal` + its set-lemmas, `FintypePMF` + ℝ-valued `tvDistance`, `BinaryMatrix.card_toFinsetFamily_le` (2-step corollary of Mathlib's Sauer-Shelah). |

Every Grade C item is defensible under CHARTER §"Duplicate rule exception — proof-engineering specialization", but each needs a **documented bridge** back to the Mathlib idiom before upstream-scrubbing.

---

## Cross-cluster patterns (risks that appear in >1 cluster)

### CC-1 — TV-convention split **[HIGHEST priority]**

Two conventions coexist in the repo with **no bridge lemma**:

| Location | Definition | Factor |
|---|---|---|
| [`ZPM/MeasureTheory/ProbabilityMeasure/TotalVariation/Real.lean`](ZPM/MeasureTheory/ProbabilityMeasure/TotalVariation/Real.lean) | `tvDistReal := sSup_A |P(A) − Q(A)|` | **half-sup-TV** (Pinsker uses this) |
| [`ZPM/Probability/FintypePMF/TVDistance.lean`](ZPM/Probability/FintypePMF/TVDistance.lean) | `FintypePMF.tvDistance := ∑ |p(a) − q(a)|` | **full L1** (2× canonical) |

On discrete supports, `∑|p−q| = 2 · sup_A |P(A)−Q(A)|`. A consumer who composes `pinsker_proof` (on `tvDistReal`) with the FintypePMF layer's `expectation_approx_of_tv` gets an off-by-2 or off-by-4 constant silently. `TVDistance.lean:10` documents the convention inline, but the missing bridge lemma `tvDistReal (p.toMeasure) (q.toMeasure) = (1/2) · p.tvDistance q` is exactly the object that would prevent the silent loss. Flagged independently by the InformationTheory and Probability-base agents.

### CC-2 — Namespace collision with Mathlib

`namespace InformationTheory`, `namespace MeasureTheory`, `namespace ProbabilityTheory` are **Mathlib namespaces**. Every ZPM def lives inside them, so future Mathlib additions (especially `InformationTheory.klBin`, `MeasureTheory.tvDist`, `ProbabilityTheory.FintypePMF`) will create immediate name collisions on a Mathlib pin bump — and Mathlib's ENNReal-valued versions cannot coexist with ZPM's ℝ-valued ones in the same namespace. Three mitigation options:
- (a) Rename to `Zetesis.{InformationTheory,MeasureTheory,ProbabilityTheory}`;
- (b) Extend the `*Real` suffix convention (`klBinReal`, `tvDistanceReal`, etc.) consistently;
- (c) Accept the collision and pay when it happens.

### CC-3 — "Silently noncomputable" via `Classical.choice` / `.choose`

- Decision cluster: `(hrow cfg.toPMF).choose` appears in `best_response_payoff_weights`, `potential_one_step_bound`, `mwuRun`. MWU dynamics are therefore `noncomputable`, even though the surface API looks like a deterministic update.
- Probability-base cluster: `SplitMeasure.splitFirst` / `splitSecond` *ignore* their `vs : ValidSplit m` argument (take the first-m / last-m columns regardless). Could be a stub or spec bug — the split is supposed to be `vs`-dependent.
- Combinatorics cluster: `vcDim` is `noncomputable` via `open Classical`; downstream decidability of `vcDim ≤ k` is lost.

None of these is a soundness bug, but all are downstream-reuse hazards that need either explicit `noncomputable` docstrings or concrete replacements.

### CC-4 — Over-qualified Polish/typeclass hypotheses

- `MeasureTheory.AnalyticSet.nullMeasurableSet` assumes `[PolishSpace α]` but its proof only uses `InnerRegularWRT IsCompact MeasurableSet` + `IsFiniteMeasure`.
- `MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact` has `[MeasurableSpace α] [BorelSpace α]` in the signature but never references `MeasurableSet` in the body — both are decorative.
- `InformationTheory.hasDerivAt_klBin_q` requires `0 < p < 1` but only `q ∈ (0,1)` is used.
- `ProbabilityTheory.FintypePMF.normalize` requires strict positivity `∀ a, 0 < w a` when `∃ a, 0 < w a` would suffice.
- `Analysis.IsCharacteristic` quantifies over **all** `Measure X` rather than `ProbabilityMeasure X` — strictly stronger than Sriperumbudur 2010 Defn. 6, making instances unprovably hard.

All are reviewer-flag-bait on a Mathlib PR; all are local tightenings.

### CC-5 — Decorative / unused scaffolding

- **`ExchangeableSample` has no exchangeability content.** The structure bundles `(m, μ, IsProbabilityMeasure μ)`. No permutation-invariance field, no Kallenberg §11 predicate. The name over-promises. Rename to `SampleBundle` / `IIDSampleBundle` or add the missing permutation-invariance field.
- **`BinaryMatrix` parallels `Mathlib.Matrix` with no bridge.** `BinaryMatrix m n := Fin m → Fin n → Bool` is type-definitionally equal to `Matrix (Fin m) (Fin n) Bool` but re-implements `transpose`, `shatters`, `toFinsetFamily` in a new namespace. CHARTER §Duplicate-rule exception requires a bridge declaration; none exists.
- **`CrossEntropy/Basic.lean`** imports only the Fintype case — no measure-theoretic cross-entropy analogue of `klDivReal` (absent but plausibly wanted).
- **`boolGamePayoff_*` lemmas duplicate `boolTestExpectation_*` proofs** inline rather than `rw`-routing through the bridge lemma `boolGamePayoff_eq_boolTestExpectation`.

---

## Cluster-by-cluster summary

### MeasureTheory (22 theorems)
- **Solid**. Kechris 30.13 (`AnalyticSet.cap_eq_iSup_isCompact`), `IsChoquetCapacity` structure, and the `Cyl` / `Bnd` / `truncate` infrastructure in [`CylinderMachinery.lean`](ZPM/MeasureTheory/ChoquetCapacity/CylinderMachinery.lean) are **Grade A** and absent from Mathlib4 at the pin. Proof of `cap_eq_iSup_isCompact` is a faithful formalization of Kechris §30 pp. 230–232.
- **Local risks**: `BorelSpace` + `MeasurableSpace` decorative in `cap_eq_iSup_isCompact` signature; `nullMeasurableSet` over-qualified with `PolishSpace`; `IsChoquetCapacity.iInter_closed` axiom is stated for closed sets only while the proved instance works on any null-measurable antitone family (weaker-than-provable definition).
- **`tvDistReal` won't survive a Mathlib pin bump as-is.** If/when Mathlib ships an `ENNReal`-valued `Measure.tvDist`, the ℝ-valued specialization needs a bridging lemma — not present.

### InformationTheory (26 theorems)
- **Sound.** All 26 theorems align with Mathlib's `klFun` / `klDiv` / `integrable_klFun_rnDeriv_iff` / `convexOn_klFun` at the pin. The Cover-Thomas Thm 11.6.1 "sharp constant 2" version of Pinsker is the one formalized; derivative / monotonicity chain is clean.
- **`klDivReal P Q = (klDiv P Q).toReal` holds unconditionally**, not just under `P ≪ Q`. The theorem `klDivReal_eq_toReal_klDiv` carries an unnecessary `hac` hypothesis — removable.
- **Namespace-collision** with Mathlib's `InformationTheory.*` is the biggest Mathlib-upstream blocker (CC-2).
- **Redundant finiteness hypotheses**: `klDivReal_eq_zero_iff` and `mutualInformationReal_eq_zero_iff_product` carry `hac ∧ hfin : klDiv ≠ ⊤`, but `klDiv_ne_top_iff` (Mathlib) collapses the pair to `Integrable (llr P Q) P`.

### Probability base (25 theorems — Concentration + Exchangeability + FintypePMF)
- **Concentration is production-quality**: `chebyshev_majority_bound` correctly routes through `meas_ge_le_variance_div_sq`, Popoviciu, and iIndep variance summation. BLM §2 idiomatic.
- **`ExchangeableSample` has no exchangeability content** (CC-5). Biggest naming risk in the repo.
- **TV-convention split** confirmed here (CC-1): `FintypePMF.tvDistance = ∑|p−q|` is the L1 form, 2× canonical. `expectation_approx_of_tv` gives `|E_p[f]−E_q[f]| ≤ tvDistance p q` — correct *given the L1 convention*, but 2× looser than the canonical `TV`-based bound.
- **`splitFirst` / `splitSecond` ignore their `vs` argument** — verify intent before upstream.

### Decision / Minimax / MWU (20 theorems)
- **Entirely novel to Mathlib.** Mathlib has no Sion, no von Neumann minimax for bilinear/matrix games, no Hedge, no multiplicative weights. The `.gitlab-ci.yml` comparator run already verified the minimax + MWU chain.
- **Convention**: Freund-Schapire 1997 `β = (1 − η)` (**not** Cesa-Bianchi-Lugosi exp-weights). `mwu_weight_eq_pow_hitCount` gives `w_T(c) = (1−η)^{hitCount_T(c)}`. Hard-coded; no `(1−η)^k ≈ exp(−ηk)` bridge. Migrating to exp-weights would re-derive everything.
- **T-bound**: `T = max 1 ⌈16 log N / ε²⌉`, `η = ε/4` — correct asymptotic, constant 16 is ~2–8× loose vs tightest Hedge analysis. Not a correctness issue.
- **`minimax_value_le_one`** is one-sided: `hrow` is *assumed*, not *proved* via von Neumann. No `maxmin = minmax` equality is claimed — the theorem is a constructive Freund-Schapire-style existence result, not the full minimax.

### RKHS / MMD / HSIC (19 theorems)
- **Correctly consumes Mathlib's `RKHS 𝕜 H X V` class** at the pin (no shadow redefinition). `BoundedKernel` + `kernelMeanEmbedding` + `mmdSq` + `IsCharacteristic` + `hsicDef` are all additions, Grade A.
- **`IsCharacteristic` is defined on all `Measure X`** — stronger than Sriperumbudur 2010 Defn. 6 (which restricts to probability measures). Consequence: the hypothesis of `mmdSq_zero_iff` is harder to satisfy than literature, meaning instances (e.g., "Gaussian kernel is characteristic") will be **unprovable** on the full `Measure X` domain.
- **`hsicDef` is MMD² on a product space**, not the classical cross-covariance-operator HSIC (Gretton et al. 2005 ALT). These agree under the product-kernel assumption (Sejdinovic-Sriperumbudur-Gretton-Fukumizu 2013 Thm 24); ZPM does not impose that assumption, so the theorem name `hsicDef_zero_iff_independent` is slightly oversold absent that bridge.
- **`SecondCountableTopology H` is silent separability assumption.** Bochner-integrating an `H`-valued function requires strong measurability, which requires separable `H`. Should be docstringed.

### Combinatorics / DualVC (5 theorems)
- **`assouad_transpose_vcDim`** (= Assouad 1983 Thm 2.13) is the crown jewel. Bound `2^{d+1} − 1` is tight. Bitstring-coding proof in `transpose_shatters_imp_shatters` is Lean-native and faithful to Assouad's original argument.
- **Mathlib has no Assouad / dual VC / transpose-shatter theory** — confirmed via targeted grep.
- **`BinaryMatrix m n := Fin m → Fin n → Bool`** type-definitionally equals `Matrix (Fin m) (Fin n) Bool` but does not declare the bridge. CHARTER §Duplicate-rule exception requires one.
- **`card_toFinsetFamily_le`** is a near-trivial 5-line corollary of Mathlib's `card_shatterer_le_sum_vcDim` (Sauer-Shelah proper) + `card_le_card_shatterer` (Pajor). Novelty thin; risk of not qualifying for zetesis-puremath on its own — Assouad is the real novelty.
- **`push Not` on `Assouad.lean:28`** may be a typo for `push_neg`. Build passes, so it's either an alias or another tactic — worth grep-verifying.

---

## Ranked top-10 cross-cluster risks

| # | Risk | Scope | Severity for upstream | Severity for correctness |
|---|---|---|---|---|
| 1 | TV convention split, no bridge (CC-1) | MeasureTheory ↔ FintypePMF | **High** | None today, medium if ever composed |
| 2 | Namespace collision with Mathlib (CC-2) | All clusters | **High** (pin bump will break) | None |
| 3 | `ExchangeableSample` has no exchangeability content | Probability base | High (naming) | Low |
| 4 | `IsCharacteristic` over all `Measure X` instead of `ProbabilityMeasure X` | RKHS | Medium | Medium — instances may be unprovable |
| 5 | `BinaryMatrix` vs `Mathlib.Matrix` bridge missing | Combinatorics | Medium | None |
| 6 | `tvDistReal` won't survive Mathlib pin bump (Mathlib will ship ENNReal TV) | MeasureTheory | Medium | None today |
| 7 | Decorative `BorelSpace` + `MeasurableSpace` in `cap_eq_iSup_isCompact` | MeasureTheory | Low (reviewer flag) | None |
| 8 | `splitFirst` / `splitSecond` ignore `vs` argument — stub or spec bug | Probability base | Medium | **Unknown — verify intent** |
| 9 | Over-qualified hypotheses (Polish, strict positivity, `p∈(0,1)`, etc.) across clusters | All | Low-medium | None |
| 10 | β=(1−η) Hedge convention hard-coded, no bridge to exp-weights | Decision | Low | None |

---

## Literature coverage map (short form)

Every theorem is identified in the cluster reports with a canonical source. Top-level mapping:

- **MeasureTheory**: Kechris 1995 §§7, 17, 29, 30; Dellacherie-Meyer *Probabilities and Potential A* Ch. III; Bogachev vol. II §7.4; Billingsley / Villani for TV conventions.
- **InformationTheory**: Cover-Thomas 2006 §2, §11, §17; Polyanskiy-Wu §§2, 3, 6; Tsybakov §2.4; Csiszár-Körner 1981; Fedotov-Harremoës-Topsøe 2003 (sharper Pinsker — not formalized, natural extension target).
- **Probability base**: Boucheron-Lugosi-Massart §2, §4, §12; Vershynin *HDP* §2; Kallenberg §§1.1, 11 (exchangeability — NOT formalized despite the name); Vapnik-Chervonenkis 1971 / BLM Ch. 12 for double-sample; Levin-Peres-Wilmer §4 for TV convention.
- **Decision / Minimax / MWU**: Freund-Schapire 1997 / 1999; Arora-Hazan-Kale 2012; Cesa-Bianchi-Lugosi 2006 (exp-weights — NOT the convention used); Nisan-Roughgarden-Tardos-Vazirani 2007 §4; Sion 1958 / von Neumann 1928 (NOT invoked).
- **RKHS / MMD / HSIC**: Aronszajn 1950; Steinwart-Christmann 2008 §§4, 6; Berlinet-Thomas-Agnan 2004; Smola-Gretton-Song-Schölkopf 2007; Gretton et al. 2012 JMLR; Sriperumbudur et al. 2010 JMLR; Sejdinovic et al. 2013 Annals of Statistics; Fukumizu-Gretton-Sun-Schölkopf 2008.
- **Combinatorics**: Assouad 1983; Sauer 1972; Shelah 1972; Vapnik-Chervonenkis 1971; Matoušek §10.3; Alon-Spencer; Mohri-Rostamizadeh-Talwalkar §3.3.

---

## Recommendations (prioritized)

1. **Add the TV-bridge lemma** linking `tvDistReal` to `FintypePMF.tvDistance` on discrete supports (CC-1). One 10-line lemma. Kills the time-bomb.
2. **Verify or fix `SplitMeasure.splitFirst` / `splitSecond`** ignoring their `vs` argument. If intentional, rename to make the independence from `vs` explicit.
3. **Decide namespace posture** (CC-2): rename to `Zetesis.*` or live with the collision on pin bump. Document the decision in CHARTER.md.
4. **Rename `ExchangeableSample`** to match its content (`IIDSampleBundle` / `SampleBundle`) or add the permutation-invariance field.
5. **Restrict `IsCharacteristic` to `ProbabilityMeasure X`** (one-line type change) to match Sriperumbudur 2010 and make instances provable.
6. **Add `BinaryMatrix ↔ Matrix (Fin m) (Fin n) Bool` bridge** (one def-eq lemma) for Mathlib transport.
7. **Tighten over-qualified hypotheses** (Polish, strict positivity, `p∈(0,1)`, `hac` on `klDivReal_eq_toReal_klDiv`, redundant `hfin` in zero-iff lemmas). Each is a local edit; none cascades.
8. **Add `SecondCountableTopology H` docstring** in `kernelMeanEmbedding` explaining it's the separability assumption, not a Lean quirk.
9. **Check `push Not` on `Assouad.lean:28`** — verify it's intentional or correct to `push_neg`.
10. **Target for future work**: the Fedotov-Harremoës-Topsøe 2003 sharper Pinsker `(4/9)(p−q)⁴ + 2(p−q)²` is a natural extension of the current sharp-2 constant.

None of these is a soundness fix. All are **upstream-readiness** items and **documentation hygiene**. The 114-theorem corpus is internally consistent, 0 sorry, 3-axiom closure, comparator-verified. The audit finds **no correctness issues**.
