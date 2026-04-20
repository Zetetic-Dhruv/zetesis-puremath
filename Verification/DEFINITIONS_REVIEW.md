# Definitions Review

A literature review pinning every definition and headline theorem in
`zetesis-puremath` to its canonical source. Anyone who wants to verify
that the Lean 4 statements in this repository match the classical
mathematical literature can use this document as an index.

Cross-references below use the Lean declaration name (e.g.
`InformationTheory.binary_pinsker`); the full statement is available
via the blueprint at
<https://zetetic-dhruv.github.io/zetesis-puremath/blueprint/> or
directly in the source tree under [`ZPM/`](../ZPM/).

---

## Measure theory

### Analytic measurability

- `MeasureTheory.AnalyticSet.nullMeasurableSet`: analytic sets are
  universally null-measurable on Souslin spaces. Kechris,
  *Classical Descriptive Set Theory* (1995), Theorem 29.5; Bogachev,
  *Measure Theory* vol. II (2007), §7.4.11.
- `MeasureTheory.AnalyticSet.exists_isCompact_measureReal_gt`: inner
  regularity of finite Borel measures extended to analytic sets.
  Kechris 1995, Theorem 17.11.
- `MeasureTheory.AnalyticSet.compactCap_eq`: measure-as-capacity
  form of capacitability for analytic sets. Kechris 1995, Theorem
  30.13; Dellacherie–Meyer, *Probabilities and Potential A* (1978),
  III.50.

### Choquet capacity

- `MeasureTheory.IsChoquetCapacity`: the three-axiom definition
  (monotonicity, continuity from below, continuity from above on
  closed sets). Kechris 1995, Definition 30.1; Dellacherie–Meyer
  1978, III.1; Choquet, *Theory of Capacities*, Ann. Inst. Fourier 5
  (1955).
- `MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact`: **Choquet's
  capacitability theorem**: every analytic set is capacitable by its
  compact subsets. Kechris 1995, Theorem 30.13; Choquet 1955.
- `MeasureTheory.measure_isChoquetCapacity`: every Radon measure is
  a Choquet capacity. Dellacherie–Meyer 1978, III.7.

### Total variation

- `MeasureTheory.tvDistReal`: real-valued metric total variation
  distance (`sup over measurable sets`). Billingsley, *Probability
  and Measure* (1995), §3; Villani, *Optimal Transport* (2009), Ch. 1.
  This is the half-sup form; Pinsker's inequality below uses this
  convention.

### Baire-space cylinders

The cylinder infrastructure (`Cyl`, `Bnd`, `truncate`, and their
lemmas) reproduces the Baire-space `\mathbb{N}^\mathbb{N}` setup used
in the proof of Choquet's capacitability theorem. Source: Kechris
1995, §7.A (pages 37–38) and §30 (pages 230–232).

---

## Information theory

### Kullback–Leibler divergence (real-valued bridge)

- `InformationTheory.klDivReal`: real-valued specialization of
  Mathlib's `ENNReal`-valued `klDiv`. Matches the standard definition
  in Cover & Thomas, *Elements of Information Theory* (2006), §2.3.
- `InformationTheory.klDivReal_nonneg`: Gibbs' inequality.
  Cover–Thomas 2006, Theorem 2.6.3.
- `InformationTheory.klDivReal_eq_zero_iff`: equality in Gibbs.
  Cover–Thomas 2006, Theorem 2.6.3.

### Binary Kullback–Leibler and Pinsker

- `InformationTheory.klBin`: binary KL
  `p log(p/q) + (1-p) log((1-p)/(1-q))` with the standard
  `0 · log 0 = 0` convention. Cover–Thomas 2006, §2.3 eq. (2.26);
  Polyanskiy & Wu, *Information Theory: From Coding to Learning*
  (2025), §2.1.
- `InformationTheory.hasDerivAt_klBin_q`: derivative
  `∂_q klBin = (q−p)/(q(1−q))`. Polyanskiy & Wu 2025, §2.1 eq. (2.6);
  Boucheron, Lugosi & Massart, *Concentration Inequalities* (2013),
  §4.4.
- `InformationTheory.binary_pinsker`: **Pinsker's inequality in
  binary form with sharp constant 2**:
  `2(p-q)² ≤ klBin(p,q)`. Kullback, *A Lower Bound for Discrimination
  Information in Terms of Variation*, IEEE TIT 13 (1967);
  Cover–Thomas 2006, Lemma 11.6.1.
- `InformationTheory.klBin_le_klDivReal`: two-point data-processing
  inequality. Cover–Thomas 2006, Theorem 2.8.1; Csiszár, *Information-
  type measures of difference of probability distributions* (1967).
- `InformationTheory.pinsker_proof`: **Pinsker's inequality** in
  measure-theoretic form: `TV(P,Q) ≤ √(KL(P‖Q)/2)`. Cover–Thomas 2006,
  Theorem 11.6.1; Tsybakov, *Introduction to Nonparametric
  Estimation* (2009), Lemma 2.5; Polyanskiy & Wu 2025, Theorem 6.5.
- `InformationTheory.two_sq_le_neg_log` and `…_one_sub`: boundary
  Pinsker cases at `p ∈ {0,1}`. Csiszár & Körner, *Information
  Theory* (1981), Lemma 3.1; Fedotov, Harremoës & Topsøe,
  *Refinements of Pinsker's inequality*, IEEE TIT 49 (2003), §2.

### Mutual information

- `InformationTheory.mutualInformationReal`: real-valued mutual
  information as KL from joint to product-of-marginals.
  Cover–Thomas 2006, §2.3 Definition 2.28; Polyanskiy & Wu 2025, §3.1.
- `InformationTheory.mutualInformationReal_nonneg`: Cover–Thomas
  2006, Theorem 2.6.3.
- `InformationTheory.mutualInformationReal_eq_zero_iff_product`:
  MI vanishes iff the variables are independent. Cover–Thomas 2006,
  Theorem 2.6.5.

---

## Probability

### Concentration

- `ProbabilityTheory.BoundedRandomVariable`: a.e. bounded
  measurable random variable. Standard; compare
  Vershynin, *High-Dimensional Probability* (2018), §2.6.
- `ProbabilityTheory.chebyshev_majority_bound`: Chebyshev-via-majority
  bound for i.i.d. Boolean indicators. Boucheron–Lugosi–Massart
  2013, §2.1 (Popoviciu + Chebyshev composition).

### Exchangeability and double-sample

- `ProbabilityTheory.ExchangeableSample`, `ValidSplit`,
  `SplitMeasure`: double-sample / symmetrization setup.
  Vapnik & Chervonenkis, *On the Uniform Convergence of Relative
  Frequencies of Events to Their Probabilities*, Theory Probab.
  Appl. 16 (1971); Boucheron–Lugosi–Massart 2013, Chapter 12;
  Kallenberg, *Foundations of Modern Probability* (2021), §11.

### Finite-type PMF

- `ProbabilityTheory.FintypePMF`: real-valued, `Fintype`-indexed
  probability mass function. A specialization of the standard
  discrete PMF; see Levin, Peres & Wilmer, *Markov Chains and Mixing
  Times* (2017), §4.1.
- `ProbabilityTheory.FintypePMF.toPMF`: bridge to Mathlib's
  `ENNReal`-valued `PMF` via `ENNReal.ofReal`.
- `ProbabilityTheory.FintypePMF.tvDistance`: L¹ total-variation
  distance on discrete distributions.
  Levin–Peres–Wilmer 2017, Proposition 4.2.
- `ProbabilityTheory.FintypePMF.expectation_approx_of_tv`: transfer
  principle bounding the expectation gap by TV. Boucheron–Lugosi–
  Massart 2013, §4.1; Sason & Verdú, *f-divergence inequalities*,
  IEEE TIT 62 (2016).

---

## Decision theory: minimax and multiplicative weights

### Zero-sum games on Boolean matrices

- `ProbabilityTheory.boolGamePayoff`: expected payoff
  `Σ p(r) · [M r c]` for a mixed-row, pure-column Boolean-matrix
  game. Freund & Schapire, *Adaptive Game Playing Using
  Multiplicative Weights*, Games Econ. Behav. 29 (1999).

### Multiplicative weights update

- `ProbabilityTheory.MWUConfig`,
  `ProbabilityTheory.mwuUpdateWeights`: the Freund–Schapire
  Hedge algorithm in `β = (1 − η)` form. Freund & Schapire,
  *A Decision-Theoretic Generalization of On-Line Learning…*,
  JCSS 55 (1997); Arora, Hazan & Kale, *The Multiplicative Weights
  Update Method*, Theory of Computing 8 (2012).
- `ProbabilityTheory.mwu_weight_eq_pow_hitCount`: closed-form
  `w_T(c) = w_0(c) · (1−η)^{hitCount_T(c)}`. Freund–Schapire 1997,
  eq. (2).
- `ProbabilityTheory.potential_one_step_bound`: one-step potential
  contraction `Φ_{t+1} ≤ Φ_t · (1 − η v)`. Arora–Hazan–Kale 2012,
  Corollary 2.2.
- `ProbabilityTheory.mwu_potential_T_bound`: `T`-step bound
  `Φ_T ≤ |C| · (1 − η v)^T`. Arora–Hazan–Kale 2012, Theorem 2.1.
- `ProbabilityTheory.mwu_approx_minimax`: **approximate minimax via
  MWU**: with `η = ε/4`, `T = ⌈16 log N / ε²⌉` rounds suffice to
  produce a mixed-row strategy with payoff at least `v − ε` against
  every pure column. Freund–Schapire, *Adaptive Game Playing*
  (1999), Theorem 3; Arora–Hazan–Kale 2012, §3.1.
- `ProbabilityTheory.covering_minimax`,
  `finite_approx_minimax`: existential covering-based minimax; the
  logical counterpart to the constructive MWU bound.

---

## Reproducing-kernel Hilbert spaces

### RKHS interface and bounded kernels

The repository consumes Mathlib's
`Mathlib.Analysis.InnerProductSpace.Reproducing` (`RKHS 𝕜 H X V`
class) directly; no redefinition. The reproducing identity
`f(x) = ⟨k_x, f⟩` is Aronszajn, *Theory of Reproducing Kernels*,
Trans. AMS 68 (1950).

- `BoundedKernel`: uniform bound on `‖k_x‖`. Steinwart &
  Christmann, *Support Vector Machines* (2008), §4.2.
- `norm_apply_le_bound_mul_norm`: Cauchy–Schwarz form of the RKHS
  evaluation bound. Berlinet & Thomas-Agnan, *Reproducing Kernel
  Hilbert Spaces in Probability and Statistics* (2004), Theorem 1
  (p. 19); Steinwart & Christmann 2008, Theorem 4.23.
- `rkhs_eval_eq_inner`: reproducing identity. Aronszajn 1950.
- `continuous_rkhs_apply`: continuity of the feature map implies
  continuity of all RKHS functions. Steinwart & Christmann 2008,
  Lemma 4.29.

### Kernel mean embedding

- `kernelMeanEmbedding`: `μ_P := ∫ k_x dP(x)`. Smola, Gretton, Song
  & Schölkopf, *A Hilbert Space Embedding for Distributions*, ALT
  (2007), Definition 1.
- `kernelMeanEmbedding_reproducing`: `⟨μ_P, f⟩ = ∫ f dP`. Smola et
  al. 2007, eq. (4); Gretton, Borgwardt, Rasch, Schölkopf & Smola,
  *A Kernel Two-Sample Test*, JMLR 13 (2012), eq. (2)–(3).
- `kernelMeanEmbedding_norm_le`: `‖μ_P‖ ≤ C` for probability
  measures. Gretton et al. 2012, Lemma 4.

### Maximum Mean Discrepancy

- `mmdSq`: squared MMD `‖μ_P − μ_Q‖²`. Gretton et al. 2012,
  Definition 2.
- `IsCharacteristic`: injectivity of the kernel mean embedding.
  Fukumizu, Gretton, Sun & Schölkopf, *Kernel Measures of Conditional
  Dependence*, NeurIPS (2008); Sriperumbudur, Gretton, Fukumizu,
  Schölkopf & Lanckriet, *Hilbert Space Embeddings and Metrics on
  Probability Measures*, JMLR 11 (2010), Definition 6.
- `mmdSq_zero_iff`: MMD² metrizes equality under characteristic
  kernels. Sriperumbudur et al. 2010, Theorem 8; Gretton et al. 2012,
  Theorem 5.

### Hilbert–Schmidt Independence Criterion

- `hsicDef`: HSIC as `MMD²(P_{XY}, P_X ⊗ P_Y)`. Modern unified
  formulation: Sejdinovic, Sriperumbudur, Gretton & Fukumizu,
  *Equivalence of distance-based and RKHS-based statistics in
  hypothesis testing*, Annals of Statistics 41 (2013), Theorem 24.
  Original Hilbert–Schmidt-norm form: Gretton, Bousquet, Smola &
  Schölkopf, *Measuring Statistical Dependence with Hilbert–Schmidt
  Norms*, ALT (2005).
- `hsicDef_zero_iff_independent`: HSIC vanishes iff the variables
  are independent (under characteristic kernels). Gretton et al.
  2005, Theorem 4; Sriperumbudur et al. 2010, §4.2.

---

## Combinatorics: VC dimension and its dual

### Binary-matrix shattering

- `BinaryMatrix`: `Fin m → Fin n → Bool`. Type-definitionally equal
  to `Matrix (Fin m) (Fin n) Bool` under Mathlib's convention.
- `BinaryMatrix.shatters`, `toFinsetFamily`: shattering in the
  Vapnik–Chervonenkis sense. Vapnik & Chervonenkis 1971; Sauer,
  *On the density of families of sets*, J. Comb. Theory Ser. A 13
  (1972).
- `BinaryMatrix.shatters_iff`: equivalence with Mathlib's
  `Finset.Shatters`.

### Sauer–Shelah bound

- `BinaryMatrix.card_toFinsetFamily_le`: `|F| ≤ Σ_{k≤d} C(n,k)`
  when `VCDim(F) ≤ d`. Sauer 1972; Shelah, *A combinatorial problem*,
  Pacific J. Math. 41 (1972); Vapnik–Chervonenkis 1971. Modern
  exposition: Matoušek, *Lectures on Discrete Geometry* (2002),
  §10.3 Lemma 10.3.3; Mohri, Rostamizadeh & Talwalkar, *Foundations
  of Machine Learning* (2018), §3.3.

### Dual VC dimension (Assouad)

- `BinaryMatrix.transpose_shatters_imp_shatters`: bitstring-coding
  step: if `Mᵀ` shatters a set of size ≥ `2^{d+1}`, then `M`
  shatters a set of size `d + 1`. Assouad, *Densité et dimension*,
  Ann. Inst. Fourier 33 (1983), Theorem 2.13; Dudley, *Uniform
  Central Limit Theorems* (1999), Theorem 4.2.
- `BinaryMatrix.assouad_transpose_vcDim`: **Assouad's dual VC
  bound**: `VCDim(Mᵀ) ≤ 2^{d+1} − 1` when `VCDim(M) ≤ d`.
  Assouad 1983, Theorem 2.13; Matoušek 2002, §10.3 Lemma 10.3.3.

---

## Selected references

- Aronszajn, N. (1950). *Theory of reproducing kernels*. Trans. Amer. Math. Soc. 68.
- Assouad, P. (1983). *Densité et dimension*. Ann. Inst. Fourier 33(3).
- Arora, S., Hazan, E., Kale, S. (2012). *The Multiplicative Weights Update Method*. Theory of Computing 8.
- Berlinet, A., Thomas-Agnan, C. (2004). *Reproducing Kernel Hilbert Spaces in Probability and Statistics*. Kluwer.
- Billingsley, P. (1995). *Probability and Measure*. Wiley.
- Bogachev, V. I. (2007). *Measure Theory* (vol. II). Springer.
- Boucheron, S., Lugosi, G., Massart, P. (2013). *Concentration Inequalities*. Oxford University Press.
- Choquet, G. (1955). *Theory of capacities*. Ann. Inst. Fourier 5.
- Cover, T. M., Thomas, J. A. (2006). *Elements of Information Theory* (2nd ed.). Wiley.
- Csiszár, I. (1967). *Information-type measures of difference of probability distributions*. Studia Sci. Math. Hungar. 2.
- Csiszár, I., Körner, J. (1981). *Information Theory*. Academic Press.
- Dellacherie, C., Meyer, P.-A. (1978). *Probabilities and Potential A*. North-Holland.
- Dudley, R. M. (1999). *Uniform Central Limit Theorems*. Cambridge University Press.
- Fedotov, A. A., Harremoës, P., Topsøe, F. (2003). *Refinements of Pinsker's inequality*. IEEE TIT 49.
- Freund, Y., Schapire, R. E. (1997). *A Decision-Theoretic Generalization of On-Line Learning…*. JCSS 55.
- Freund, Y., Schapire, R. E. (1999). *Adaptive Game Playing Using Multiplicative Weights*. Games Econ. Behav. 29.
- Fukumizu, K., Gretton, A., Sun, X., Schölkopf, B. (2008). *Kernel Measures of Conditional Dependence*. NeurIPS.
- Gretton, A., Borgwardt, K. M., Rasch, M. J., Schölkopf, B., Smola, A. (2012). *A Kernel Two-Sample Test*. JMLR 13.
- Gretton, A., Bousquet, O., Smola, A., Schölkopf, B. (2005). *Measuring Statistical Dependence with Hilbert–Schmidt Norms*. ALT.
- Kallenberg, O. (2021). *Foundations of Modern Probability* (3rd ed.). Springer.
- Kechris, A. S. (1995). *Classical Descriptive Set Theory*. Springer.
- Kullback, S. (1967). *A Lower Bound for Discrimination Information in Terms of Variation*. IEEE TIT 13.
- Levin, D. A., Peres, Y., Wilmer, E. L. (2017). *Markov Chains and Mixing Times* (2nd ed.). AMS.
- Matoušek, J. (2002). *Lectures on Discrete Geometry*. Springer.
- Mohri, M., Rostamizadeh, A., Talwalkar, A. (2018). *Foundations of Machine Learning*. MIT Press.
- Polyanskiy, Y., Wu, Y. (2025). *Information Theory: From Coding to Learning*. Cambridge University Press.
- Sason, I., Verdú, S. (2016). *f-divergence inequalities*. IEEE TIT 62.
- Sauer, N. (1972). *On the density of families of sets*. J. Comb. Theory Ser. A 13.
- Sejdinovic, D., Sriperumbudur, B., Gretton, A., Fukumizu, K. (2013). *Equivalence of distance-based and RKHS-based statistics in hypothesis testing*. Annals of Statistics 41.
- Shelah, S. (1972). *A combinatorial problem; stability and order for models and theories in infinitary languages*. Pacific J. Math. 41.
- Smola, A., Gretton, A., Song, L., Schölkopf, B. (2007). *A Hilbert Space Embedding for Distributions*. ALT.
- Sriperumbudur, B., Gretton, A., Fukumizu, K., Schölkopf, B., Lanckriet, G. (2010). *Hilbert Space Embeddings and Metrics on Probability Measures*. JMLR 11.
- Steinwart, I., Christmann, A. (2008). *Support Vector Machines*. Springer.
- Tsybakov, A. B. (2009). *Introduction to Nonparametric Estimation*. Springer.
- Vapnik, V. N., Chervonenkis, A. Ya. (1971). *On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities*. Theory Probab. Appl. 16.
- Vershynin, R. (2018). *High-Dimensional Probability*. Cambridge University Press.
- Villani, C. (2009). *Optimal Transport: Old and New*. Springer.
