/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.ProductMeasure

/-!
# ℝ-valued KL divergence (bridge to Mathlib's ℝ≥0∞-valued `klDiv`)

`klDivReal P Q := if P ≪ Q then ∫ log (dP/dQ) dP else 0`, the real-valued
Kullback–Leibler divergence between two measures. For probability
measures with `P ≪ Q` it equals `(InformationTheory.klDiv P Q).toReal`,
bridging Mathlib's `ℝ≥0∞`-valued KL to a real-valued arithmetic layer
where `linarith` / `nlinarith` / `field_simp` compose naturally. This is
the same proof-engineering specialization as `FintypePMF` relative to
`Mathlib.PMF`, documented in `CHARTER.md` under "Duplicate rule
exception."

## Main results

- `klDivReal_eq_toReal_klDiv`: bridge to Mathlib's KL for probability
  measures with absolute continuity.
- `klDivReal_nonneg`: nonnegativity for probability measures.
- `klDivReal_eq_zero_iff`: KL = 0 ↔ P = Q (under absolute continuity and
  finite KL).
-/

noncomputable section

open MeasureTheory InformationTheory Real Classical

namespace InformationTheory

variable {α : Type*} [MeasurableSpace α]

/-- ℝ-valued KL divergence. Returns 0 when `P` is not absolutely continuous
with respect to `Q` (by convention; the `ℝ≥0∞`-valued `klDiv` returns `⊤`
in that case). -/
def klDivReal (P Q : Measure α) : ℝ :=
  if P.AbsolutelyContinuous Q then
    ∫ x, Real.log (P.rnDeriv Q x).toReal ∂P
  else 0

/-- The integrand `log ((P.rnDeriv Q x).toReal)` is definitionally Mathlib's
log-likelihood ratio `llr P Q x`. -/
lemma integrand_eq_llr (P Q : Measure α) :
    (fun x => Real.log (P.rnDeriv Q x).toReal) = llr P Q := rfl

/-- For probability measures with `P ≪ Q`, the ℝ-valued KL equals
`(Mathlib.klDiv P Q).toReal`. Both measures have total mass 1, so the
Mathlib correction term vanishes. -/
theorem klDivReal_eq_toReal_klDiv
    (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q) :
    klDivReal P Q = (InformationTheory.klDiv P Q).toReal := by
  unfold klDivReal
  rw [if_pos hac, integrand_eq_llr]
  rw [toReal_klDiv_of_measure_eq hac]
  simp [IsProbabilityMeasure.measure_univ]

/-- ℝ-valued KL is nonnegative for probability measures. -/
theorem klDivReal_nonneg
    (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    0 ≤ klDivReal P Q := by
  by_cases hac : P.AbsolutelyContinuous Q
  · rw [klDivReal_eq_toReal_klDiv P Q hac]
    exact ENNReal.toReal_nonneg
  · show 0 ≤ klDivReal P Q
    unfold klDivReal
    simp [if_neg hac]

/-- For probability measures with `P ≪ Q` and finite KL, `klDivReal P Q = 0`
iff `P = Q`. The finite-KL hypothesis is essential: a non-integrable
log-likelihood ratio makes the Bochner integral collapse to 0 even when
`P ≠ Q`. -/
theorem klDivReal_eq_zero_iff
    (P Q : Measure α)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hac : P.AbsolutelyContinuous Q)
    (hfin : InformationTheory.klDiv P Q ≠ ⊤) :
    klDivReal P Q = 0 ↔ P = Q := by
  rw [klDivReal_eq_toReal_klDiv P Q hac]
  constructor
  · intro h
    have h0 : InformationTheory.klDiv P Q = 0 := by
      rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at h
    exact InformationTheory.klDiv_eq_zero_iff.mp h0
  · intro h
    rw [h, InformationTheory.klDiv_self]
    simp

end InformationTheory

end
