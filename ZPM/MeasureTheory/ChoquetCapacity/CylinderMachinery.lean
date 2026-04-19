/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.Sequences
import Mathlib.Topology.Metrizable.Basic

/-!
# Cylinder machinery for the Choquet capacitability proof

Pure combinatorics / topology on `ℕ → ℕ`: cylinder sets `Cyl N n`, bounded
sets `Bnd N`, truncation, and the key compactness lemma
`iInter_closure_image_cyl_eq` that says the intersection of closures of
cylinder images equals the compact image.

This file is infrastructure for `Capacitability.lean`.
-/

open MeasureTheory Set Filter Topology

/-- Cylinder set: `{g : ℕ → ℕ | ∀ i ≤ n, g i ≤ N i}`. -/
abbrev Cyl (N : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {g | ∀ i, i ≤ n → g i ≤ N i}

/-- Bounded functions set: `{g : ℕ → ℕ | ∀ i, g i ≤ N i}`. -/
abbrev Bnd (N : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {g | ∀ i, g i ≤ N i}

lemma isCompact_bnd (N : ℕ → ℕ) : IsCompact (Bnd N) := by
  have : Bnd N = Set.pi Set.univ (fun i => Set.Iic (N i)) := by
    ext g
    simp only [Bnd, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic]
  rw [this]
  exact isCompact_univ_pi fun i => (Set.finite_Iic (N i)).isCompact

lemma bnd_subset_cyl (N : ℕ → ℕ) (n : ℕ) : Bnd N ⊆ Cyl N n :=
  fun _ hg i _ => hg i

lemma cyl_succ_eq (N : ℕ → ℕ) (n : ℕ) :
    Cyl N n = ⋃ k : ℕ, (Cyl N n ∩ {g | g (n + 1) ≤ k}) := by
  ext g; simp only [Cyl, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
  exact ⟨fun h => ⟨g (n + 1), h, le_refl _⟩, fun ⟨_, h, _⟩ => h⟩

lemma monotone_cyl_split (N : ℕ → ℕ) (n : ℕ) :
    Monotone (fun k => Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k}) := by
  intro a b hab x ⟨hx1, hx2⟩
  exact ⟨hx1, le_trans hx2 hab⟩

lemma cyl_inter_eq_cyl_update (N : ℕ → ℕ) (n k : ℕ) :
    Cyl N n ∩ {g : ℕ → ℕ | g (n + 1) ≤ k} = Cyl (Function.update N (n + 1) k) (n + 1) := by
  ext g
  simp only [Cyl, Set.mem_inter_iff, Set.mem_setOf_eq, Function.update]
  constructor
  · rintro ⟨hg, hgk⟩ i hi
    by_cases heq : i = n + 1
    · subst heq; simp [hgk]
    · have : i ≤ n := by omega
      simp [heq, hg i this]
  · intro hg; constructor
    · intro i hi; specialize hg i (by omega); simp [show i ≠ n + 1 by omega] at hg; exact hg
    · specialize hg (n + 1) (le_refl _); simp at hg; exact hg

lemma cyl_ext (N N' : ℕ → ℕ) (n : ℕ) (h : ∀ i, i ≤ n → N i = N' i) :
    Cyl N n = Cyl N' n := by
  ext g; simp only [Cyl, Set.mem_setOf_eq]
  exact ⟨fun hg i hi => h i hi ▸ hg i hi, fun hg i hi => (h i hi).symm ▸ hg i hi⟩

/-- Truncation: replace `g i` by `min (g i) (N i)` to bring any `g` into the
bounded set. -/
noncomputable def truncate (N : ℕ → ℕ) (g : ℕ → ℕ) : ℕ → ℕ :=
  fun i => min (g i) (N i)

lemma truncate_mem_bnd (N : ℕ → ℕ) (g : ℕ → ℕ) : truncate N g ∈ Bnd N :=
  fun _ => min_le_right _ _

lemma truncate_agree_on_cyl (N : ℕ → ℕ) (n : ℕ) (g : ℕ → ℕ) (hg : g ∈ Cyl N n) :
    ∀ i, i ≤ n → truncate N g i = g i := by
  intro i hi
  simp only [truncate, min_eq_left (hg i hi)]

/-- The intersection of closures of cylinder images equals the compact image.
Key lemma for the capacitability proof: uses truncation and sequential
compactness. -/
lemma iInter_closure_image_cyl_eq
    {α : Type*} [TopologicalSpace α] [PolishSpace α]
    {f : (ℕ → ℕ) → α} (hf : Continuous f) (N : ℕ → ℕ) :
    ⋂ n, closure (f '' Cyl N n) = f '' Bnd N := by
  haveI : T2Space α := inferInstance
  apply Set.Subset.antisymm
  · letI := TopologicalSpace.upgradeIsCompletelyMetrizable α
    intro y hy
    simp only [Set.mem_iInter] at hy
    have : ∀ n, ∃ g ∈ Cyl N n, dist (f g) y < 1 / (↑n + 1) := by
      intro n
      have : y ∈ closure (f '' Cyl N n) := hy n
      rw [Metric.mem_closure_iff] at this
      obtain ⟨z, hz, hd⟩ := this (1 / (↑n + 1)) (by positivity)
      obtain ⟨g, hg, hfg⟩ := hz
      exact ⟨g, hg, by rw [hfg, dist_comm]; exact hd⟩
    choose g hg_cyl hg_dist using this
    let g' : ℕ → (ℕ → ℕ) := fun n => truncate N (g n)
    have hg'_bnd : ∀ n, g' n ∈ Bnd N := fun n => truncate_mem_bnd N (g n)
    have hg'_agree : ∀ n i, i ≤ n → g' n i = g n i :=
      fun n => truncate_agree_on_cyl N n (g n) (hg_cyl n)
    have hBnd_compact := isCompact_bnd N
    have hBnd_seq := hBnd_compact.isSeqCompact
    obtain ⟨g_star, hg_star_bnd, φ, hφ_strict, hg'_conv⟩ :=
      hBnd_seq (fun n => hg'_bnd n)
    have hg_conv : Tendsto (fun n => g (φ n)) atTop (𝓝 g_star) := by
      rw [tendsto_pi_nhds]
      intro i
      simp only [nhds_discrete, Filter.tendsto_pure]
      have hg'_ev : ∀ᶠ n in atTop, g' (φ n) i = g_star i := by
        rw [tendsto_pi_nhds] at hg'_conv
        have := hg'_conv i
        simp only [nhds_discrete, Filter.tendsto_pure] at this
        exact this
      have hφ_ev : ∀ᶠ n in atTop, i ≤ φ n :=
        (hφ_strict.tendsto_atTop).eventually (Filter.eventually_ge_atTop i)
      filter_upwards [hg'_ev, hφ_ev] with n h1 h2
      rw [← h1, hg'_agree (φ n) i h2]
    have hf_conv : Tendsto (fun n => f (g (φ n))) atTop (𝓝 (f g_star)) :=
      hf.continuousAt.tendsto.comp hg_conv
    have hfy : Tendsto (fun n => f (g (φ n))) atTop (𝓝 y) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have h1div : Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hφ_top := hφ_strict.tendsto_atTop
      have h_comp : Tendsto (fun n => (1 : ℝ) / (↑(φ n) + 1)) atTop (𝓝 0) :=
        h1div.comp hφ_top
      obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp h_comp) ε hε
      use M
      intro n hn
      have hdist_bound := hg_dist (φ n)
      have hsmall : (1 : ℝ) / (↑(φ n) + 1) < ε := by
        have h := hM n hn
        rw [Real.dist_0_eq_abs, abs_of_nonneg (by positivity)] at h
        exact h
      exact lt_trans hdist_bound hsmall
    have : f g_star = y := tendsto_nhds_unique hf_conv hfy
    exact ⟨g_star, hg_star_bnd, this⟩
  · intro y hy
    simp only [Set.mem_iInter]
    intro n
    apply subset_closure
    obtain ⟨g, hg, hfg⟩ := hy
    exact ⟨g, bnd_subset_cyl N n hg, hfg⟩
