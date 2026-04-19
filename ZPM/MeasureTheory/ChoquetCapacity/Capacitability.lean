/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import ZPM.MeasureTheory.ChoquetCapacity.Def
import ZPM.MeasureTheory.ChoquetCapacity.CylinderMachinery

/-!
# Choquet capacitability for analytic sets

Kechris, Classical Descriptive Set Theory, Theorem 30.13: for any Choquet
capacity `cap` on a Polish space and any analytic `s`, `cap s` equals the
supremum of `cap K` over compact subsets `K ⊆ s`. The analytic set is
parametrised as the continuous image of `ℕ^ℕ`, a sequence of truncation
bounds `N : ℕ → ℕ` is built by diagonal induction using `iUnion_nat`, and
`iInter_closed` is applied to the closures of cylinder images to collapse
the intersection to a compact image via `iInter_closure_image_cyl_eq`.
-/

open MeasureTheory Set Filter Topology

/-- **Choquet capacitability.** For analytic sets, capacity equals the
supremum over compact subsets (Kechris 30.13). -/
theorem MeasureTheory.AnalyticSet.cap_eq_iSup_isCompact
    {α : Type*}
    [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {cap : Set α → ENNReal}
    (hcap : MeasureTheory.IsChoquetCapacity cap)
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    cap s = ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ s), cap K := by
  apply le_antisymm
  · rw [AnalyticSet] at hs
    rcases hs with rfl | ⟨f, hf_cont, hf_range⟩
    · exact le_iSup_of_le ∅ (le_iSup_of_le isCompact_empty
        (le_iSup_of_le (Set.empty_subset _) le_rfl))
    · subst hf_range
      apply le_of_forall_lt_imp_le_of_dense
      intro t ht
      have hrange_union : range f = ⋃ k, f '' {g : ℕ → ℕ | g 0 ≤ k} := by
        rw [← Set.image_univ,
          show (Set.univ : Set (ℕ → ℕ)) = ⋃ k, {g : ℕ → ℕ | g 0 ≤ k} from by
            ext g; simp [Set.mem_iUnion]; exact ⟨g 0, le_refl _⟩,
          Set.image_iUnion]
      have hmono_base : Monotone (fun k => f '' {g : ℕ → ℕ | g 0 ≤ k}) := by
        intro a b hab; apply Set.image_mono; intro x (hx : x 0 ≤ a); exact le_trans hx hab
      rw [hrange_union, hcap.iUnion_nat _ hmono_base] at ht
      obtain ⟨k₀, hk₀⟩ := lt_iSup_iff.mp ht

      have hcyl0 : f '' {g : ℕ → ℕ | g 0 ≤ k₀} = f '' Cyl (fun _ => k₀) 0 := by
        congr 1; ext g; simp [Cyl]

      have rec_step : ∀ (M : ℕ → ℕ) (n : ℕ), t < cap (f '' Cyl M n) →
          ∃ k, t < cap (f '' Cyl (Function.update M (n + 1) k) (n + 1)) := by
        intro M n hlt_M
        have hsplit : cap (f '' Cyl M n) =
            ⨆ k, cap (f '' (Cyl M n ∩ {g | g (n + 1) ≤ k})) := by
          conv_lhs => rw [cyl_succ_eq M n, Set.image_iUnion]
          exact hcap.iUnion_nat _
            (fun a b h => Set.image_mono (monotone_cyl_split M n h))
        rw [hsplit] at hlt_M
        obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt_M
        exact ⟨k, by rwa [cyl_inter_eq_cyl_update] at hk⟩

      let build : (n : ℕ) → { M : ℕ → ℕ // t < cap (f '' Cyl M n) } :=
        fun n => Nat.rec
          ⟨fun _ => k₀, hcyl0 ▸ hk₀⟩
          (fun m ⟨M_prev, hM_prev⟩ =>
            ⟨Function.update M_prev (m + 1)
              (Classical.choose (rec_step M_prev m hM_prev)),
             Classical.choose_spec (rec_step M_prev m hM_prev)⟩)
          n

      let N_seq : ℕ → (ℕ → ℕ) := fun n => (build n).val
      have hN_seq_prop : ∀ n, t < cap (f '' Cyl (N_seq n) n) :=
        fun n => (build n).property

      have hN_seq_consistent : ∀ n i, i ≤ n → N_seq (n + 1) i = N_seq n i := by
        intro n i hi
        show (Function.update (N_seq n) (n + 1) _) i = N_seq n i
        exact Function.update_of_ne (by omega) ..

      let N : ℕ → ℕ := fun i => N_seq i i

      have hN_agree : ∀ n i, i ≤ n → N i = N_seq n i := by
        intro n
        induction n with
        | zero => intro i hi; simp only [Nat.le_zero] at hi; subst hi; rfl
        | succ m ih =>
          intro i hi
          by_cases heq : i = m + 1
          · subst heq; rfl
          · have him : i ≤ m := by omega
            show N_seq i i = N_seq (m + 1) i
            rw [hN_seq_consistent m i him]
            exact ih i him

      have hcyl_eq : ∀ n, Cyl N n = Cyl (N_seq n) n :=
        fun n => cyl_ext N (N_seq n) n (hN_agree n)

      have hcap_bound : ∀ n, t < cap (f '' Cyl N n) :=
        fun n => hcyl_eq n ▸ hN_seq_prop n

      set E := fun n => closure (f '' Cyl N n) with hE_def
      have hE_closed : ∀ n, IsClosed (E n) := fun _ => isClosed_closure
      have hE_anti : Antitone E := by
        intro m n hmn
        apply closure_mono
        apply Set.image_mono
        intro x (hx : ∀ i, i ≤ n → x i ≤ N i) i hi
        exact hx i (le_trans hi hmn)
      have hE_cap : ∀ n, t < cap (E n) := by
        intro n
        exact lt_of_lt_of_le (hcap_bound n) (hcap.mono subset_closure)

      have hE_inter_cap : cap (⋂ n, E n) = ⨅ n, cap (E n) :=
        hcap.iInter_closed E hE_anti hE_closed
      have ht_le : t ≤ cap (⋂ n, E n) := by
        rw [hE_inter_cap]; exact le_iInf fun n => le_of_lt (hE_cap n)

      have hkey : ⋂ n, E n = f '' Bnd N :=
        iInter_closure_image_cyl_eq hf_cont N

      have hK_compact : IsCompact (f '' Bnd N) := (isCompact_bnd N).image hf_cont
      have hK_sub : f '' Bnd N ⊆ range f := Set.image_subset_range f _

      calc t ≤ cap (⋂ n, E n) := ht_le
        _ = cap (f '' Bnd N) := by rw [hkey]
        _ ≤ ⨆ (K : Set α), ⨆ (_ : IsCompact K), ⨆ (_ : K ⊆ range f), cap K :=
            le_iSup_of_le _ (le_iSup_of_le hK_compact (le_iSup_of_le hK_sub le_rfl))
  · exact iSup_le fun K => iSup_le fun _ => iSup_le fun hKs => hcap.mono hKs
