import mathlib

import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.EigenSpectrumHankel
import ThEqRiemann.EqTheorem.Vandermonde
import ThEqRiemann.EqTheorem.CompagnonCharpoly
import ThEqRiemann.EqTheorem.IndeterminationSet
import ThEqRiemann.EqTheorem.HarveyPolkingExtention

/-! -/
namespace ThEq

open Set Complex DefinitionsThEq SpectrumHankel
open VandermondeThEq CompagnonCharpolyThEq
open IndeterminationSetThEq HarveyPolkingThEq


lemma spectre_operateur_regulier
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y : ℂ)
    (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam) (hw : ∀ r : Fin K, w r ≠ 0)
    (hmom : ∀ k : ℕ,
      momentsParametres C γΩ g y k = ∑ r :
        Fin K, (w r : ℂ) * (lam r) ^ k) :
    IsUnit (hankel0Dynamique K C γΩ g y) ∧
    spectrum ℂ ((hankel0Dynamique K C γΩ g y)⁻¹ *
      hankel1Dynamique K C γΩ g y)
      = Set.range lam := by
  have h0 : hankel0Dynamique K C γΩ g y = hankel0 lam w := by
    unfold hankel0Dynamique
    exact hankelOfMoments_eq_hankel0 _ lam w hmom
  have h1 : hankel1Dynamique K C γΩ g y = hankel1 lam w := by
    funext i j
    unfold hankel1Dynamique hankel1 momentsHankel
    exact hmom _
  rw [h0, h1]
  exact ⟨isUnit_hankel0 lam w hlam hw,
    spectre_hankel_inverse lam w hlam hw⟩

lemma continuous_coeff_polyAssocie {K : ℕ} (i : ℕ) :
    Continuous (fun lam : Fin K → ℂ => (polyAssocie lam).coeff i) := by
  have key : ∀ s : Finset (Fin K), ∀ n : ℕ,
      Continuous (fun lam : Fin K → ℂ =>
        (∏ r ∈ s, (Polynomial.X - Polynomial.C (lam r))).coeff n) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro n
        simp only [Finset.prod_empty]
        exact continuous_const
    | insert a s ha ih =>
        intro n
        simp only [Finset.prod_insert ha, Polynomial.coeff_mul]
        refine continuous_finsetSum _ (fun p _ => ?_)
        refine Continuous.mul ?_ (ih p.2)
        rcases Nat.lt_or_ge p.1 2 with hlt | hge
        · interval_cases h : p.1
          · have : ∀ lam : Fin K → ℂ,
                (Polynomial.X - Polynomial.C (lam a)).coeff 0 = - lam a := by
              intro lam
              rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero,
                Polynomial.coeff_C_zero]
              ring
            simp only [this]
            exact (continuous_apply a).neg
          · have : ∀ lam : Fin K → ℂ,
                (Polynomial.X - Polynomial.C (lam a)).coeff 1 = 1 := by
              intro lam
              rw [Polynomial.coeff_sub, Polynomial.coeff_X_one,
                Polynomial.coeff_C, ite_eq_right (by norm_num)]
              ring
            simp only [this]
            exact continuous_const
        · have : ∀ lam : Fin K → ℂ,
              (Polynomial.X - Polynomial.C (lam a)).coeff p.1 = 0 := by
            intro lam
            rw [Polynomial.coeff_sub, Polynomial.coeff_X_of_ne_one
              (by omega),
              Polynomial.coeff_C, ite_eq_right (by omega)]
            ring
          simp only [this]
          exact continuous_const
  simpa [polyAssocie] using key Finset.univ i


lemma companion'_continuous {K : ℕ} :
    Continuous (fun lam : Fin K → ℂ => companion' lam) := by
  refine continuous_pi (fun i => continuous_pi (fun j => ?_))
  unfold companion'
  by_cases h1 : (i : ℕ) = (j : ℕ) + 1 ∧ (j : ℕ) < K - 1
  · simp only [h1, and_self, ite_true]
    exact continuous_const
  · simp only [h1, ite_false]
    by_cases h2 : (j : ℕ) = K - 1
    · simp only [h2, ite_true]
      exact (continuous_coeff_polyAssocie (K := K) (i : ℕ)).neg
    · simp only [h2, ite_false]
      exact continuous_const

lemma companion'_tendsto {K : ℕ} {ι : Type*} {F : Filter ι}
    (lam : ι → Fin K → ℂ) (lam₀ : Fin K → ℂ)
    (h : Filter.Tendsto lam F (nhds lam₀)) :
    Filter.Tendsto (fun y => companion' (lam y)) F (nhds (companion' lam₀)) :=
  (Continuous.tendsto (companion'_continuous (K := K)) lam₀).comp h

lemma spectre_companion' {K : ℕ} (lam₀ : Fin K → ℂ) :
    spectrum ℂ (companion' lam₀) = Set.range lam₀ := by
  ext z
  rw [spectre_eq_roots_charpoly, companion'_charpoly lam₀,
      polyAssocie_isRoot_iff_mem_range]

lemma inv_tendsto_zero_of_norm_atTop
    {f : ℂ → ℂ} {pq : ℂ}
    (hpole : Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin pq {pq}ᶜ) Filter.atTop) :
    Filter.Tendsto (fun z => (f z)⁻¹) (nhdsWithin pq {pq}ᶜ) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  exact tendsto_inv_atTop_zero.comp hpole

lemma analyticAt_update_of_tendsto
    {h : ℂ → ℂ} {x₀ c : ℂ}
    (hmero : MeromorphicAt h x₀)
    (hlim : Filter.Tendsto h (nhdsWithin x₀ {x₀}ᶜ) (nhds c)) :
    AnalyticAt ℂ (Function.update h x₀ c) x₀ := by
  have heq : Function.update h x₀ c =ᶠ[nhdsWithin x₀ {x₀}ᶜ] h := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Function.update_of_ne (Set.mem_compl_singleton_iff.mp hz) c h
  have hmero' : MeromorphicAt (Function.update h x₀ c) x₀ :=
    hmero.congr heq.symm
  have hcont : ContinuousAt (Function.update h x₀ c) x₀ :=
    continuousAt_update_same.mpr hlim
  exact hmero'.analyticAt hcont

lemma exists_analytic_inv
    {f : ℂ → ℂ} {pq : ℂ}
    (hf : MeromorphicAt f pq)
    (hpole : Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin pq {pq}ᶜ) Filter.atTop) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ pq ∧ φ pq = 0 ∧
      ∀ᶠ z in nhdsWithin pq {pq}ᶜ, φ z = (f z)⁻¹ := by
  have hinv : MeromorphicAt (fun z => (f z)⁻¹) pq := hf.inv
  have hlim := inv_tendsto_zero_of_norm_atTop hpole
  refine ⟨Function.update (fun z => (f z)⁻¹) pq 0,
    analyticAt_update_of_tendsto hinv hlim, by simp, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  simp [Function.update_of_ne (Set.mem_compl_singleton_iff.mp hz)]

lemma phi_not_eventually_const
    {f φ : ℂ → ℂ} {pq : ℂ}
    (hpole : Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin pq {pq}ᶜ) Filter.atTop)
    (hφ0 : φ pq = 0)
    (hφ_eq : ∀ᶠ z in nhdsWithin pq {pq}ᶜ, φ z = (f z)⁻¹) :
    ¬ ∀ᶠ z in nhds pq, φ z = φ pq := by
  intro hconst
  have h1 : ∀ᶠ z in nhdsWithin pq {pq}ᶜ, f z = 0 := by
    filter_upwards [hφ_eq, nhdsWithin_le_nhds hconst] with z hz1 hz2
    rw [hφ0] at hz2
    rw [hz2] at hz1
    exact inv_eq_zero.mp hz1.symm
  have h2 : ∀ᶠ z in nhdsWithin pq {pq}ᶜ, (1 : ℝ) < ‖f z‖ :=
    hpole.eventually (Filter.eventually_gt_atTop 1)
  obtain ⟨z, hz1, hz2⟩ := (h1.and h2).exists
  rw [hz1, norm_zero] at hz2
  linarith

lemma phi_image_contains_ball
    {φ : ℂ → ℂ} {pq : ℂ} (hφ : AnalyticAt ℂ φ pq) (hφ0 : φ pq = 0)
    (hnc : ¬ ∀ᶠ z in nhds pq, φ z = φ pq) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, Metric.ball (0 : ℂ) δ ⊆ φ '' Metric.ball pq ε := by
  have hopen : nhds (φ pq) ≤ Filter.map φ (nhds pq) := by
    rcases hφ.eventually_constant_or_nhds_le_map_nhds with h | h
    · exact absurd h hnc
    · exact h
  have hmem : φ '' Metric.ball pq ε ∈ nhds (φ pq) := by
    apply hopen
    rw [Filter.mem_map]
    filter_upwards [Metric.ball_mem_nhds pq hε] with z hz
    exact ⟨z, hz, rfl⟩
  rw [hφ0] at hmem
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hmem
  exact ⟨δ, hδ, hsub⟩

lemma pole_prend_grandes_valeurs
    {f : ℂ → ℂ} {pq : ℂ}
    (hf : MeromorphicAt f pq)
    (hpole : Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin pq {pq}ᶜ) Filter.atTop)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ w : ℂ, R < ‖w‖ →
      ∃ x : ℂ, x ≠ pq ∧ dist x pq < ε ∧ f x = w := by
  obtain ⟨φ, hφ_an, hφ0, hφ_eq⟩ := exists_analytic_inv hf hpole
  have hnc := phi_not_eventually_const hpole hφ0 hφ_eq
  obtain ⟨ε1, hε1, hball1⟩ : ∃ ε1 > 0, ∀ z, dist z pq < ε1 → z ≠ pq → φ z = (f z)⁻¹ := by
    have := (mem_nhdsWithin.mp hφ_eq)
    obtain ⟨U, hU_open, hpqU, hUsub⟩ := this
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU_open pq hpqU
    refine ⟨r, hr, fun z hz hne => ?_⟩
    exact hUsub ⟨hrU hz, hne⟩
  obtain ⟨δ, hδ, hball⟩ :=
    phi_image_contains_ball hφ_an hφ0 hnc (lt_min hε hε1)
  refine ⟨1 / δ, fun w hw => ?_⟩
  have hw0 : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hw
    have : 0 < 1 / δ := by positivity
    linarith
  have hwδ : w⁻¹ ∈ Metric.ball (0 : ℂ) δ := by
    rw [mem_ball_zero_iff, norm_inv]
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    calc ‖w‖⁻¹ < (1 / δ)⁻¹ := inv_strictAnti₀ (by positivity) hw
      _ = δ := by simp
  obtain ⟨x, hx, hφx⟩ := hball hwδ
  have hxd : dist x pq < min ε ε1 := by simpa using hx
  have hx_ne : x ≠ pq := by
    intro h
    rw [h, hφ0] at hφx
    exact inv_ne_zero hw0 hφx.symm
  refine ⟨x, hx_ne, lt_of_lt_of_le hxd (min_le_left _ _), ?_⟩
  have h1 : φ x = (f x)⁻¹ := hball1 x (lt_of_lt_of_le hxd (min_le_right _ _)) hx_ne
  rw [h1] at hφx
  exact inv_injective hφx

lemma choix_antecedents
    {f : ℂ → ℂ} {pq : ℂ} {S : ℕ → ℝ}
    (hS : ∀ (n : ℕ) (w : ℂ), S n < ‖w‖ →
      ∃ x, x ≠ pq ∧ dist x pq < 1 / ((n : ℝ) + 1) ∧ f x = w) :
    ∃ s : ℂ → ℕ → ℂ, ∀ (w : ℂ) (n : ℕ), S n < ‖w‖ →
      f (s w n) = w ∧ dist (s w n) pq < 1 / ((n : ℝ) + 1) := by
  classical
  refine ⟨fun w n => if h : S n < ‖w‖ then (hS n w h).choose else pq, ?_⟩
  intro w n hn
  simp only [dite_eq_left hn]
  exact ⟨(hS n w hn).choose_spec.2.2, (hS n w hn).choose_spec.2.1⟩

lemma exists_monotone_majorant (R : ℕ → ℝ) :
    ∃ S : ℕ → ℝ, Monotone S ∧ ∀ n, R n ≤ S n := by
  refine ⟨fun n => (Finset.range (n + 1)).sup' ⟨0, by simp⟩ R, ?_, ?_⟩
  · intro a b hab
    apply Finset.sup'_mono
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
  · intro n
    exact Finset.le_sup' R (by simp)

lemma N_grand
    {l : Filter ℂ} {g : ℂ → ℂ} {S : ℕ → ℝ}
    (hg : Filter.Tendsto (fun y => ‖g y‖) l Filter.atTop)
    (n : ℕ) (M : ℝ) (hM : S n ≤ M) :
    ∀ᶠ y in l, n ≤ Nat.findGreatest (fun k => S k < ‖g y‖) ⌈‖g y‖⌉₊ := by
  classical
  have h1 : ∀ᶠ y in l, max M (n : ℝ) < ‖g y‖ :=
    hg.eventually (Filter.eventually_gt_atTop _)
  filter_upwards [h1] with y hy
  apply Nat.le_findGreatest
  · have : (n : ℝ) ≤ ‖g y‖ := le_trans (le_max_right _ _) hy.le
    exact_mod_cast this.trans (Nat.le_ceil _)
  · exact lt_of_le_of_lt hM (lt_of_le_of_lt (le_max_left _ _) hy)

lemma N_admissible
    {g : ℂ → ℂ} {S : ℕ → ℝ} {y : ℂ} (h0 : S 0 < ‖g y‖) :
    S (Nat.findGreatest (fun k => S k < ‖g y‖) ⌈‖g y‖⌉₊) < ‖g y‖ := by
  classical
  exact Nat.findGreatest_spec (P := fun k => S k < ‖g y‖) (Nat.zero_le _) h0

lemma solutions_tendent_vers_pole
    {f g : ℂ → ℂ} {y₀ pq : ℂ}
    (hf : MeromorphicAt f pq)
    (hpole : Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin pq {pq}ᶜ) Filter.atTop)
    (hg : Filter.Tendsto (fun y => ‖g y‖) (nhdsWithin y₀ {y₀}ᶜ) Filter.atTop) :
    ∃ x : ℂ → ℂ, (∀ᶠ y in nhdsWithin y₀ {y₀}ᶜ, f (x y) = g y) ∧
      Filter.Tendsto x (nhdsWithin y₀ {y₀}ᶜ) (nhds pq) := by
  classical
  have hR : ∀ n : ℕ, ∃ R : ℝ, ∀ w : ℂ, R < ‖w‖ →
      ∃ x : ℂ, x ≠ pq ∧ dist x pq < 1 / ((n : ℝ) + 1) ∧ f x = w := fun n =>
    pole_prend_grandes_valeurs hf hpole (by positivity)
  choose R hR using hR
  obtain ⟨S, hSmono, hRS⟩ := exists_monotone_majorant R
  have hS : ∀ (n : ℕ) (w : ℂ), S n < ‖w‖ →
      ∃ x, x ≠ pq ∧ dist x pq < 1 / ((n : ℝ) + 1) ∧ f x = w :=
    fun n w hw => hR n w (lt_of_le_of_lt (hRS n) hw)
  obtain ⟨s, hs⟩ := choix_antecedents hS
  let N : ℂ → ℕ := fun y => Nat.findGreatest (fun k => S k < ‖g y‖) ⌈‖g y‖⌉₊
  have h0 : ∀ᶠ y in nhdsWithin y₀ {y₀}ᶜ, S 0 < ‖g y‖ :=
    hg.eventually (Filter.eventually_gt_atTop _)
  refine ⟨fun y => s (g y) (N y), ?_, ?_⟩
  · filter_upwards [h0] with y hy
    exact (hs (g y) (N y) (N_admissible hy)).1
  · rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have hNn := N_grand (l := nhdsWithin y₀ {y₀}ᶜ) (g := g) hg n (S n) le_rfl
    filter_upwards [h0, hNn] with y hy hy'
    have hd := (hs (g y) (N y) (N_admissible hy)).2
    calc dist (s (g y) (N y)) pq < 1 / ((N y : ℝ) + 1) := hd
      _ ≤ 1 / ((n : ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity)
          have : (n : ℝ) ≤ N y := by exact_mod_cast hy'
          linarith
      _ < ε := hn

----------------------------------------------------------------


lemma collision_spectrale_abstraite {K : ℕ} (y₀ : ℂ)
    (lamFun : ℂ → Fin K → ℂ) (lamLim : Fin K → ℂ)
    (hlim : Filter.Tendsto lamFun (nhdsWithin y₀ {y₀}ᶜ) (nhds lamLim)) :
    Filter.Tendsto (fun y => companion' (lamFun y)) (nhdsWithin y₀ {y₀}ᶜ)
        (nhds (companion' lamLim)) ∧
    spectrum ℂ (companion' lamLim) = Set.range lamLim :=
  ⟨companion'_tendsto lamFun lamLim hlim, spectre_companion' lamLim⟩

lemma collision_spectrale_poles
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y₀ : ℂ)
    (lamFun : ℂ → Fin K → ℂ) (w : ℂ → Fin K → ℤ)
    (hlam : ∀ y, Function.Injective (lamFun y))
    (hw : ∀ y r, w y r ≠ 0)
    (hmom : ∀ y k, momentsParametres C γΩ g y k =
      ∑ r : Fin K, (w y r : ℂ) * (lamFun y r) ^ k)
    (lamLim : Fin K → ℂ)
    (hlim : Filter.Tendsto lamFun (nhdsWithin y₀ {y₀}ᶜ) (nhds lamLim))
    (Pf : Set ℂ) (hPf : Set.range lamLim = Pf) :
    ∃ Mlim : Matrix (Fin K) (Fin K) ℂ,
      Filter.Tendsto
        (fun y => (hankel0Dynamique K C γΩ g y)⁻¹ *
          hankel1Dynamique K C γΩ g y)
        (nhdsWithin y₀ {y₀}ᶜ) (nhds Mlim) ∧
      spectrum ℂ Mlim = Pf := by
  refine ⟨companion' lamLim, ?_, by rw [spectre_companion', hPf]⟩
  have hM : ∀ y, (hankel0Dynamique K C γΩ g y)⁻¹ *
    hankel1Dynamique K C γΩ g y
      = companion' (lamFun y) := by
    intro y
    have h0 : hankel0Dynamique K C γΩ g y = hankel0 (lamFun y) (w y) :=
      hankelOfMoments_eq_hankel0 _ (lamFun y) (w y) (hmom y)
    have h1 : hankel1Dynamique K C γΩ g y = hankel1 (lamFun y) (w y) := by
      funext i j
      unfold hankel1Dynamique hankel1 momentsHankel
      exact hmom y _
    rw [h0, h1]
    exact hankel_inverse_mul_eq_companion (lamFun y) (w y) (hlam y) (hw y)
  simp only [hM]
  exact companion'_tendsto lamFun lamLim hlim

--------------------------------------------------------------------

theorem equationary_theorem
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y₀ : ℂ)
    (lamFun : ℂ → Fin K → ℂ) (w : ℂ → Fin K → ℤ)
    (hlam : ∀ y, Function.Injective (lamFun y))
    (hw : ∀ y r, w y r ≠ 0)
    (hmom : ∀ y k, momentsParametres C γΩ g y k =
      ∑ r : Fin K, (w y r : ℂ) * (lamFun y r) ^ k)
    (lamLim : Fin K → ℂ)
    (hlim : Filter.Tendsto lamFun (nhdsWithin y₀ {y₀}ᶜ) (nhds lamLim))
    (Pf : Set ℂ) (hPf : Set.range lamLim = Pf) :
    (∀ y : ℂ,
      IsUnit (hankel0Dynamique K C γΩ g y) ∧
      spectrum ℂ ((hankel0Dynamique K C γΩ g y)⁻¹ * hankel1Dynamique K C γΩ g y)
        = Set.range (lamFun y)) ∧
    (∃ Mlim : Matrix (Fin K) (Fin K) ℂ,
      Filter.Tendsto
        (fun y => (hankel0Dynamique K C γΩ g y)⁻¹ * hankel1Dynamique K C γΩ g y)
        (nhdsWithin y₀ {y₀}ᶜ) (nhds Mlim) ∧
      spectrum ℂ Mlim = Pf) := by
  refine ⟨fun y => ?_, ?_⟩
  · exact spectre_operateur_regulier K C γΩ g y (lamFun y) (w y)
      (hlam y) (hw y) (hmom y)
  · exact collision_spectrale_poles K C γΩ g y₀ lamFun w hlam hw hmom
      lamLim hlim Pf hPf















end ThEq
