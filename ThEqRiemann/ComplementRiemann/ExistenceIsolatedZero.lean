import mathlib

/-! -/
namespace ExistIsolatedZero

open Set Complex


lemma eventually_nhds_imp_of_nhdsWithin_compl_singleton
    {α : Type*} [TopologicalSpace α] {zm : α} {P : α → Prop} :
    (∀ᶠ x in nhdsWithin zm {zm}ᶜ, P x) →
    (∀ᶠ x in nhds zm, x ≠ zm → P x) := by
  intro h
  change {x | P x} ∈ nhdsWithin zm {zm}ᶜ at h
  change {x | x ≠ zm → P x} ∈ nhds zm
  obtain ⟨U, hU, hUP⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp h
  apply Filter.mem_of_superset hU
  intro x hx hne
  exact hUP ⟨hx, by
    simpa only [Set.mem_compl_singleton_iff] using hne⟩

lemma exists_contour_zero_isole
    {f : ℂ → ℂ} {zm : ℂ} (hre : |zm.re| < 1 / 2)
    (hana : AnalyticAt ℂ f zm) (_ : f zm = 0)
    (hnz : ¬ (∀ᶠ z in nhds zm, f z = 0)) :
    ∃ R : ℝ, 0 < R ∧
      (∀ z ∈ Metric.closedBall zm R, z.re < 1 / 2) ∧
      (∀ z ∈ Metric.closedBall zm R, -1 / 2 < z.re) ∧
      (∀ z ∈ Metric.closedBall zm R, f z = 0 → z = zm) ∧
      (∀ z ∈ Metric.sphere zm R, f z ≠ 0) := by
  have hiso : ∀ᶠ z in nhds zm, z ≠ zm → f z ≠ 0 := by
    have h := hana.eventually_eq_zero_or_eventually_ne_zero
    rcases h with h | h
    · exact absurd h hnz
    · exact eventually_nhds_imp_of_nhdsWithin_compl_singleton h
  obtain ⟨ρ, hρ, hρsub⟩ := Metric.eventually_nhds_iff.mp hiso
  have hre1 : zm.re < 1 / 2 := (abs_lt.mp hre).2
  have hre2 : -1 / 2 < zm.re := by linarith [(abs_lt.mp hre).1]
  refine ⟨min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ / 2, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 < min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ :=
      lt_min (lt_min (by linarith) (by linarith)) hρ
    linarith
  · intro z hz
    have hzd : dist z zm ≤ min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ / 2 :=
      Metric.mem_closedBall.mp hz
    have h1 : |z.re - zm.re| ≤ dist z zm :=
      (Complex.abs_re_le_norm (z - zm)).trans_eq (Complex.dist_eq z zm).symm
    have h2 : min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ ≤ 1 / 2 - zm.re :=
      (min_le_left _ _).trans (min_le_left _ _)
    have h3 : 0 < min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ :=
      lt_min (lt_min (by linarith) (by linarith)) hρ
    have := (abs_le.mp (h1.trans hzd)).2
    linarith
  · intro z hz
    have hzd : dist z zm ≤ min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ / 2 :=
      Metric.mem_closedBall.mp hz
    have h1 : |z.re - zm.re| ≤ dist z zm :=
      (Complex.abs_re_le_norm (z - zm)).trans_eq (Complex.dist_eq z zm).symm
    have h2 : min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ ≤ 1 / 2 + zm.re :=
      (min_le_left _ _).trans (min_le_right _ _)
    have h3 : 0 < min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ :=
      lt_min (lt_min (by linarith) (by linarith)) hρ
    have := (abs_le.mp (h1.trans hzd)).1
    linarith
  · intro z hz hfz
    by_contra hne
    have hzd : dist z zm ≤ min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ / 2 :=
      Metric.mem_closedBall.mp hz
    have h_le_rho : min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ ≤ ρ :=
      (min_le_right _ _)
    have h_pos : 0 < min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ :=
      lt_min (lt_min (by linarith) (by linarith)) hρ
    have : dist z zm < ρ := by linarith
    exact hρsub this hne hfz
  · intro z hz hfz
    have hzd : dist z zm = min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ / 2 :=
      Metric.mem_sphere.mp hz
    have h_le_rho : min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ ≤ ρ :=
      min_le_right _ _
    have h_pos : 0 < min (min (1 / 2 - zm.re) (1 / 2 + zm.re)) ρ :=
      lt_min (lt_min (by linarith) (by linarith)) hρ
    have hne : z ≠ zm := by
      intro h; rw [h, dist_self] at hzd; linarith
    have : dist z zm < ρ := by linarith
    exact hρsub this hne hfz




end ExistIsolatedZero
