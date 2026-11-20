import mathlib

import ThEqRiemann.EqTheorem.DefThEq

/-! -/
namespace GeoZero

open Set Complex DefinitionsThEq



/-- L'adhérence de `Ω` est compacte (fermé + borné dans `ℂ`, espace propre). -/
lemma closure_Omega_compact (C : CadreGeometrique) :
    IsCompact (closure C.Ω) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_closure C.hΩ_bounded.closure


lemma gAux_differentiableOn (C : CadreGeometrique) :
    DifferentiableOn ℂ (gAux C) C.V := by
  change DifferentiableOn ℂ (fun z => C.f z - C.y) C.V
  exact C.hf.sub (differentiableOn_const C.y)

lemma gAux_analyticOnNhd (C : CadreGeometrique) :
    AnalyticOnNhd ℂ (gAux C) C.V :=
  (gAux_differentiableOn C).analyticOnNhd C.hV_open

lemma gAux_codiscrete_ne_zero (C : CadreGeometrique)
    (hf_ne : ¬ Set.EqOn (gAux C) 0 C.V) :
    ∀ᶠ x in Filter.codiscreteWithin C.V, gAux C x ≠ 0 :=
  ((gAux_analyticOnNhd C).eqOn_zero_or_eventually_ne_zero_of_preconnected
    C.hV_preconnected).resolve_left hf_ne

lemma finitude_zeros_gAux (C : CadreGeometrique)
    (hf_ne : ¬ Set.EqOn (gAux C) 0 C.V) :
    (closure C.Ω ∩ {x | gAux C x = 0}).Finite := by
  have hmem : {x | gAux C x ≠ 0} ∈ Filter.codiscreteWithin C.V :=
    gAux_codiscrete_ne_zero C hf_ne
  have hmem' : {x | gAux C x ≠ 0} ∈ Filter.codiscreteWithin (closure C.Ω) :=
    Filter.codiscreteWithin_mono C.hV_sub hmem
  have hfin : (closure C.Ω \ {x | gAux C x ≠ 0}).Finite :=
    (closure_Omega_compact C).finite_sdiff_of_mem_codiscreteWithin hmem'
  have heq : closure C.Ω \ {x | gAux C x ≠ 0} = closure C.Ω ∩ {x | gAux C x = 0} := by
    ext x
    simp [Set.mem_sdiff, Set.mem_inter_iff]
  rwa [heq] at hfin

lemma finitude_solutions_S (C : CadreGeometrique)
    (hf_ne : ¬ Set.EqOn (gAux C) 0 C.V) :
    (solutionsInterieures C).Finite := by
  apply (finitude_zeros_gAux C hf_ne).subset
  intro z hz
  obtain ⟨hzΩ, hzf⟩ := hz
  refine ⟨subset_closure hzΩ, ?_⟩
  change gAux C z = 0
  simp [gAux, hzf]


lemma nhdsWithin_compl_singleton_neBot (x₀ : ℂ) :
    (nhdsWithin x₀ {x₀}ᶜ).NeBot := by
  infer_instance

lemma tendsto_norm_nhdsWithin_of_continuousAt (f : ℂ → ℂ) (x₀ : ℂ)
    (hf_cont : ContinuousAt f x₀) :
    Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin x₀ {x₀}ᶜ) (nhds ‖f x₀‖) := by
  have hcont' : Filter.Tendsto f (nhdsWithin x₀ {x₀}ᶜ) (nhds (f x₀)) :=
    hf_cont.tendsto.mono_left nhdsWithin_le_nhds
  exact hcont'.norm

lemma not_tendsto_nhds_and_atTop {α : Type*} {l : Filter α} [l.NeBot]
    (g : α → ℝ) (a : ℝ)
    (h1 : Filter.Tendsto g l (nhds a)) (h2 : Filter.Tendsto g l Filter.atTop) :
    False :=
  not_tendsto_atTop_of_tendsto_nhds h1 h2

lemma disjonction_solutions_poles (f : ℂ → ℂ) (Ω₁ : Set ℂ) (hΩ₁_open : IsOpen Ω₁)
    (hf_cont : ContinuousOn f Ω₁) (v : ℂ) :
    Disjoint (ensembleSolutions f Ω₁ v) (ensemblePoles f Ω₁) := by
  rw [Set.disjoint_left]
  intro x₀ hx₀S hx₀P
  obtain ⟨hx₀Ω, hx₀eq⟩ := hx₀S
  obtain ⟨_, hx₀lim⟩ := hx₀P
  have := nhdsWithin_compl_singleton_neBot x₀
  have hcontAt : ContinuousAt f x₀ :=
    (hf_cont x₀ hx₀Ω).continuousAt (hΩ₁_open.mem_nhds hx₀Ω)
  have hnorm := tendsto_norm_nhdsWithin_of_continuousAt f x₀ hcontAt
  exact not_tendsto_nhds_and_atTop (fun z => ‖f z‖) ‖f x₀‖ hnorm hx₀lim

lemma Hy_differentiableAt (f : ℂ → ℂ) (w x_j : ℂ)
    (hf_diff : DifferentiableAt ℂ f x_j) :
    DifferentiableAt ℂ (fun x => f x - w) x_j :=
  hf_diff.sub (differentiableAt_const w)

lemma forme_normale_zero
    (H : ℂ → ℂ) (x_j : ℂ)
    (hH_an : AnalyticAt ℂ H x_j)
    (hH_ne : ¬ (∀ᶠ x in nhds x_j, H x = 0)) :
    ∃ (m_j : ℕ) (ψ : ℂ → ℂ), AnalyticAt ℂ ψ x_j ∧ ψ x_j ≠ 0 ∧
      ∀ᶠ x in nhds x_j, H x = (x - x_j) ^ m_j * ψ x := by
  obtain ⟨m_j, ψ, hψ_an, hψ_nz, hHψ⟩ :=
    (AnalyticAt.exists_eventuallyEq_pow_smul_ne_zero_iff hH_an).mpr hH_ne
  refine ⟨m_j, ψ, hψ_an, hψ_nz, ?_⟩
  filter_upwards [hHψ] with x hx
  simpa [smul_eq_mul] using hx

lemma extraction_point_central
    (H ψ : ℂ → ℂ) (x_j : ℂ) (m_j : ℕ) (x : ℂ)
    (hx_eq : ∀ᶠ y in nhds x, H y = (y - x_j) ^ m_j * ψ y) :
    H x = (x - x_j) ^ m_j * ψ x :=
  hx_eq.self_of_nhds

lemma differentiabilite_H_locale
    (H ψ : ℂ → ℂ) (x_j : ℂ) (m_j : ℕ) (x : ℂ)
    (hψx_diff : DifferentiableAt ℂ ψ x)
    (hx_eq : H =ᶠ[nhds x] fun z => (z - x_j) ^ m_j * ψ z) :
    DifferentiableAt ℂ H x := by
  have hprod_diff : DifferentiableAt ℂ (fun z => (z - x_j) ^ m_j * ψ z) x :=
    ((differentiableAt_id.sub_const x_j).pow m_j).mul hψx_diff
  exact hprod_diff.congr_of_eventuallyEq hx_eq

lemma deriv_produit_forme_normale
    (ψ : ℂ → ℂ) (x_j : ℂ) (m_j : ℕ) (x : ℂ)
    (hψx_diff : DifferentiableAt ℂ ψ x) :
    deriv (fun z => (z - x_j) ^ m_j * ψ z) x
      = (m_j : ℂ) * (x - x_j) ^ (m_j - 1) * ψ x + (x - x_j) ^ m_j * deriv ψ x := by
  have h1 : HasDerivAt (fun z : ℂ => z - x_j) 1 x := (hasDerivAt_id x).sub_const x_j
  have h2 : HasDerivAt (fun z : ℂ => (z - x_j) ^ m_j)
      ((m_j : ℂ) * (x - x_j) ^ (m_j - 1) * 1) x := h1.pow m_j
  have h3 : HasDerivAt ψ (deriv ψ x) x := hψx_diff.hasDerivAt
  have h4 := h2.mul h3
  simp only [mul_one] at h4
  exact h4.deriv


lemma identite_algebrique_deriv_log
    (a p q : ℂ) (m_j : ℕ) (hm_j : m_j ≠ 0)
    (ha : a ≠ 0) (hp : p ≠ 0) :
    ((m_j : ℂ) * a ^ (m_j - 1) * p + a ^ m_j * q) / (a ^ m_j * p)
      = (m_j : ℂ) / a + q / p := by
  have hpow : a * a ^ (m_j - 1) = a ^ m_j := mul_pow_sub_one hm_j a
  have hpow_ne : a ^ m_j ≠ 0 := pow_ne_zero m_j ha
  rw [div_add_div _ _ ha hp, div_eq_div_iff
    (mul_ne_zero hpow_ne hp) (mul_ne_zero ha hp)]
  ring_nf
  rw [← hpow]
  ring




end GeoZero
