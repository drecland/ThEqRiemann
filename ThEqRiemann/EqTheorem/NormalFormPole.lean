import mathlib

import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.GeometricalZero
import ThEqRiemann.EqTheorem.ResiduCircleIntegration1
import ThEqRiemann.EqTheorem.MeromorphicOn

/-! -/
namespace NormalFormPoleThEq

open Set Complex DefinitionsThEq GeoZero ResCircIntegration1

lemma meromorphicOrderAt_sub_const_eq_of_pole
    (f : ℂ → ℂ) (p_q w : ℂ) (n_q : ℕ) (hn_q_pos : 0 < n_q)
    (hf_mero : MeromorphicAt f p_q)
    (hf_pole : meromorphicOrderAt f p_q = -(n_q : ℤ)) :
    meromorphicOrderAt (fun x => f x - w) p_q = -(n_q : ℤ) := by
  -- Étape 1 : forme normale de f
  obtain ⟨φ, hφ_an, hφ_ne, hφ_eq⟩ := (meromorphicOrderAt_eq_int_iff hf_mero).mp hf_pole
  -- Étape 2 : la fonction (z-p_q)^n_q est analytique (polynomiale)
  have hpow_an : AnalyticAt ℂ (fun z => (z - p_q) ^ n_q) p_q :=
    (analyticAt_id.sub analyticAt_const).pow n_q
  -- Étape 3 : ψ := φ - w * (z-p_q)^n_q est analytique
  set ψ : ℂ → ℂ := fun z => φ z - w * (z - p_q) ^ n_q with hψ_def
  have hψ_an : AnalyticAt ℂ ψ p_q :=
    hφ_an.sub (analyticAt_const.mul hpow_an)
    -- Étape 4 : ψ p_q ≠ 0
  have hψ_ne : ψ p_q ≠ 0 := by
    have h0 : (0:ℂ) ^ n_q = 0 := zero_pow hn_q_pos.ne'
    simp [hψ_def, h0, hφ_ne]
  -- Étape 5 : (fun x => f x - w) =ᶠ[nhdsWithin p_q {p_q}ᶜ] (z-p_q)^(-n_q) • ψ
  have heq : ∀ᶠ z in nhdsWithin p_q {p_q}ᶜ,
      f z - w = (z - p_q) ^ (-(n_q : ℤ)) • ψ z := by
    filter_upwards [hφ_eq, self_mem_nhdsWithin] with z hz hz_ne
    have hz_ne' : z ≠ p_q := hz_ne
    have hzp : (z - p_q) ≠ 0 := sub_ne_zero.mpr hz_ne'
    rw [hz]
    simp only [hψ_def, smul_eq_mul, mul_sub]
    rw [zpow_neg, zpow_natCast]
    field_simp
  -- Étape 6 : conclusion via meromorphicOrderAt_eq_int_iff
  have hmero_sub : MeromorphicAt (fun x => f x - w) p_q :=
    hf_mero.sub (AnalyticAt.meromorphicAt analyticAt_const)
  exact (meromorphicOrderAt_eq_int_iff hmero_sub).mpr ⟨ψ, hψ_an, hψ_ne, heq⟩

lemma meromorphicAt_of_order_ne_top (H : ℂ → ℂ) (p_q : ℂ) (n_q : ℕ) (hn_q_pos : 0 < n_q)
    (hH_order : meromorphicOrderAt H p_q = -(n_q : ℤ)) :
    MeromorphicAt H p_q := by
  by_contra hcontra
  have hzero : meromorphicOrderAt H p_q = 0 :=
    meromorphicOrderAt_of_not_meromorphicAt hcontra
  rw [hzero] at hH_order
  simp at hH_order
  omega

lemma forme_normale_pole
    (H : ℂ → ℂ) (p_q : ℂ) (n_q : ℕ) (_ : 0 < n_q)
    (hH_mero : MeromorphicAt H p_q)
    (hH_order : meromorphicOrderAt H p_q = -(n_q : ℤ)) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ p_q ∧ φ p_q ≠ 0 ∧
      H =ᶠ[nhdsWithin p_q {p_q}ᶜ] fun x => (x - p_q : ℂ) ^ (-(n_q : ℤ)) * φ x := by
  obtain ⟨φ, hφ_an, hφ_nz, hHφ⟩ := (meromorphicOrderAt_eq_int_iff hH_mero).mp hH_order
  refine ⟨φ, hφ_an, hφ_nz, ?_⟩
  filter_upwards [hHφ] with z hz
  rw [hz, zpow_neg, zpow_natCast, smul_eq_mul]



lemma step1_deriv_sub (p_q x : ℂ) : HasDerivAt (fun z : ℂ => z - p_q) 1 x :=
  (hasDerivAt_id x).sub_const p_q

lemma step2_deriv_pow (p_q x : ℂ) (n_q : ℕ) :
    HasDerivAt (fun z : ℂ => (z - p_q) ^ n_q) ((n_q : ℂ) * (x - p_q) ^ (n_q - 1)) x := by
  have h := (step1_deriv_sub p_q x).pow n_q
  simp only [mul_one] at h
  convert h using 1


lemma step3_deriv_inv (p_q x : ℂ) (n_q : ℕ) (hx : x - p_q ≠ 0) :
    HasDerivAt (fun z : ℂ => ((z - p_q) ^ n_q)⁻¹)
      (-((n_q : ℂ) * (x - p_q) ^ (n_q - 1)) / ((x - p_q) ^ n_q) ^ 2) x :=
  (step2_deriv_pow p_q x n_q).inv (pow_ne_zero n_q hx)

lemma step4_fun_eq (p_q : ℂ) (n_q : ℕ) :
    (fun z : ℂ => (z - p_q) ^ (-(n_q : ℤ))) = (fun z : ℂ => ((z - p_q) ^ n_q)⁻¹) := by
  funext z
  rw [zpow_neg, zpow_natCast]

lemma step5_val_eq (p_q x : ℂ) (n_q : ℕ) (hx : x - p_q ≠ 0) :
    (x - p_q) ^ (-(n_q : ℤ) - 1) = ((x - p_q) ^ n_q)⁻¹ * (x - p_q)⁻¹ := by
  rw [zpow_sub₀ hx, zpow_neg, zpow_natCast, zpow_one, div_eq_mul_inv]

lemma step6_algebra (p_q x : ℂ) (m : ℕ) (hx : x - p_q ≠ 0) :
    -((m.succ : ℂ) * (x - p_q) ^ (m.succ - 1)) / ((x - p_q) ^ m.succ) ^ 2
      = (-(m.succ : ℤ) : ℂ) * (((x - p_q) ^ m.succ)⁻¹ * (x - p_q)⁻¹) := by
  have hpow_ne : (x - p_q) ^ m.succ ≠ 0 := pow_ne_zero _ hx
  simp only [Nat.succ_sub_one, pow_succ]
  push_cast
  field_simp

lemma step7_zero_case (x : ℂ) :
    -((0:ℂ) * (x) ^ (0 - 1)) / ((x) ^ 0) ^ 2
      = (-(0:ℤ) : ℂ) * (((x) ^ 0)⁻¹ * (x)⁻¹) := by
  simp

lemma deriv_zpow_neg_natCast (p_q : ℂ) (n_q : ℕ) (x : ℂ) (hx : x - p_q ≠ 0) :
    HasDerivAt (fun z : ℂ => (z - p_q) ^ (-(n_q : ℤ)))
      ((-(n_q : ℤ) : ℂ) * (x - p_q) ^ (-(n_q : ℤ) - 1)) x := by
  rw [step4_fun_eq p_q n_q]
  have hinv := step3_deriv_inv p_q x n_q hx
  convert hinv using 1
  rw [step5_val_eq p_q x n_q hx]
  rcases n_q with _ | m
  · simp
  · exact (step6_algebra p_q x m hx).symm


lemma phi_differentiable_ev (φ : ℂ → ℂ) (p_q : ℂ)
    (hφ_an : AnalyticAt ℂ φ p_q) :
    ∀ᶠ x in nhds p_q, DifferentiableAt ℂ φ x :=
  Complex.analyticAt_iff_eventually_differentiableAt.mp hφ_an

lemma phi_ne_zero_ev (φ : ℂ → ℂ) (p_q : ℂ)
    (hφ_an : AnalyticAt ℂ φ p_q) (hφ_nz : φ p_q ≠ 0) :
    ∀ᶠ x in nhds p_q, φ x ≠ 0 :=
  hφ_an.continuousAt.eventually_ne hφ_nz

lemma sub_ne_zero_of_ne_point (p_q x : ℂ) (hx_ne : x ≠ p_q) :
    (x - p_q : ℂ) ≠ 0 :=
  sub_ne_zero.mpr hx_ne


lemma deriv_congr_of_eventuallyEq_nhds
    {H g : ℂ → ℂ} {x : ℂ} (h : H =ᶠ[nhds x] g) :
    deriv H x = deriv g x :=
  h.deriv_eq

lemma eventuallyEq_nhds_of_mem_open
    {H g : ℂ → ℂ} {x : ℂ} {U : Set ℂ}
    (hUopen : IsOpen U)
    (hUeq : U ⊆ {z | H z = g z})
    (hxU : x ∈ U) :
    H =ᶠ[nhds x] g :=
  Filter.eventuallyEq_of_mem (hUopen.mem_nhds hxU) hUeq

lemma deriv_H_eq_deriv_forme_normale
    (H φ : ℂ → ℂ) (p_q : ℂ) (n_q : ℕ) (x : ℂ)
    (hHφ_x : H =ᶠ[nhds x] fun z => (z - p_q : ℂ) ^ (-(n_q : ℤ)) * φ z) :
    deriv H x = deriv (fun z => (z - p_q : ℂ) ^ (-(n_q : ℤ)) * φ z) x :=
  hHφ_x.deriv_eq

lemma hasDerivAt_forme_normale
    (φ : ℂ → ℂ) (p_q : ℂ) (n_q : ℕ) (x : ℂ)
    (hxp_ne : (x - p_q : ℂ) ≠ 0)
    (hφx_diff : DifferentiableAt ℂ φ x) :
    HasDerivAt (fun z => (z - p_q : ℂ) ^ (-(n_q : ℤ)) * φ z)
      ((-(n_q : ℤ) : ℂ) * (x - p_q) ^ (-(n_q : ℤ) - 1) * φ x
        + (x - p_q : ℂ) ^ (-(n_q : ℤ)) * deriv φ x) x :=
  (deriv_zpow_neg_natCast p_q n_q x hxp_ne).mul hφx_diff.hasDerivAt

lemma deriv_H_valeur
    (H φ : ℂ → ℂ) (p_q : ℂ) (n_q : ℕ) (x : ℂ)
    (hHφ_x : H =ᶠ[nhds x] fun z => (z - p_q : ℂ) ^ (-(n_q : ℤ)) * φ z)
    (hxp_ne : (x - p_q : ℂ) ≠ 0)
    (hφx_diff : DifferentiableAt ℂ φ x) :
    deriv H x =
      (-(n_q : ℤ) : ℂ) * (x - p_q) ^ (-(n_q : ℤ) - 1) * φ x
        + (x - p_q : ℂ) ^ (-(n_q : ℤ)) * deriv φ x := by
  rw [deriv_H_eq_deriv_forme_normale H φ p_q n_q x hHφ_x]
  exact (hasDerivAt_forme_normale φ p_q n_q x hxp_ne hφx_diff).deriv

lemma zpow_neg_natCast_ne_zero (p_q x : ℂ) (n_q : ℕ) (hxp_ne : (x - p_q : ℂ) ≠ 0) :
    (x - p_q : ℂ) ^ (-(n_q : ℤ)) ≠ 0 :=
  zpow_ne_zero _ hxp_ne

lemma zpow_neg_natCast_sub_one (p_q x : ℂ) (n_q : ℕ) (hxp_ne : (x - p_q : ℂ) ≠ 0) :
    (x - p_q : ℂ) ^ (-(n_q : ℤ) - 1) = (x - p_q : ℂ) ^ (-(n_q : ℤ)) / (x - p_q) := by
  rw [zpow_sub₀ hxp_ne, zpow_one]

lemma H_ne_zero_of_forme_normale
    (H φ : ℂ → ℂ) (p_q : ℂ) (n_q : ℕ) (x : ℂ)
    (hx_eq : H x = (x - p_q : ℂ) ^ (-(n_q : ℤ)) * φ x)
    (hxp_ne : (x - p_q : ℂ) ≠ 0)
    (hφx_ne : φ x ≠ 0) :
    H x ≠ 0 := by
  rw [hx_eq]
  exact mul_ne_zero (zpow_neg_natCast_ne_zero p_q x n_q hxp_ne) hφx_ne

lemma calcul_final_derivee_log
    (p_q x φx dφx : ℂ) (n_q : ℕ)
    (hxp_ne : (x - p_q : ℂ) ≠ 0)
    (hφx_ne : φx ≠ 0) :
    ((-(n_q : ℤ) : ℂ) * ((x - p_q : ℂ) ^ (-(n_q : ℤ)) / (x - p_q)) * φx
        + (x - p_q : ℂ) ^ (-(n_q : ℤ)) * dφx)
      / ((x - p_q : ℂ) ^ (-(n_q : ℤ)) * φx)
    = (-(n_q : ℤ) : ℂ) / (x - p_q) + dφx / φx := by
  have hxpow_ne : (x - p_q : ℂ) ^ (-(n_q : ℤ)) ≠ 0 := zpow_ne_zero _ hxp_ne
  field_simp

lemma derivee_logarithmique_forme_normale_pole_point
    (H φ : ℂ → ℂ) (p_q : ℂ) (n_q : ℕ) (x : ℂ)
    (hx_eq : H x = (x - p_q : ℂ) ^ (-(n_q : ℤ)) * φ x)
    (hHφ_x : H =ᶠ[nhds x] fun z => (z - p_q : ℂ) ^ (-(n_q : ℤ)) * φ z)
    (hφx_diff : DifferentiableAt ℂ φ x)
    (hφx_ne : φ x ≠ 0)
    (hx_ne : x ≠ p_q) :
    deriv H x / H x = (-(n_q : ℤ) : ℂ) / (x - p_q) + deriv φ x / φ x := by
  have hxp_ne : (x - p_q : ℂ) ≠ 0 :=
    sub_ne_zero_of_ne_point p_q x hx_ne
  have hderiv_H : deriv H x =
      (-(n_q : ℤ) : ℂ) * (x - p_q) ^ (-(n_q : ℤ) - 1) * φ x
        + (x - p_q : ℂ) ^ (-(n_q : ℤ)) * deriv φ x := by
    rw [Filter.EventuallyEq.deriv_eq hHφ_x]
    exact (hasDerivAt_forme_normale φ p_q n_q x hxp_ne hφx_diff).deriv
  have hzpow_split : (x - p_q : ℂ) ^ (-(n_q : ℤ) - 1) =
      (x - p_q : ℂ) ^ (-(n_q : ℤ)) / (x - p_q) :=
    zpow_neg_natCast_sub_one p_q x n_q hxp_ne
  rw [hderiv_H, hx_eq, hzpow_split]
  exact calcul_final_derivee_log p_q x (φ x) (deriv φ x) n_q hxp_ne hφx_ne

theorem derivee_logarithmique_forme_normale_pole
    (H φ : ℂ → ℂ) (p_q : ℂ) (n_q : ℕ)
    (hφ_an : AnalyticAt ℂ φ p_q)
    (hφ_nz : φ p_q ≠ 0)
    (hHφ : H =ᶠ[nhds p_q] fun x => (x - p_q : ℂ) ^ (-(n_q : ℤ)) * φ x) :
    ∀ᶠ x in nhds p_q, x ≠ p_q →
      deriv H x / H x = (-(n_q : ℤ) : ℂ) / (x - p_q) + deriv φ x / φ x := by
  filter_upwards [hHφ.eventually_nhds,
    phi_differentiable_ev φ p_q hφ_an,
    phi_ne_zero_ev φ p_q hφ_an hφ_nz] with x hx_eq hφx_diff hφx_ne
  intro hx_ne
  have hx_eq' : H x = (x - p_q : ℂ) ^ (-(n_q : ℤ)) * φ x :=
    hx_eq.self_of_nhds
  exact derivee_logarithmique_forme_normale_pole_point H φ p_q n_q x
    hx_eq' hx_eq hφx_diff hφx_ne hx_ne


----------------------------------------------------------------



lemma pole_mul_of_pole
    {Ω₁ : Set ℂ} {h₁ h₂ : ℂ → ℂ}
    (h₁mero : MeromorphicOn h₁ Ω₁) (h₂mero : MeromorphicOn h₂ Ω₁)
    {x : ℂ} (hx : x ∈ Ω₁)
    (hprod : meromorphicOrderAt (h₁ * h₂) x < 0) :
    meromorphicOrderAt h₁ x < 0 ∨ meromorphicOrderAt h₂ x < 0 := by
  by_contra h
  push Not at h
  rw [meromorphicOrderAt_mul (h₁mero x hx) (h₂mero x hx)] at hprod
  exact (not_lt_of_ge (add_nonneg h.1 h.2)) hprod


lemma no_poles_pow_id (Ω₁ : Set ℂ) (k : ℕ) :
    poles (fun x : ℂ => x ^ k) Ω₁ = ∅ := by
  ext x
  simp only [poles, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hxΩ
  exact (analyticAt_id.pow k).meromorphicOrderAt_nonneg


lemma pole_mul_of_pole'
    {Ω₁ : Set ℂ} {h₁ h₂ : ℂ → ℂ}
    (h₁mero : MeromorphicOn h₁ Ω₁)
    (h₂mero : MeromorphicOn h₂ Ω₁) :
    poles (h₁ * h₂) Ω₁ ⊆ poles h₁ Ω₁ ∪ poles h₂ Ω₁ := by
  intro x hx
  rcases hx with ⟨hxΩ, hxprod⟩
  have hor : meromorphicOrderAt h₁ x < 0 ∨ meromorphicOrderAt h₂ x < 0 :=
    pole_mul_of_pole h₁mero h₂mero hxΩ hxprod
  rcases hor with hor | hor
  · exact Or.inl ⟨hxΩ, hor⟩
  · exact Or.inr ⟨hxΩ, hor⟩

lemma poles_deriv_subset
    {Ω₁ : Set ℂ} {f : ℂ → ℂ}
    (hf : MeromorphicOn f Ω₁) :
    poles (deriv f) Ω₁ ⊆ poles f Ω₁ := by
  intro x hx
  rcases hx with ⟨hxΩ, hxderiv⟩
  by_contra hnot
  simp only [poles, Set.mem_ofPred_eq, not_and] at hnot
  have hnonpole : 0 ≤ meromorphicOrderAt f x := le_of_not_gt (hnot hxΩ)
  have hfan : AnalyticAt ℂ f x := canonical_extension hf x hxΩ hnonpole
  have hderivan : AnalyticAt ℂ (deriv f) x := hfan.deriv
  have hderiv_nonneg : 0 ≤ meromorphicOrderAt (deriv f) x :=
    hderivan.meromorphicOrderAt_nonneg
  exact (not_lt_of_ge hderiv_nonneg) hxderiv


lemma poles_inv_sub_const_subset_solutions
    {Ω₁ : Set ℂ} {f : ℂ → ℂ} {c : ℂ}
    (hf : MeromorphicOn f Ω₁) :
    poles (fun x => (f x - c)⁻¹) Ω₁ ⊆ ensembleSolutions f Ω₁ c ∪ poles f Ω₁ := by
  intro x hx
  by_contra hnot
  have hnot' : x ∉ ensembleSolutions f Ω₁ c ∧ x ∉ poles f Ω₁ := by
    simpa only [Set.mem_union, not_or] using hnot
  have hx' : x ∈ Ω₁ ∧ meromorphicOrderAt (fun z => (f z - c)⁻¹) x < 0 := by
    simpa only [poles, Set.mem_ofPred_eq] using hx
  rcases hx' with ⟨hxΩ, hxinvpole⟩
  rcases lt_or_ge (meromorphicOrderAt f x) 0 with hfpole | hforder
  · exact hnot'.2 ⟨hxΩ, hfpole⟩
  · have hfan : AnalyticAt ℂ f x := canonical_extension hf x hxΩ hforder
    have hsuban : AnalyticAt ℂ (fun z => f z - c) x := by
      change AnalyticAt ℂ (f - fun _ : ℂ => c) x
      exact hfan.sub analyticAt_const
    have hne : f x - c ≠ 0 := by
      intro hz
      exact hnot'.1 ⟨hxΩ, sub_eq_zero.mp hz⟩
    have hinvan : AnalyticAt ℂ (fun z => (f z - c)⁻¹) x := hsuban.inv hne
    exact (not_lt_of_ge hinvan.meromorphicOrderAt_nonneg) hxinvpole

open Meromorphic_On in
lemma poles_formeSpectrale_subset_solutions_union_poles
    {Ω₁ : Set ℂ} {f : ℂ → ℂ} {c : ℂ} {k : ℕ}
    (hf : MeromorphicOn f Ω₁) :
    poles (formeSpectrale f c k) Ω₁ ⊆
      ensembleSolutions f Ω₁ c ∪ poles f Ω₁ := by
  have hpow : MeromorphicOn (fun x : ℂ => x ^ k) Ω₁ := meromorphicOn_pow_id k
  have hderiv : MeromorphicOn (deriv f) Ω₁ := hf.deriv
  have hsub : MeromorphicOn (fun x => f x - c) Ω₁ := hf.sub (MeromorphicOn.const c)
  have hinv : MeromorphicOn (fun x => (f x - c)⁻¹) Ω₁ := hsub.inv
  have hpow_no : poles (fun x : ℂ => x ^ k) Ω₁ = ∅ := no_poles_pow_id Ω₁ k
  have hderiv_sub : poles (deriv f) Ω₁ ⊆ poles f Ω₁ := poles_deriv_subset hf
  have hinv_sub : poles (fun x => (f x - c)⁻¹) Ω₁ ⊆ ensembleSolutions f Ω₁ c ∪ poles f Ω₁ :=
    poles_inv_sub_const_subset_solutions hf
  intro x hx
  simp only [poles, Set.mem_ofPred_eq] at hx
  obtain ⟨hxΩ, hxorder⟩ := hx
  have houter := pole_mul_of_pole (hpow.mul hderiv) hinv hxΩ hxorder
  rcases houter with hnum_pole | hinv_pole
  · have hinner := pole_mul_of_pole' hpow hderiv ⟨hxΩ, hnum_pole⟩
    rcases hinner with hpow_pole | hderiv_pole
    · exfalso; rw [hpow_no] at hpow_pole; exact hpow_pole
    · exact Or.inr (hderiv_sub hderiv_pole)
  · exact hinv_sub ⟨hxΩ, hinv_pole⟩





end NormalFormPoleThEq
