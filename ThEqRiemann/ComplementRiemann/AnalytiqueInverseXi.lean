import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.ComplementRiemann.LogDerivationXi
import ThEqRiemann.ComplementRiemann.ConvexeIntegration

/-! -/
namespace AnalytiqueInvXi

open Set Complex
open RiemannDef LogDerivXi

lemma integrande_un_decompose (z : ℂ) (hs : 0 < ((1 / 2 : ℂ) + z).re)
    (h1 : (1 / 2 : ℂ) + z ≠ 1) (hzeta : riemannZeta ((1 / 2 : ℂ) + z) ≠ 0) :
    z * (deriv xi ((1 / 2 : ℂ) + z) / xi ((1 / 2 : ℂ) + z))
      = z * (1 / ((1 / 2 : ℂ) + z) - 1 / ((1 / 2 : ℂ) - z))
        + (-(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)) * z
        + (1 / 2 : ℂ) * (z * (deriv Complex.Gamma (1 / 4 + z / 2)
              / Complex.Gamma (1 / 4 + z / 2)))
        + z * (deriv riemannZeta ((1 / 2 : ℂ) + z) / riemannZeta ((1 / 2 : ℂ) + z)) := by
  rw [deriv_log_xi _ hs h1 hzeta]
  have hs2 : ((1 / 2 : ℂ) + z) / 2 = 1 / 4 + z / 2 := by ring
  have hz1 : (1 / 2 : ℂ) + z - 1 = -((1 / 2 : ℂ) - z) := by ring
  rw [hs2, hz1, one_div_neg_eq_neg_one_div]
  ring

lemma integrale_lacet_somme4 (γ : ℝ → ℂ) (f₁ f₂ f₃ f₄ : ℂ → ℂ)
    (h₁ : IntervalIntegrable (fun t => deriv γ t * f₁ (γ t)) MeasureTheory.volume 0 1)
    (h₂ : IntervalIntegrable (fun t => deriv γ t * f₂ (γ t)) MeasureTheory.volume 0 1)
    (h₃ : IntervalIntegrable (fun t => deriv γ t * f₃ (γ t)) MeasureTheory.volume 0 1)
    (h₄ : IntervalIntegrable (fun t => deriv γ t * f₄ (γ t)) MeasureTheory.volume 0 1) :
    (∫ t in (0 : ℝ)..1, deriv γ t * (f₁ (γ t) + f₂ (γ t) + f₃ (γ t) + f₄ (γ t)))
      = (∫ t in (0 : ℝ)..1, deriv γ t * f₁ (γ t))
        + (∫ t in (0 : ℝ)..1, deriv γ t * f₂ (γ t))
        + (∫ t in (0 : ℝ)..1, deriv γ t * f₃ (γ t))
        + (∫ t in (0 : ℝ)..1, deriv γ t * f₄ (γ t)) := by
  simp only [mul_add]
  rw [intervalIntegral.integral_add ((h₁.add h₂).add h₃) h₄,
    intervalIntegral.integral_add (h₁.add h₂) h₃,
    intervalIntegral.integral_add h₁ h₂]

lemma integrale_lacet_id_nulle (γ : ℝ → ℂ) (hclos : γ 0 = γ 1)
    (hdiff : ∀ t, DifferentiableAt ℝ γ t)
    (hcont : Continuous (deriv γ)) :
    (∫ t in (0 : ℝ)..1, deriv γ t * γ t) = 0 := by
  have hprim : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => γ s ^ 2 / 2) (deriv γ t * γ t) t := by
    intro t _
    have h1 : HasDerivAt γ (deriv γ t) t := (hdiff t).hasDerivAt
    have h2 := (h1.pow 2).div_const 2
    convert h2 using 1
    simp
    ring
  have hint : IntervalIntegrable (fun t => deriv γ t * γ t) MeasureTheory.volume 0 1 := by
    have hγc : Continuous γ := continuous_iff_continuousAt.mpr
      (fun t => (hdiff t).continuousAt)
    exact (hcont.mul hγc).intervalIntegrable 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hint]
  rw [hclos]
  ring

lemma formule_explicite_algebrique (I₁ I₂ I₄ L : ℂ) (hL : L = 0) :
    (1 / (2 * Complex.I * (Real.pi : ℂ))) *
    (I₁ + (-(1/2 : ℂ) * (Real.log Real.pi : ℂ)) * L
        + (1/2 : ℂ) * I₂ + I₄)
      = (1 / (2 * Complex.I * (Real.pi : ℂ))) * I₁
        + (1 / (4 * Complex.I * (Real.pi : ℂ))) * I₂
        + (1 / (2 * Complex.I * (Real.pi : ℂ))) * I₄ := by
  subst hL
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp
  ring

---------------------------------------------------------------------

lemma hasDerivAt_comp_lacet (γ : ℝ → ℂ) (F : ℂ → ℂ) (t : ℝ) (γ' F' : ℂ)
    (h1 : HasDerivAt γ γ' t) (h2 : HasDerivAt F F' (γ t)) :
    HasDerivAt (fun s => F (γ s)) (γ' * F') t := by
  have h3 : HasDerivAt (F ∘ γ) (γ' • F') t := HasDerivAt.scomp t h2 h1
  simpa [Function.comp_def, smul_eq_mul] using h3

lemma integrale_lacet_primitive (γ : ℝ → ℂ) (hclos : γ 0 = γ 1)
    (hdiff : ∀ t, DifferentiableAt ℝ γ t)
    (hcont : Continuous (deriv γ))
    (U : Set ℂ) (hγU : ∀ t ∈ Set.uIcc (0 : ℝ) 1, γ t ∈ U)
    (F f : ℂ → ℂ) (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hfc : ContinuousOn f U) :
    (∫ t in (0 : ℝ)..1, deriv γ t * f (γ t)) = 0 := by
  have hprim : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => F (γ s)) (deriv γ t * f (γ t)) t := by
    intro t ht
    exact hasDerivAt_comp_lacet γ F t (deriv γ t) (f (γ t))
      (hdiff t).hasDerivAt (hF _ (hγU t ht))
  have hint : IntervalIntegrable (fun t => deriv γ t * f (γ t))
      MeasureTheory.volume 0 1 := by
    have hγc : Continuous γ :=
      continuous_iff_continuousAt.mpr (fun t => (hdiff t).continuousAt)
    have hγcU : ContinuousOn (fun t => f (γ t)) (Set.uIcc (0 : ℝ) 1) :=
      hfc.comp hγc.continuousOn hγU
    exact (hcont.continuousOn.mul hγcU).intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim hint, hclos]
  ring

lemma hasDerivAt_primitive_rationnel (z : ℂ) (h1 : -(1 / 2 : ℝ) < z.re)
    (h2 : z.re < 1 / 2) :
    HasDerivAt (fun w : ℂ => 2 * w - (1/2 : ℂ) * Complex.log ((1/2 : ℂ) + w)
        + (1/2 : ℂ) * Complex.log ((1/2 : ℂ) - w))
      (z * (1 / ((1/2 : ℂ) + z) - 1 / ((1/2 : ℂ) - z))) z := by
  have ha : ((1/2 : ℂ) + z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp; linarith
  have hb : ((1/2 : ℂ) - z) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]; left; simp; linarith
  have hne1 : (1/2 : ℂ) + z ≠ 0 := Complex.slitPlane_ne_zero ha
  have hne2 : (1/2 : ℂ) - z ≠ 0 := Complex.slitPlane_ne_zero hb
  have hl1 : HasDerivAt (fun w : ℂ => Complex.log ((1/2 : ℂ) + w))
      (1 / ((1/2 : ℂ) + z)) z := by
    have := ((hasDerivAt_id z).const_add (1/2 : ℂ)).clog ha
    simpa using this
  have hl2 : HasDerivAt (fun w : ℂ => Complex.log ((1/2 : ℂ) - w))
      (-1 / ((1/2 : ℂ) - z)) z := by
    have := ((hasDerivAt_id z).const_sub (1/2 : ℂ)).clog hb
    simpa using this
  have h := (((hasDerivAt_id z).const_mul 2).sub (hl1.const_mul (1/2 : ℂ))).add
    (hl2.const_mul (1/2 : ℂ))
  convert h using 1
  · funext w
    simp only [Pi.add_apply, Pi.sub_apply, id]
  · have hA : (1 + z * 2 : ℂ) ≠ 0 := by
      intro h0
      apply hne1
      linear_combination (1/2 : ℂ) * h0
    have hB : (1 - z * 2 : ℂ) ≠ 0 := by
      intro h0
      apply hne2
      linear_combination (1/2 : ℂ) * h0
    field_simp
    ring

lemma annulation_rationnel (γ : ℝ → ℂ) (hclos : γ 0 = γ 1)
    (hdiff : ∀ t, DifferentiableAt ℝ γ t)
    (hcont : Continuous (deriv γ))
    (hbande : ∀ t ∈ Set.uIcc (0 : ℝ) 1, -(1 / 2 : ℝ) < (γ t).re ∧ (γ t).re < 1 / 2) :
    (∫ t in (0 : ℝ)..1, deriv γ t *
        (γ t * (1 / ((1 / 2 : ℂ) + γ t) - 1 / ((1 / 2 : ℂ) - γ t)))) = 0 := by
  apply integrale_lacet_primitive γ hclos hdiff hcont
    {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2} hbande
    _ (fun z => z * (1 / ((1/2 : ℂ) + z) - 1 / ((1/2 : ℂ) - z)))
  · intro z hz
    exact hasDerivAt_primitive_rationnel z hz.1 hz.2
  · intro z hz
    have hne1 : (1/2 : ℂ) + z ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith [hz.1]
    have hne2 : (1/2 : ℂ) - z ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      simp at this
      linarith [hz.2]
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := assumption)

lemma annulation_gamma (γ : ℝ → ℂ) (hclos : γ 0 = γ 1)
    (hdiff : ∀ t, DifferentiableAt ℝ γ t)
    (hcont : Continuous (deriv γ))
    (hbande : ∀ t ∈ Set.uIcc (0 : ℝ) 1, -(1 / 2 : ℝ) < (γ t).re ∧ (γ t).re < 1 / 2)
    (G : ℂ → ℂ)
    (hG : ∀ z : ℂ, -(1/2 : ℝ) < z.re → z.re < 1/2 →
      HasDerivAt G (z * (deriv Complex.Gamma (1/4 + z/2) /
      Complex.Gamma (1/4 + z/2))) z)
    (hfc : ContinuousOn (fun z : ℂ => z * (deriv Complex.Gamma (1/4 + z/2)
        / Complex.Gamma (1/4 + z/2))) {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2}) :
    (∫ t in (0 : ℝ)..1, deriv γ t *
        (γ t * (deriv Complex.Gamma (1/4 + γ t/2) / Complex.Gamma (1/4 + γ t/2))))
        = 0 :=
  integrale_lacet_primitive γ hclos hdiff hcont
    {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2} hbande G _
    (fun z (hz : z ∈ {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2}) =>
      hG z hz.1 hz.2) hfc

lemma differentiableAt_deriv_Gamma (w : ℂ) (hw : 0 < w.re) :
    DifferentiableAt ℂ (deriv Complex.Gamma) w := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hdiffOn : DifferentiableOn ℂ Complex.Gamma {u : ℂ | 0 < u.re} := by
    intro u hu
    apply DifferentiableAt.differentiableWithinAt
    apply Complex.differentiableAt_Gamma
    intro m h
    have hre := congrArg Complex.re h
    simp at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hu' : 0 < u.re := hu
    linarith
  have hAn : AnalyticAt ℂ Complex.Gamma w :=
    hdiffOn.analyticAt (hopen.mem_nhds hw)
  exact hAn.deriv.differentiableAt

lemma re_quart_add_demi_pos (z : ℂ) (h : -(1 / 2 : ℝ) < z.re) :
    0 < ((1/4 : ℂ) + z/2).re := by
  have h1 : ((1/4 : ℂ) + z/2).re = 1/4 + z.re / 2 := by
    simp [Complex.add_re]
  rw [h1]
  linarith

lemma quart_add_demi_ne_pole (z : ℂ) (h : -(1 / 2 : ℝ) < z.re) :
    ∀ m : ℕ, (1/4 : ℂ) + z/2 ≠ -(m : ℂ) := by
  intro m hm
  have hpos := re_quart_add_demi_pos z h
  have hre : ((1/4 : ℂ) + z/2).re = (-(m : ℂ)).re := by rw [hm]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  simp at hre
  rw [hm] at hpos
  simp at hpos
  linarith

lemma differentiableAt_comp_quart (g : ℂ → ℂ) (z : ℂ)
    (hg : DifferentiableAt ℂ g ((1 / 4 : ℂ) + z / 2)) :
    DifferentiableAt ℂ (fun y : ℂ => g ((1/4 : ℂ) + y/2)) z := by
  have hin : DifferentiableAt ℂ (fun y : ℂ => (1/4 : ℂ) + y/2) z := by fun_prop
  exact DifferentiableAt.comp (g := g) z hg hin

lemma differentiableAt_integrande_gamma (z : ℂ) (h : -(1 / 2 : ℝ) < z.re) :
    DifferentiableAt ℂ (fun y : ℂ => y * (deriv Complex.Gamma (1/4 + y/2)
      / Complex.Gamma (1/4 + y/2))) z := by
  have hne := quart_add_demi_ne_pole z h
  have hpos := re_quart_add_demi_pos z h
  have hΓd : DifferentiableAt ℂ Complex.Gamma ((1/4 : ℂ) + z/2) :=
    Complex.differentiableAt_Gamma _ hne
  have hΓ0 : Complex.Gamma ((1/4 : ℂ) + z/2) ≠ 0 := Complex.Gamma_ne_zero hne
  have hd' : DifferentiableAt ℂ (deriv Complex.Gamma) ((1/4 : ℂ) + z/2) :=
    differentiableAt_deriv_Gamma _ hpos
  have h1 := differentiableAt_comp_quart (deriv Complex.Gamma) z hd'
  have h2 := differentiableAt_comp_quart Complex.Gamma z hΓd
  exact differentiableAt_id.mul (h1.div h2 hΓ0)



lemma differentiableOn_integrande_gamma :
    DifferentiableOn ℂ (fun y : ℂ => y * (deriv Complex.Gamma (1/4 + y/2)
      / Complex.Gamma (1/4 + y/2))) {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2} :=
  fun z hz =>
  (differentiableAt_integrande_gamma z hz.1).differentiableWithinAt



--------------------------------------------------------------


open ConvIntegration

lemma gamma_argument_ne_neg_nat {z : ℂ} (h1 : -(1 / 2 : ℝ) < z.re) (_ : z.re < 1 / 2) :
    ∀ m : ℕ, (1 / 4 : ℂ) + z/2 ≠ -(m : ℂ) := by
  intro m hm
  have := congrArg Complex.re hm
  simp at this
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma existe_primitive_gamma :
    ∃ G : ℂ → ℂ, ∀ z : ℂ, -(1/2 : ℝ) < z.re → z.re < 1/2 →
      HasDerivAt G (z * (deriv Complex.Gamma (1/4 + z/2)
        / Complex.Gamma (1/4 + z/2))) z := by
  obtain ⟨G, hG⟩ := differentiableOn_exists_primitive_bande
    differentiableOn_integrande_gamma
  exact ⟨G, fun z h1 h2 => hG z ⟨h1, h2⟩⟩

lemma annulation_gamma_lacet (γ : ℝ → ℂ) (hclos : γ 0 = γ 1)
    (hdiff : ∀ t, DifferentiableAt ℝ γ t)
    (hcont : Continuous (deriv γ))
    (hbande : ∀ t ∈ Set.uIcc (0 : ℝ) 1, -(1 / 2 : ℝ) < (γ t).re ∧ (γ t).re < 1 / 2) :
    ∫ t in (0 : ℝ)..1, deriv γ t *
        (γ t * (deriv Complex.Gamma (1/4 + γ t/2) / Complex.Gamma (1/4 + γ t/2))) = 0 := by
  have hfc : ContinuousOn (fun z : ℂ => z * (deriv Complex.Gamma (1/4 + z/2)
      / Complex.Gamma (1/4 + z/2))) {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2} := by
    intro z hz
    exact (differentiableAt_integrande_gamma z hz.1).continuousAt.continuousWithinAt
  obtain ⟨G, hG⟩ := existe_primitive_gamma
  exact annulation_gamma γ hclos hdiff hcont hbande G hG hfc


theorem reduction_analytic_inverse_zeta (γ : ℝ → ℂ) (hclos : γ 0 = γ 1)
    (hdiff : ∀ t, DifferentiableAt ℝ γ t)
    (hcont : Continuous (deriv γ))
    (hbande : ∀ t ∈ Set.uIcc (0 : ℝ) 1, -(1 / 2 : ℝ) < (γ t).re ∧ (γ t).re < 1 / 2)
    (I₁ I₂ I₄ : ℂ)
    (hI₁ : I₁ = ∫ t in (0 : ℝ)..1, deriv γ t *
        (γ t * (1 / ((1 / 2 : ℂ) + γ t) - 1 / ((1 / 2 : ℂ) - γ t))))
    (hI₂ : I₂ = ∫ t in (0 : ℝ)..1, deriv γ t *
        (γ t * (deriv Complex.Gamma (1 / 4 + γ t / 2) / Complex.Gamma (1 / 4 + γ t / 2))))
    (_ : I₄ = ∫ t in (0 : ℝ)..1, deriv γ t *
        (γ t * (deriv riemannZeta (1 / 2 + γ t) / riemannZeta (1 / 2 + γ t)))) :
    (1 / (2 * Complex.I * (Real.pi : ℂ))) *
      (I₁ + (-(1/2 : ℂ) * (Real.log Real.pi : ℂ)) * 0
        + (1/2 : ℂ) * I₂ + I₄)
      = (1 / (2 * Complex.I * (Real.pi : ℂ))) * I₄ := by
  have hI₁_null : I₁ = 0 := by
    rw [hI₁]
    exact annulation_rationnel γ hclos hdiff hcont hbande
  have hI₂_null : I₂ = 0 := by
    rw [hI₂]
    exact annulation_gamma_lacet γ hclos hdiff hcont hbande
  rw [hI₁_null, hI₂_null]
  simp only [zero_add]
  ring




end AnalytiqueInvXi
