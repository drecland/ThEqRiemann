import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.ComplementRiemann.EtaPartialProp
/-! -/
namespace RealPartCarac

open Set Complex
open RiemannDef EtaPartialProperty

theorem caracterisation_partie_reelle
    {c zm : ℂ} {R : ℝ} (hR : 0 < R)
    (hlim : Filter.Tendsto
      (fun N : ℕ => 1 / (2 * ↑Real.pi * I) *
        ∮ z in C(c, R), z *
          (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z)))
      Filter.atTop (nhds zm)) :
    Filter.Tendsto
      (fun N : ℕ => 1 / (4 * ↑Real.pi * I) *
        ((∮ z in C(c, R), z *
          (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z)))
        + ∮ z in C((starRingEnd ℂ) c, R),
            z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z))))
      Filter.atTop (nhds ((zm + (starRingEnd ℂ) zm) / 2)) := by
  have hconj : Filter.Tendsto
      (fun N : ℕ => (starRingEnd ℂ) (1 / (2 * ↑Real.pi * I) *
        ∮ z in C(c, R), z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z))))
      Filter.atTop (nhds ((starRingEnd ℂ) zm)) :=
    ((Complex.continuous_conj).tendsto zm).comp hlim
  have hsum := (hlim.add hconj).div_const 2
  refine hsum.congr (fun N => ?_)
  have h := conj_integral_etaPartial N c R hR.le
  set I_N := ∮ z in C(c, R), z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z))
    with hI
  set J_N := ∮ z in C((starRingEnd ℂ) c, R),
    z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z)) with hJ
  have hJ' : J_N = - (starRingEnd ℂ) I_N := by rw [h]; ring
  rw [hJ']
  simp only [map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  ring

------------------------------------------------------------------------

lemma re_eq_half_add_conj (z : ℂ) :
    (z.re : ℂ) = (z + (starRingEnd ℂ) z) / 2 := by
  rw [Complex.add_conj]
  push_cast
  ring

lemma half_sub_conj (z : ℂ) :
    (z - (starRingEnd ℂ) z) / 2 = Complex.I * (z.im : ℂ) := by
  rw [Complex.sub_conj]
  push_cast
  ring

lemma zeros_symm_imag (Z : Set ℂ)
    (hconj : ∀ z ∈ Z, (starRingEnd ℂ) z ∈ Z) (hneg : ∀ z ∈ Z, -z ∈ Z) :
    ∀ z ∈ Z, -(starRingEnd ℂ) z ∈ Z :=
  fun z hz => hneg _ (hconj z hz)

theorem AnnulationPartieReelleZeta (Z U : Set ℂ) (zm : ℂ)
    (hzm : zm ∈ Z) (hU : zm ∈ U)
    (hUsymm : ∀ z ∈ U, -(starRingEnd ℂ) z ∈ U)
    (huniq : ∀ z ∈ Z, z ∈ U → z = zm)
    (hconj : ∀ z ∈ Z, (starRingEnd ℂ) z ∈ Z) (hneg : ∀ z ∈ Z, -z ∈ Z) :
    zm.re = 0 := by
  have hmem : -(starRingEnd ℂ) zm ∈ Z := zeros_symm_imag Z hconj hneg zm hzm
  have hmemU : -(starRingEnd ℂ) zm ∈ U := hUsymm zm hU
  have heq : -(starRingEnd ℂ) zm = zm := huniq _ hmem hmemU
  have h := congrArg Complex.re heq
  simp at h
  linarith

lemma neg_conj_involutive (a : ℂ) :
    -(starRingEnd ℂ) (-(starRingEnd ℂ) a) = a := by
  simp

lemma analyticAt_conj_comp_neg_conj
    {g : ℂ → ℂ} {a : ℂ} (hg : AnalyticAt ℂ g a) :
    AnalyticAt ℂ (fun w => (starRingEnd ℂ) (g (-(starRingEnd ℂ) w)))
      (-(starRingEnd ℂ) a) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  let phi : ℂ → ℂ := fun w => -(starRingEnd ℂ) w
  have hphi : ContinuousAt phi (-(starRingEnd ℂ) a) := by
    dsimp [phi]
    fun_prop
  have hpa : phi (-(starRingEnd ℂ) a) = a := by
    simp [phi]
  have ha : ∀ᶠ z in nhds a, DifferentiableAt ℂ g z :=
    hg.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hev : ∀ᶠ w in nhds (-(starRingEnd ℂ) a),
      DifferentiableAt ℂ g (phi w) := by
    have ha' : ∀ᶠ z in nhds (phi (-(starRingEnd ℂ) a)),
        DifferentiableAt ℂ g z := by
      rw [hpa]
      exact ha
    exact hphi.eventually ha'
  filter_upwards [hev] with w hw
  have hw' : DifferentiableAt ℂ g (-(starRingEnd ℂ) w) := hw
  have hk : DifferentiableAt ℂ (fun z : ℂ => g (-z)) (starRingEnd ℂ w) := by
    have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) (starRingEnd ℂ w) :=
      differentiableAt_id.neg
    exact DifferentiableAt.comp (starRingEnd ℂ w) hw' hneg
  have hc := hk.conj_conj
  simpa [Function.comp_def, phi] using hc

lemma analyticOrderAt_symm_neg_conj_top
    {f : ℂ → ℂ} {a : ℂ}
    (hsym : ∀ z, f (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (htop : analyticOrderAt f a = ⊤) :
    analyticOrderAt f (-(starRingEnd ℂ) a) = ⊤ := by
  rw [analyticOrderAt_eq_top] at htop
  rw [analyticOrderAt_eq_top]
  let phi : ℂ → ℂ := fun w => -(starRingEnd ℂ) w
  have hphi : ContinuousAt phi (-(starRingEnd ℂ) a) := by
    dsimp [phi]
    fun_prop
  have hpa : phi (-(starRingEnd ℂ) a) = a := by
    simp [phi]
  have htop' : ∀ᶠ z in nhds (phi (-(starRingEnd ℂ) a)), f z = 0 := by
    rw [hpa]
    exact htop
  have hev : ∀ᶠ w in nhds (-(starRingEnd ℂ) a), f (phi w) = 0 :=
    hphi.eventually htop'
  filter_upwards [hev] with w hw
  have h1 : f (-(starRingEnd ℂ) w) = 0 := hw
  have h2 : f w = (starRingEnd ℂ) (f (-(starRingEnd ℂ) w)) := by
    have := hsym (-(starRingEnd ℂ) w)
    simpa using this
  rw [h2, h1, map_zero]

lemma analyticOrderAt_symm_neg_conj_finite
    {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a)
    (hsym : ∀ z, f (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (htop : analyticOrderAt f a ≠ ⊤) :
    analyticOrderAt f a ≤ analyticOrderAt f (-(starRingEnd ℂ) a) := by
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp htop
  have hk' : analyticOrderAt f a = (k : ℕ∞) := hk.symm
  obtain ⟨g, hg, hga, hfg⟩ := (hf.analyticOrderAt_eq_natCast).mp hk'
  let g' : ℂ → ℂ := fun w => (-1 : ℂ) ^ k * (starRingEnd ℂ) (g (-(starRingEnd ℂ) w))
  have hg' : AnalyticAt ℂ g' (-(starRingEnd ℂ) a) :=
    analyticAt_const.mul (analyticAt_conj_comp_neg_conj hg)
  have hg'a : g' (-(starRingEnd ℂ) a) ≠ 0 := by
    have e : -(starRingEnd ℂ) (-(starRingEnd ℂ) a) = a := by simp
    simp only [g', e]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) ((map_ne_zero _).mpr hga)
  let phi : ℂ → ℂ := fun w => -(starRingEnd ℂ) w
  have hphi : ContinuousAt phi (-(starRingEnd ℂ) a) := by
    dsimp [phi]
    fun_prop
  have hpa : phi (-(starRingEnd ℂ) a) = a := by
    simp [phi]
  have hfg' : ∀ᶠ z in nhds (phi (-(starRingEnd ℂ) a)),
      f z = (z - a) ^ k • g z := by
    rw [hpa]
    exact hfg
  have hev : ∀ᶠ w in nhds (-(starRingEnd ℂ) a),
      f w = (w - (-(starRingEnd ℂ) a)) ^ k • g' w := by
    filter_upwards [hphi.eventually hfg'] with w hw
    have h1 : f w = (starRingEnd ℂ) (f (-(starRingEnd ℂ) w)) := by
      have := hsym (-(starRingEnd ℂ) w)
      simpa using this
    have hw' : f (-(starRingEnd ℂ) w)
        = (-(starRingEnd ℂ) w - a) ^ k • g (-(starRingEnd ℂ) w) := hw
    have h3 : (starRingEnd ℂ) (-(starRingEnd ℂ) w - a)
        = -(w - (-(starRingEnd ℂ) a)) := by
      simp [map_sub, map_neg]
      ring
    rw [h1, hw', smul_eq_mul, map_mul, map_pow, h3]
    simp only [g', smul_eq_mul]
    rw [neg_pow]
    ring
  have hf' : AnalyticAt ℂ f (-(starRingEnd ℂ) a) := by
    have hpoly : AnalyticAt ℂ
        (fun w => (w - (-(starRingEnd ℂ) a)) ^ k • g' w) (-(starRingEnd ℂ) a) :=
      ((analyticAt_id.sub analyticAt_const).pow k).smul hg'
    exact hpoly.congr (hev.mono fun w hw => hw.symm)
  have hord : analyticOrderAt f (-(starRingEnd ℂ) a) = (k : ℕ∞) :=
    (hf'.analyticOrderAt_eq_natCast).mpr ⟨g', hg', hg'a, hev⟩
  rw [hk', hord]

lemma analyticOrderAt_le_symm_neg_conj
    {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (_ : AnalyticAt ℂ f (-(starRingEnd ℂ) a))
    (hsym : ∀ z, f (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    analyticOrderAt f a ≤ analyticOrderAt f (-(starRingEnd ℂ) a) := by
  by_cases htop : analyticOrderAt f a = ⊤
  · rw [analyticOrderAt_symm_neg_conj_top hsym htop, htop]
  · exact analyticOrderAt_symm_neg_conj_finite hf hsym htop

lemma analyticOrderAt_symm_neg_conj
    {f : ℂ → ℂ} {a : ℂ}
    (hf : AnalyticAt ℂ f a) (hf' : AnalyticAt ℂ f (-(starRingEnd ℂ) a))
    (hsym : ∀ z, f (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (f z)) :
    analyticOrderAt f (-(starRingEnd ℂ) a) = analyticOrderAt f a := by
  let b := -(starRingEnd ℂ) a
  let m := analyticOrderAt f a
  have h1 : analyticOrderAt f a ≤ analyticOrderAt f b :=
    analyticOrderAt_le_symm_neg_conj hf hf' hsym
  have hba : -(starRingEnd ℂ) b = a := neg_conj_involutive a
  have hf'' : AnalyticAt ℂ f (-(starRingEnd ℂ) b) := by
    rw [hba]; exact hf
  have h2 : analyticOrderAt f b ≤ analyticOrderAt f (-(starRingEnd ℂ) b) :=
    analyticOrderAt_le_symm_neg_conj hf' hf'' hsym
  rw [hba] at h2
  exact le_antisymm h2 h1

theorem AnnulationPartieReelle_multiplicite
    (Z U : Set ℂ) (zm : ℂ) (hzm : zm ∈ Z) (hU : zm ∈ U)
    (hUsymm : ∀ z ∈ U, -(starRingEnd ℂ) z ∈ U)
    (huniq : ∀ z ∈ Z, z ∈ U → z = zm)
    (hconj : ∀ z ∈ Z, (starRingEnd ℂ) z ∈ Z) (hneg : ∀ z ∈ Z, -z ∈ Z) :
    zm.re = 0 :=
  AnnulationPartieReelleZeta Z U zm hzm hU hUsymm huniq hconj hneg





end RealPartCarac
