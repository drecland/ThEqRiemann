import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.ResiduCircleIntegration1
import ThEqRiemann.RiemannProof.XiEntiereProp
import ThEqRiemann.ComplementRiemann.RealPartCaracterisation

/-! -/
namespace XiDecalePropRiemann

open RiemannDef Set Complex DefinitionsThEq

lemma xiDecale_differentiable : Differentiable ℂ xiDecale := by
  unfold xiDecale
  exact xiEntiere_differentiable.comp
    (differentiable_const _ |>.add differentiable_id)

---------------------------------------------------------------------

lemma meromorphicOrderAt_eq_map_analyticOrderAt {f : ℂ → ℂ} {x : ℂ}
    (hf : AnalyticAt ℂ f x) :
    meromorphicOrderAt f x = ENat.map Nat.cast (analyticOrderAt f x) := by
  exact hf.meromorphicOrderAt_eq

lemma enat_map_cast_eq_natCast {n : ℕ∞} {m : ℕ}
    (h : ENat.map Nat.cast n = ((m : ℤ) : WithTop ℤ)) :
    n = (m : ℕ∞) := by
  induction n using ENat.recTopCoe with
  | top =>
    simp at h
  | coe k =>
    rw [ENat.map_natCast] at h
    have h' : ((k : ℤ) : WithTop ℤ) = ((m : ℤ) : WithTop ℤ) := h
    have hkm : (k : ℤ) = (m : ℤ) := WithTop.coe_injective h'
    have : k = m := by exact_mod_cast hkm
    rw [this]

---------------------------------------------------------------------

lemma xiDecale_forme_normale (zj : ℂ) (m : ℕ) (_ : 0 < m)
    (hord : meromorphicOrderAt xiDecale zj = (m : ℤ)) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ zj ∧ ψ zj ≠ 0 ∧
      xiDecale =ᶠ[nhds zj] fun z => (z - zj) ^ m * ψ z := by
  have hAn : AnalyticAt ℂ xiDecale zj :=
    xiDecale_differentiable.analyticAt zj
  have hMer : meromorphicOrderAt xiDecale zj
      = ENat.map Nat.cast (analyticOrderAt xiDecale zj) :=
    meromorphicOrderAt_eq_map_analyticOrderAt hAn
  have hAO : analyticOrderAt xiDecale zj = (m : ℕ∞) :=
    enat_map_cast_eq_natCast (hMer.symm.trans hord)
  obtain ⟨ψ, hψ_an, hψ_ne, hψ_eq⟩ := (hAn.analyticOrderAt_eq_natCast (n := m)).mp hAO
  refine ⟨ψ, hψ_an, hψ_ne, ?_⟩
  filter_upwards [hψ_eq] with z hz
  simpa [smul_eq_mul] using hz

open ResCircIntegration1

lemma deriv_log_xiDecale (zj : ℂ) (m : ℕ) (ψ : ℂ → ℂ)
    (hψ_an : AnalyticAt ℂ ψ zj) (hψ_nz : ψ zj ≠ 0)
    (hH : xiDecale =ᶠ[nhds zj] fun z => (z - zj) ^ m * ψ z) :
    ∀ᶠ z in nhds zj, z ≠ zj →
      deriv xiDecale z / xiDecale z = (m : ℂ) / (z - zj) + deriv ψ z / ψ z :=
  derivee_logarithmique_forme_normale xiDecale ψ zj m hψ_an hψ_nz hH


lemma residu_integrandeMoment (zj : ℂ) (m k : ℕ) (r : ℝ) (_ : 0 < r)
    (hres : residu (fun z => z ^ k * deriv xiDecale z / (xiDecale z - 0)) zj r
              = (m : ℂ) * zj ^ k) :
    residu (integrandeMoment k) zj r = (m : ℂ) * (-Complex.I * zj) ^ k := by
  have h : integrandeMoment k
      = fun z => (-Complex.I) ^ k * (z ^ k * deriv xiDecale z / (xiDecale z - 0)) := by
    funext z
    simp only [integrandeMoment, sub_zero, mul_pow]
    ring
  rw [h, residu_const_mul, hres]
  rw [mul_pow]
  ring

lemma nu_eq_somme_residus
    (γ : ℝ → ℂ) (k : ℕ) (S : Finset ℂ)
    (hind : ∀ z ∈ S, indiceLacet γ z = 1)
    (hthm : (∫ t in (0 : ℝ)..1, deriv γ t * integrandeMoment k (γ t))
              = 2 * Complex.I * (Real.pi : ℂ) *
                ∑ a ∈ S, (indiceLacet γ a) * (residu (integrandeMoment k) a 1)) :
    nuMoment γ k = ∑ a ∈ S, residu (integrandeMoment k) a 1 := by
  have hsum : ∑ a ∈ S, (indiceLacet γ a) * (residu (integrandeMoment k) a 1)
      = ∑ a ∈ S, residu (integrandeMoment k) a 1 := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hind a ha, one_mul]
  unfold nuMoment
  rw [hthm, hsum]
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp

theorem evaluation_moments_zeta
    {d : ℕ} (γ : ℝ → ℂ) (z : Fin d → ℂ) (m : Fin d → ℕ)
    (hz_inj : Function.Injective z)
    (_ : ∀ j, 0 < m j)
    (hind : ∀ j, indiceLacet γ (z j) = 1)
    (hres : ∀ k j, residu (integrandeMoment k) (z j) 1 =
      (m j : ℂ) * (-Complex.I * z j) ^ k)
    (hthm : ∀ k, (∫ t in (0 : ℝ)..1, deriv γ t * integrandeMoment k (γ t))
              = 2 * Complex.I * (Real.pi : ℂ) *
                ∑ a ∈ (Finset.univ.image z), (indiceLacet γ a) *
                (residu (integrandeMoment k) a 1))
    (k : ℕ) :
    nuMoment γ k = ∑ j : Fin d, (m j : ℂ) * (-Complex.I * z j) ^ k := by
  have hind' : ∀ a ∈ Finset.univ.image z, indiceLacet γ a = 1 := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    exact hind j
  rw [nu_eq_somme_residus γ k (Finset.univ.image z) hind' (hthm k)]
  rw [Finset.sum_image (fun i _ j _ hij => hz_inj hij)]
  apply Finset.sum_congr rfl
  intro j _
  exact hres k j

-----------------------------------------------------------------------

lemma xiDecale_zero_simple_deriv_ne_zero (zm : ℂ)
    (hord : meromorphicOrderAt xiDecale zm = ((1 : ℕ) : ℤ)) :
    xiDecale zm = 0 ∧ deriv xiDecale zm ≠ 0 := by
  obtain ⟨ψ, hψ_an, hψ_ne, hψ_eq⟩ :=
    xiDecale_forme_normale zm 1 one_pos hord
  have hval : xiDecale zm = 0 := by
    have := hψ_eq.self_of_nhds
    simpa using this
  refine ⟨hval, ?_⟩
  have hderiv : HasDerivAt (fun z => (z - zm) ^ 1 * ψ z) (ψ zm) zm := by
    have h1 : HasDerivAt (fun z => z - zm) 1 zm := (hasDerivAt_id zm).sub_const zm
    have h2 : HasDerivAt ψ (deriv ψ zm) zm := hψ_an.differentiableAt.hasDerivAt
    have h3 : HasDerivAt (fun z => (z - zm) * ψ z)
        (1 * ψ zm + (zm - zm) * deriv ψ zm) zm := h1.mul h2
    have h4 : (1 * ψ zm + (zm - zm) * deriv ψ zm) = ψ zm := by
      simp
    rw [h4] at h3
    simpa using h3
  have hxi : HasDerivAt xiDecale (ψ zm) zm :=
    hderiv.congr_of_eventuallyEq hψ_eq
  rw [hxi.deriv]
  exact hψ_ne

lemma xiDecale_inverse_continuousAt_voisinage (zm : ℂ)
    (h0 : xiDecale zm = 0) (hd : deriv xiDecale zm ≠ 0)
    (hinv : HasStrictDerivAt xiDecale (deriv xiDecale zm) zm) :
    ∀ᶠ w in nhds (0 : ℂ), ContinuousAt
      (HasStrictDerivAt.localInverse xiDecale (deriv xiDecale zm) zm hinv hd) w := by
  set φ := (hinv.hasStrictFDerivAt_equiv hd).toOpenPartialHomeomorph xiDecale with hφ
  have h_mem : (0 : ℂ) ∈ φ.target := by
    have := (hinv.hasStrictFDerivAt_equiv hd).image_mem_toOpenPartialHomeomorph_target
    rwa [h0] at this
  have h_nhds : φ.target ∈ nhds (0 : ℂ) := φ.open_target.mem_nhds h_mem
  filter_upwards [h_nhds] with w hw
  exact φ.continuousAt_symm hw

lemma differentiableAt_of_reciproque_locale {f g : ℂ → ℂ} {w : ℂ}
    (hcont : ContinuousAt g w) (hf : DifferentiableAt ℂ f (g w))
    (hne : deriv f (g w) ≠ 0) (hright : ∀ᶠ y in nhds w, f (g y) = y) :
    DifferentiableAt ℂ g w :=
  (HasDerivAt.of_local_left_inverse
    hcont hf.hasDerivAt hne hright).differentiableAt

lemma eventually_nhds_propage {P : ℂ → Prop} {a : ℂ}
    (h : ∀ᶠ w in nhds a, P w) :
    ∀ᶠ w in nhds a, ∀ᶠ y in nhds w, P y :=
  h.eventually_nhds

lemma xiDecale_inverse_differentiableAt_voisinage (zm : ℂ)
    (h0 : xiDecale zm = 0) (hd : deriv xiDecale zm ≠ 0)
    (hinv : HasStrictDerivAt xiDecale (deriv xiDecale zm) zm) :
    ∀ᶠ w in nhds (0 : ℂ),
      DifferentiableAt ℂ
        (HasStrictDerivAt.localInverse xiDecale
          (deriv xiDecale zm) zm hinv hd) w := by
  set Xinv := HasStrictDerivAt.localInverse xiDecale
    (deriv xiDecale zm) zm hinv hd
    with hXinv
  have hAn : AnalyticAt ℂ xiDecale zm := xiDecale_differentiable.analyticAt zm
  have hcont : ContinuousAt (deriv xiDecale) zm := hAn.deriv.continuousAt
  have hne : ∀ᶠ z in nhds zm, deriv xiDecale z ≠ 0 := hcont.eventually_ne hd
  have hder0 : HasStrictDerivAt Xinv (deriv xiDecale zm)⁻¹ 0 := by
    have h := hinv.to_localInverse hd
    rwa [h0] at h
  have hXinv0 : Xinv 0 = zm := by
    have h := (hinv.eventually_left_inverse hd).self_of_nhds
    rwa [h0] at h
  have hcontXinv : ContinuousAt Xinv 0 := hder0.hasDerivAt.continuousAt
  have hne' : ∀ᶠ w in nhds (0 : ℂ), deriv xiDecale (Xinv w) ≠ 0 := by
    have : Filter.Tendsto Xinv (nhds 0) (nhds zm) := by
      simpa [hXinv0] using hcontXinv.tendsto
    exact this.eventually hne
  have hright : ∀ᶠ w in nhds (0 : ℂ), xiDecale (Xinv w) = w := by
    have h := hinv.eventually_right_inverse hd
    rwa [h0] at h
  have hcw := xiDecale_inverse_continuousAt_voisinage zm h0 hd hinv
  have hright' := eventually_nhds_propage hright
  filter_upwards [hne', hright', hcw] with w hw_ne hw_right' hw_cont
  exact differentiableAt_of_reciproque_locale hw_cont
    (xiDecale_differentiable (Xinv w)) hw_ne hw_right'

lemma xiDecale_inverse_analyticAt (zm : ℂ)
    (h0 : xiDecale zm = 0) (hd : deriv xiDecale zm ≠ 0)
    (hinv : HasStrictDerivAt xiDecale (deriv xiDecale zm) zm) :
    AnalyticAt ℂ
      (HasStrictDerivAt.localInverse xiDecale (deriv xiDecale zm) zm hinv hd) 0 := by
  have hdiff := xiDecale_inverse_differentiableAt_voisinage zm h0 hd hinv
  exact Complex.analyticAt_iff_eventually_differentiableAt.mpr hdiff

lemma xiDecale_inverse_locale (zm : ℂ)
    (h0 : xiDecale zm = 0) (hd : deriv xiDecale zm ≠ 0) :
    ∃ Xinv : ℂ → ℂ, AnalyticAt ℂ Xinv 0 ∧ Xinv 0 = zm ∧
      (∀ᶠ w in nhds (0 : ℂ), xiDecale (Xinv w) = w) ∧
      (∀ᶠ z in nhds zm, Xinv (xiDecale z) = z) := by
  have hAn : AnalyticAt ℂ xiDecale zm := xiDecale_differentiable.analyticAt zm
  have hstrict : HasStrictDerivAt xiDecale (deriv xiDecale zm) zm :=
    hAn.hasStrictDerivAt
  have hinv : HasStrictDerivAt xiDecale (deriv xiDecale zm) zm := hstrict
  refine ⟨hinv.localInverse xiDecale (deriv xiDecale zm) zm hd, ?_, ?_, ?_, ?_⟩
  · exact xiDecale_inverse_analyticAt zm h0 hd hinv
  · have h := (hinv.eventually_left_inverse hd).self_of_nhds
    rwa [h0] at h
  · have h := hinv.eventually_right_inverse hd
    rwa [h0] at h
  · exact hinv.eventually_left_inverse hd

lemma racine_eq_I_mul_nuMoment (γ : ℝ → ℂ) (zm : ℂ)
    (h : nuMoment γ 1 = -Complex.I * zm) :
    zm = Complex.I * nuMoment γ 1 := by
  rw [h]
  have : Complex.I * (-Complex.I * zm) = zm := by
    ring_nf
    simp [Complex.I_sq]
  exact this.symm

lemma nuMoment_un_zero_simple
    (γ : ℝ → ℂ) (zm : ℂ)
    (hind : indiceLacet γ zm = 1)
    (hres : ∀ k, residu (integrandeMoment k) zm 1 = (1 : ℂ) * (-Complex.I * zm) ^ k)
    (hthm : ∀ k, (∫ t in (0 : ℝ)..1, deriv γ t * integrandeMoment k (γ t))
              = 2 * Complex.I * (Real.pi : ℂ) *
                ∑ a ∈ (Finset.univ.image (fun _ : Fin 1 => zm)),
                  (indiceLacet γ a) * (residu (integrandeMoment k) a 1)) :
    nuMoment γ 1 = -Complex.I * zm := by
  have h := evaluation_moments_zeta (d := 1) γ (fun _ => zm) (fun _ => 1)
    (fun i j _ => Subsingleton.elim i j)
    (fun _ => one_pos)
    (fun _ => hind)
    (fun k _ => by simpa using hres k)
    hthm 1
  simpa [Fin.sum_univ_one, Nat.cast_one, one_mul, pow_one] using h

theorem application_inversion_xi
    (γ : ℝ → ℂ) (zm : ℂ)
    (hord : meromorphicOrderAt xiDecale zm = ((1 : ℕ) : ℤ))
    (hind : indiceLacet γ zm = 1)
    (hres : ∀ k, residu (integrandeMoment k) zm 1 = (1 : ℂ) * (-Complex.I * zm) ^ k)
    (hthm : ∀ k, (∫ t in (0 : ℝ)..1, deriv γ t * integrandeMoment k (γ t))
              = 2 * Complex.I * (Real.pi : ℂ) *
                ∑ a ∈ (Finset.univ.image (fun _ : Fin 1 => zm)),
                  (indiceLacet γ a) * (residu (integrandeMoment k) a 1)) :
    (∃ Xinv : ℂ → ℂ, AnalyticAt ℂ Xinv 0 ∧ Xinv 0 = zm ∧
        (∀ᶠ w in nhds (0 : ℂ), xiDecale (Xinv w) = w)) ∧
    zm = Complex.I * nuMoment γ 1 := by
  obtain ⟨h0, hd⟩ := xiDecale_zero_simple_deriv_ne_zero zm hord
  obtain ⟨Xinv, hAn, hX0, hright, _⟩ := xiDecale_inverse_locale zm h0 hd
  exact ⟨⟨Xinv, hAn, hX0, hright⟩,
    racine_eq_I_mul_nuMoment γ zm (nuMoment_un_zero_simple γ zm hind hres hthm)⟩



------------------------------------------------------------------------



lemma zerosXiDecale_neg : ∀ z ∈ zerosXiDecale, -z ∈ zerosXiDecale := by
  intro z hz
  simp only [zerosXiDecale, xiDecale, Set.mem_ofPred_eq] at hz ⊢
  have h : (1 / 2 : ℂ) + -z = 1 - (1 / 2 + z) := by ring
  rw [h, xiEntiere_one_sub]
  exact hz

lemma riemannZeta_conj_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    riemannZeta ((starRingEnd ℂ) s) = (starRingEnd ℂ) (riemannZeta s) := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  rw [zeta_eq_tsum_one_div_nat_cpow hs', zeta_eq_tsum_one_div_nat_cpow hs]
  rw [Complex.conj_tsum]
  congr 1
  ext n
  rw [map_div₀, map_one]
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : s ≠ 0 := fun h => by simp [h] at hs; linarith
    have hcs0 : (starRingEnd ℂ) s ≠ 0 := by simpa using hs0
    simp [Complex.zero_cpow hs0, Complex.zero_cpow hcs0]
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlog : (starRingEnd ℂ) (Complex.log (n : ℂ)) = Complex.log (n : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n),
          Complex.conj_ofReal]
    rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0]
    rw [← Complex.exp_conj, map_mul, hlog]

lemma Gammaℝ_conj (s : ℂ) :
    Complex.Gammaℝ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Complex.Gammaℝ s) := by
  unfold Complex.Gammaℝ
  rw [map_mul]
  congr 1
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Complex.cpow_def_of_ne_zero hpi, Complex.cpow_def_of_ne_zero hpi,
        ← Complex.exp_conj, map_mul]
    have hlog : (starRingEnd ℂ) (Complex.log (Real.pi : ℂ)) = Complex.log (Real.pi : ℂ) := by
      have h := Complex.ofReal_log Real.pi_pos.le
      rw [← h, Complex.conj_ofReal]
    rw [hlog]
    congr 2
    simp [map_div₀, map_neg, map_ofNat]
  · have : (starRingEnd ℂ) s / 2 = (starRingEnd ℂ) (s / 2) := by
      simp [map_div₀, map_ofNat]
    rw [this]
    exact Complex.Gamma_conj _

lemma completedRiemannZeta₀_conj_of_one_lt_re (s : ℂ) (hs : 1 < s.re) :
    completedRiemannZeta₀ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (completedRiemannZeta₀ s) := by
  have hs' : 1 < ((starRingEnd ℂ) s).re := by simpa using hs
  have hre : 0 < s.re := by linarith
  have hcre : 0 < ((starRingEnd ℂ) s).re := by linarith
  have hdef : ∀ w : ℂ, completedRiemannZeta₀ w
      = completedRiemannZeta w + 1 / w + 1 / (1 - w) := by
    intro w
    rw [completedRiemannZeta_eq]; ring
  have hLam : ∀ w : ℂ, 0 < w.re → completedRiemannZeta w = Complex.Gammaℝ w * riemannZeta w := by
    intro w hw
    have hw0 : w ≠ 0 := fun h => by simp [h] at hw
    have hG : Complex.Gammaℝ w ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hw
    rw [riemannZeta_def_of_ne_zero hw0]
    field_simp
  rw [hdef ((starRingEnd ℂ) s), hdef s, hLam _ hcre, hLam _ hre,
      Gammaℝ_conj, riemannZeta_conj_of_one_lt_re s hs]
  simp [map_add, map_mul, map_sub]

lemma completedRiemannZeta₀_conj' (s : ℂ) :
    completedRiemannZeta₀ ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (completedRiemannZeta₀ s) := by
  set F : ℂ → ℂ := fun w => (starRingEnd ℂ) (completedRiemannZeta₀ ((starRingEnd ℂ) w)) with hF
  have hFdiff : Differentiable ℂ F := by
    intro w
    have h := (differentiable_completedZeta₀ ((starRingEnd ℂ) w)).conj_conj
    rw [Complex.conj_conj] at h
    exact h
  have hΛdiff : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  have hev : F =ᶠ[nhds (2 : ℂ)] completedRiemannZeta₀ := by
    have hopen : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (2 : ℂ) ∈ {w : ℂ | 1 < w.re})] with w hw
    have h := completedRiemannZeta₀_conj_of_one_lt_re w hw
    simp only [hF]
    rw [h, Complex.conj_conj]
  have hFan : AnalyticOnNhd ℂ F Set.univ :=
    hFdiff.differentiableOn.analyticOnNhd isOpen_univ
  have hΛan : AnalyticOnNhd ℂ completedRiemannZeta₀ Set.univ :=
    hΛdiff.differentiableOn.analyticOnNhd isOpen_univ
  have heq : ∀ w, F w = completedRiemannZeta₀ w := fun w =>
    hFan.eqOn_of_preconnected_of_eventuallyEq hΛan isPreconnected_univ (Set.mem_univ _) hev
      (Set.mem_univ w)
  have h1 := heq ((starRingEnd ℂ) s)
  simp only [hF, Complex.conj_conj] at h1
  exact h1.symm

open XiEntiereRiemann in
lemma zerosXiDecale_conj :
    ∀ z ∈ zerosXiDecale, (starRingEnd ℂ) z ∈ zerosXiDecale := by
  intro z hz
  simp only [zerosXiDecale, xiDecale, Set.mem_ofPred_eq] at hz ⊢
  have h : (1 / 2 : ℂ) + (starRingEnd ℂ) z = (starRingEnd ℂ) (1 / 2 + z) := by
    simp [map_add, map_ofNat]
  rw [h, xiEntiere_conj, hz, map_zero]

open RealPartCarac in
theorem riemann_xi_of_unique
    (s : ℂ) (hs : xiEntiere s = 0) (U : Set ℂ)
    (hU : s - 1 / 2 ∈ U)
    (hUsymm : ∀ z ∈ U, -(starRingEnd ℂ) z ∈ U)
    (huniq : ∀ z ∈ zerosXiDecale, z ∈ U → z = s - 1 / 2) :
    s.re = 1 / 2 := by
  have hzm : s - 1 / 2 ∈ zerosXiDecale := by
    simp only [zerosXiDecale, xiDecale, Set.mem_ofPred_eq]
    have : (1 / 2 : ℂ) + (s - 1 / 2) = s := by ring
    rw [this]; exact hs
  have h0 := AnnulationPartieReelleZeta zerosXiDecale U (s - 1 / 2)
    hzm hU hUsymm huniq zerosXiDecale_conj zerosXiDecale_neg
  have : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  linarith

open XiEntiereRiemann in
lemma xiDecale_not_eventually_zero (zm : ℂ) :
    ¬ (∀ᶠ z in nhds zm, xiDecale z = 0) := by
  intro h
  have hana : AnalyticOnNhd ℂ xiDecale Set.univ :=
    fun z _ => xiDecale_differentiable.analyticAt z
  have hfreq : ∃ᶠ z in nhdsWithin zm {zm}ᶜ, xiDecale z = 0 :=
    (h.filter_mono nhdsWithin_le_nhds).frequently
  have hzero : Set.EqOn xiDecale 0 Set.univ :=
    hana.eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ zm) hfreq
  have h0 : xiDecale (1 / 2) = 0 := hzero (Set.mem_univ _)
  have : xiDecale (1 / 2) = 1 / 2 := by
    unfold xiDecale
    rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, xiEntiere_one]
  rw [this] at h0
  norm_num at h0






end XiDecalePropRiemann
