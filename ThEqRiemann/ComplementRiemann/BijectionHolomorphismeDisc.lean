import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.ComplementRiemann.ChangementVariable
import ThEqRiemann.RiemannProof.XiDecaleProp
/-! -/
namespace BijHoloDisc

open Set Complex
open RiemannDef

theorem mobius_den_ne_zero (c₁ : ℂ) {R₁ : ℝ} (hR₁ : 0 < R₁)
    {a : ℂ} (ha : ‖a‖ < 1) {z : ℂ} (hz : z ∈ Metric.ball c₁ R₁) :
    ((R₁ : ℂ) - (starRingEnd ℂ) a * (z - c₁)) ≠ 0 := by
  intro h0
  have h1 : (R₁ : ℂ) = (starRingEnd ℂ) a * (z - c₁) := sub_eq_zero.mp h0
  have hz' : ‖z - c₁‖ < R₁ := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    exact hz
  have h2 : ‖(R₁ : ℂ)‖ = R₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR₁]
  have h3 : ‖(starRingEnd ℂ) a * (z - c₁)‖ = ‖a‖ * ‖z - c₁‖ := by
    rw [norm_mul, Complex.norm_conj]
  have h4 : (R₁ : ℝ) = ‖a‖ * ‖z - c₁‖ := by
    rw [← h2, h1, h3]
  have h5 : ‖a‖ * ‖z - c₁‖ < R₁ := by
    have hn : 0 ≤ ‖z - c₁‖ := norm_nonneg _
    nlinarith
  linarith

theorem hasDerivAt_mobiusDisque (c₁ c₂ : ℂ) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁)
    {a : ℂ} (ha : ‖a‖ < 1) (θ : ℝ) {z : ℂ} (hz : z ∈ Metric.ball c₁ R₁) :
    HasDerivAt (mobiusDisque c₁ c₂ R₁ R₂ a θ)
      (((R₂ : ℂ) / R₁) * Complex.exp (θ * Complex.I) * (1 - (‖a‖ : ℂ)^2) /
        (1 - (starRingEnd ℂ) a * ((z - c₁) / R₁))^2) z := by
  have hden := mobius_den_ne_zero c₁ hR₁ ha hz
  have hR : (R₁ : ℂ) ≠ 0 := by exact_mod_cast hR₁.ne'
  have hN : HasDerivAt (fun w : ℂ => w - c₁ - a * R₁) 1 z :=
    ((hasDerivAt_id z).sub_const c₁).sub_const (a * R₁)
  have hD : HasDerivAt (fun w : ℂ => (R₁ : ℂ) - (starRingEnd ℂ) a * (w - c₁))
      (-((starRingEnd ℂ) a)) z := by
    have h := (((hasDerivAt_id z).sub_const c₁).const_mul ((starRingEnd ℂ) a)).const_sub (R₁ : ℂ)
    simpa using h
  have hQ := hN.div hD hden
  have hF := (hQ.const_mul ((R₂ : ℂ) * Complex.exp (θ * Complex.I))).const_add c₂
  unfold mobiusDisque
  convert hF using 1
  have hna : ((‖a‖ : ℂ))^2 = a * (starRingEnd ℂ) a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hna]
  field_simp
  ring

lemma mobiusUnite_den_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    1 - (starRingEnd ℂ) a * w ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * w = 1 := by linear_combination -h
  have h2 : ‖(starRingEnd ℂ) a * w‖ = ‖a‖ * ‖w‖ := by
    rw [norm_mul, Complex.norm_conj]
  have h3 : ‖a‖ * ‖w‖ < 1 := by
    have := norm_nonneg a
    have := norm_nonneg w
    nlinarith
  rw [h1, norm_one] at h2
  linarith

lemma mobius_norm_identite (a w : ℂ) :
    ‖1 - (starRingEnd ℂ) a * w‖^2 - ‖w - a‖^2 = (1 - ‖a‖^2) * (1 - ‖w‖^2) := by
  have e1 : ∀ z : ℂ, ‖z‖^2 = Complex.normSq z := fun z => by
    rw [Complex.sq_norm]
  rw [e1, e1, e1, e1]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

lemma mobiusUnite_norm_lt {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    ‖mobiusUnite a w‖ < 1 := by
  have hden := mobiusUnite_den_ne_zero ha hw
  have hpos : 0 < ‖1 - (starRingEnd ℂ) a * w‖ := norm_pos_iff.mpr hden
  have hid := mobius_norm_identite a w
  have hgt : ‖w - a‖^2 < ‖1 - (starRingEnd ℂ) a * w‖^2 := by
    have h1 : 0 < 1 - ‖a‖^2 := by nlinarith [norm_nonneg a]
    have h2 : 0 < 1 - ‖w‖^2 := by nlinarith [norm_nonneg w]
    nlinarith [mul_pos h1 h2]
  unfold mobiusUnite
  rw [norm_div, div_lt_one hpos]
  exact lt_of_pow_lt_pow_left₀ 2 hpos.le hgt

theorem mobiusUnite_inv {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) :
    mobiusUnite a (mobiusUnite (-a) w) = w := by
  have hD : (1 + (starRingEnd ℂ) a * w) ≠ 0 := by
    have := mobiusUnite_den_ne_zero (a := -a) (by simpa using ha) hw
    simpa [sub_eq_add_neg] using this
  have hna : a * (starRingEnd ℂ) a = ((‖a‖ : ℝ) : ℂ)^2 := by
    exact Complex.mul_conj' a
  have hK : (1 - a * (starRingEnd ℂ) a) ≠ 0 := by
    rw [hna]
    have : (‖a‖ : ℝ)^2 < 1 := by nlinarith [norm_nonneg a]
    intro h0
    have h1 : ((‖a‖ : ℝ) : ℂ)^2 = 1 := by linear_combination -h0
    have h2 : (‖a‖ : ℝ)^2 = 1 := by exact_mod_cast h1
    linarith
  have hin : mobiusUnite (-a) w = (w + a) / (1 + (starRingEnd ℂ) a * w) := by
    unfold mobiusUnite
    simp [sub_eq_add_neg]
  have hden : 1 - (starRingEnd ℂ) a * ((w + a) / (1 + (starRingEnd ℂ) a * w))
      = (1 - a * (starRingEnd ℂ) a) / (1 + (starRingEnd ℂ) a * w) := by
    rw [eq_div_iff hD, sub_mul, mul_assoc, div_mul_cancel₀ _ hD]
    ring
  have hnum : (w + a) / (1 + (starRingEnd ℂ) a * w) - a
      = w * (1 - a * (starRingEnd ℂ) a) / (1 + (starRingEnd ℂ) a * w) := by
    rw [eq_div_iff hD, sub_mul, div_mul_cancel₀ _ hD]
    ring
  change (mobiusUnite (-a) w - a) /
      (1 - (starRingEnd ℂ) a * mobiusUnite (-a) w) = w
  rw [hin, hden, hnum]
  rw [div_div_div_cancel_right₀ hD, mul_div_assoc, div_self hK, mul_one]


lemma two_le_of_factor {g h : ℂ → ℂ} {z₀ : ℂ} {n : ℕ}
    (hhA : AnalyticAt ℂ h z₀) (hh0 : h z₀ ≠ 0)
    (hzero : deriv g z₀ = 0)
    (hfac : ∀ᶠ z in nhds z₀, g z - g z₀ = (z - z₀) ^ n • h z) : 2 ≤ n := by
  by_contra hlt
  push Not at hlt
  have hz_self : g z₀ - g z₀ = (z₀ - z₀) ^ n • h z₀ := hfac.self_of_nhds
  interval_cases n
  · apply hh0
    simpa using hz_self.symm
  · apply hh0
    have h1 : HasDerivAt (fun z => (z - z₀) * h z) (h z₀) z₀ := by
      have hs : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
      have hh : HasDerivAt h (deriv h z₀) z₀ := hhA.differentiableAt.hasDerivAt
      have hm : HasDerivAt (fun z => (z - z₀) * h z) (1 * h z₀ + (z₀ - z₀) * deriv h z₀) z₀ :=
        hs.mul hh
      convert hm using 1
      simp
    have h2 : HasDerivAt (fun z => g z₀ + (z - z₀) * h z) (h z₀) z₀ := h1.const_add _
    have hder : HasDerivAt g (h z₀) z₀ := by
      refine h2.congr_of_eventuallyEq ?_
      filter_upwards [hfac] with z hz
      have : g z - g z₀ = (z - z₀) * h z := by simpa [smul_eq_mul] using hz
      linear_combination this
    rw [← hder.deriv]
    exact hzero

lemma exists_pow_root {g h : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} (hn0 : n ≠ 0)
    (hhA : AnalyticAt ℂ h z₀) (hh0 : h z₀ ≠ 0)
    (hfac : ∀ᶠ z in nhds z₀, g z - g z₀ = (z - z₀) ^ n • h z) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z₀ ∧ ψ z₀ = 0 ∧
      deriv ψ z₀ ≠ 0 ∧ (∀ᶠ z in nhds z₀, g z - g z₀ = ψ z ^ n) := by
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c ^ n = h z₀ :=
    IsAlgClosed.exists_pow_nat_eq (h z₀) (Nat.pos_of_ne_zero hn0)
  have hc0 : c ≠ 0 := by
    intro hc'
    apply hh0
    rw [← hc, hc', zero_pow hn0]
  have hq_cont : ContinuousAt (fun z => h z / h z₀) z₀ :=
    hhA.continuousAt.div_const _
  have hq_one : (fun z => h z / h z₀) z₀ = 1 := div_self hh0
  have hslit : ∀ᶠ z in nhds z₀, h z / h z₀ ∈ Complex.slitPlane := by
    have : Complex.slitPlane ∈ nhds ((fun z => h z / h z₀) z₀) := by
      rw [hq_one]
      exact Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane
    exact hq_cont.eventually_mem this
  set φ : ℂ → ℂ := fun z => c * Complex.exp (Complex.log (h z / h z₀) / n) with hφdef
  have hφA : AnalyticAt ℂ φ z₀ := by
    have hqA : AnalyticAt ℂ (fun z => h z / h z₀) z₀ :=
      hhA.div analyticAt_const hh0
    have hlogA : AnalyticAt ℂ (fun z => Complex.log (h z / h z₀)) z₀ :=
      hqA.clog hslit.self_of_nhds
    exact analyticAt_const.mul
      ((hlogA.div analyticAt_const (by exact_mod_cast hn0)).cexp)
  have hφpow : ∀ᶠ z in nhds z₀, φ z ^ n = h z := by
    have hne : ∀ᶠ z in nhds z₀, h z ≠ 0 := hhA.continuousAt.eventually_ne hh0
    filter_upwards [hslit, hne] with z hz hz0
    simp only [hφdef]
    rw [mul_pow, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast hn0),
      Complex.exp_log (div_ne_zero hz0 hh0), hc]
    field_simp
  have hφ0 : φ z₀ ≠ 0 := by
    have h1 : φ z₀ ^ n = h z₀ := hφpow.self_of_nhds
    intro h0
    apply hh0
    rw [← h1, h0, zero_pow hn0]
  refine ⟨fun z => (z - z₀) * φ z,
    (analyticAt_id.sub analyticAt_const).mul hφA, by simp, ?_, ?_⟩
  · have hd : HasDerivAt (fun z => (z - z₀) * φ z) (φ z₀) z₀ := by
      have hs : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
      have hp : HasDerivAt φ (deriv φ z₀) z₀ := hφA.differentiableAt.hasDerivAt
      have hm : HasDerivAt (fun z => (z - z₀) * φ z)
          (1 * φ z₀ + (z₀ - z₀) * deriv φ z₀) z₀ := hs.mul hp
      exact hm.congr_deriv (by simp)
    rw [hd.deriv]
    exact hφ0
  · filter_upwards [hfac, hφpow] with z hz1 hz2
    rw [mul_pow, hz2, hz1, smul_eq_mul]

lemma false_of_pow_root {g ψ : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} {U : Set ℂ}
    (hU : U ∈ nhds z₀) (hinj : Set.InjOn g U) (hn : 2 ≤ n)
    (hψA : AnalyticAt ℂ ψ z₀) (hψ0 : ψ z₀ = 0) (hψd : deriv ψ z₀ ≠ 0)
    (hψpow : ∀ᶠ z in nhds z₀, g z - g z₀ = ψ z ^ n) : False := by
  have hn0 : n ≠ 0 := by omega
  have hstrict : HasStrictDerivAt ψ (deriv ψ z₀) z₀ := hψA.hasStrictDerivAt
  set χ := hstrict.localInverse ψ (deriv ψ z₀) z₀ hψd with hχ
  have hχinv := hstrict.to_localInverse hψd
  have hright : ∀ᶠ u in nhds (ψ z₀), ψ (χ u) = u :=
    hstrict.eventually_right_inverse hψd
  have hχ0 : χ (ψ z₀) = z₀ := by
    have := hstrict.eventually_left_inverse hψd
    exact this.self_of_nhds
  rw [hψ0] at hright hχ0
  have hχcont : ContinuousAt χ 0 := by
    have h1 : ContinuousAt χ (ψ z₀) := hχinv.hasDerivAt.continuousAt
    rwa [hψ0] at h1
  have hχnear : ∀ᶠ u in nhds (0 : ℂ), χ u ∈ U ∧ g (χ u) - g z₀ = ψ (χ u) ^ n := by
    have hUev : ∀ᶠ z in nhds z₀, z ∈ U := hU
    have h1 : ∀ᶠ z in nhds z₀, z ∈ U ∧ g z - g z₀ = ψ z ^ n := hUev.and hψpow
    have htχ : Filter.Tendsto χ (nhds 0) (nhds z₀) := by
      have := hχcont.tendsto
      rwa [hχ0] at this
    exact htχ.eventually h1
  have hprim : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / n)) n :=
    Complex.isPrimitiveRoot_exp n hn0
  set ζ := Complex.exp (2 * Real.pi * Complex.I / n) with hζ
  have hζn : ζ ^ n = 1 := hprim.pow_eq_one
  have hζ1 : ζ ≠ 1 := hprim.ne_one (by omega)
  have hc : ContinuousAt (fun u : ℂ => ζ * u) 0 :=
    (continuous_const.mul continuous_id).continuousAt
  have htend : Filter.Tendsto (fun u : ℂ => ζ * u) (nhds 0) (nhds 0) := by
    have h := hc.tendsto
    simpa using h
  have hnear2 : ∀ᶠ u in nhds (0 : ℂ),
      χ (ζ * u) ∈ U ∧ g (χ (ζ * u)) - g z₀ = ψ (χ (ζ * u)) ^ n :=
    htend.eventually hχnear
  have hright2 : ∀ᶠ u in nhds (0 : ℂ), ψ (χ (ζ * u)) = ζ * u :=
    htend.eventually hright
  have hall : ∀ᶠ u in nhdsWithin (0 : ℂ) {0}ᶜ,
      (((χ u ∈ U ∧ g (χ u) - g z₀ = ψ (χ u) ^ n) ∧ ψ (χ u) = u) ∧
      ((χ (ζ * u) ∈ U ∧ g (χ (ζ * u)) - g z₀ = ψ (χ (ζ * u)) ^ n) ∧
        ψ (χ (ζ * u)) = ζ * u)) ∧ u ∈ ({0}ᶜ : Set ℂ) :=
    (((hχnear.and hright).and (hnear2.and hright2)).filter_mono
      nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨u, ⟨⟨⟨hb1, hg1⟩, hr1⟩, ⟨⟨hb2, hg2⟩, hr2⟩⟩, hu0⟩ := hall.exists
  have hgeq : g (χ u) = g (χ (ζ * u)) := by
    have e1 : g (χ u) - g z₀ = u ^ n := by rw [hg1, hr1]
    have e2 : g (χ (ζ * u)) - g z₀ = u ^ n := by
      rw [hg2, hr2, mul_pow, hζn, one_mul]
    linear_combination e1 - e2
  have hne : χ u ≠ χ (ζ * u) := by
    intro heq
    have h3 : u = ζ * u := by
      calc u = ψ (χ u) := hr1.symm
        _ = ψ (χ (ζ * u)) := by rw [heq]
        _ = ζ * u := hr2
    have hu : u ≠ 0 := hu0
    apply hζ1
    have : (ζ - 1) * u = 0 := by linear_combination -h3
    rcases mul_eq_zero.mp this with h4 | h4
    · linear_combination h4
    · exact absurd h4 hu
  exact hne (hinj hb1 hb2 hgeq)

theorem deriv_ne_zero_of_injOn {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hinj : Set.InjOn g (Metric.ball 0 1)) {z₀ : ℂ} (hz₀ : z₀ ∈ Metric.ball (0 : ℂ) 1) :
    deriv g z₀ ≠ 0 := by
  intro hzero
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hA : AnalyticAt ℂ g z₀ := hd.analyticAt (hopen.mem_nhds hz₀)
  have hnc : ¬ ∀ᶠ z in nhds z₀, g z = g z₀ := by
    intro hev
    have hball : ∀ᶠ z in nhds z₀, z ∈ Metric.ball (0 : ℂ) 1 := hopen.eventually_mem hz₀
    have hmem : ∀ᶠ z in nhdsWithin z₀ {z₀}ᶜ,
        (z ∈ Metric.ball (0 : ℂ) 1 ∧ g z = g z₀) ∧ z ∈ ({z₀}ᶜ : Set ℂ) :=
      ((hball.and hev).filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨z, ⟨hzball, hgz⟩, hzne⟩ := hmem.exists
    exact hzne (hinj hzball hz₀ hgz)
  obtain ⟨n, h, hhA, hh0, hfac, hn⟩ : ∃ n : ℕ, ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧ h z₀ ≠ 0 ∧
      (∀ᶠ z in nhds z₀, g z - g z₀ = (z - z₀) ^ n • h z) ∧ 2 ≤ n := by
    have hfA : AnalyticAt ℂ (fun z => g z - g z₀) z₀ := hA.sub analyticAt_const
    have hfnc : ¬ ∀ᶠ z in nhds z₀, (fun z => g z - g z₀) z = 0 := by
      intro hf
      exact hnc (hf.mono fun z hz => sub_eq_zero.mp hz)
    obtain ⟨n, h, hhA, hh0, hfac⟩ :=
      (Iff.mpr hfA.exists_eventuallyEq_pow_smul_ne_zero_iff hfnc)
    refine ⟨n, h, hhA, hh0, hfac, ?_⟩
    exact two_le_of_factor hhA hh0 hzero hfac
  obtain ⟨ψ, hψA, hψ0, hψd, hψpow⟩ : ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ z₀ ∧ ψ z₀ = 0 ∧
      deriv ψ z₀ ≠ 0 ∧ (∀ᶠ z in nhds z₀, g z - g z₀ = ψ z ^ n) := by
    exact exists_pow_root (by omega) hhA hh0 hfac
  exact false_of_pow_root (hopen.mem_nhds hz₀) hinj hn hψA hψ0 hψd hψpow

theorem inverse_holomorphe_disque {g : ℂ → ℂ}
    (hd : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hb : Set.BijOn g (Metric.ball 0 1) (Metric.ball 0 1)) :
    DifferentiableOn ℂ (Function.invFunOn g (Metric.ball 0 1)) (Metric.ball 0 1) := by
  intro y hy
  obtain ⟨z₀, hz₀, rfl⟩ := hb.surjOn hy
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball
  have hdiff : DifferentiableAt ℂ g z₀ := hd.differentiableAt (hopen.mem_nhds hz₀)
  have hstrict : HasStrictDerivAt g (deriv g z₀) z₀ :=
    (hd.analyticAt (hopen.mem_nhds hz₀)).hasStrictDerivAt
  have hne : deriv g z₀ ≠ 0 := deriv_ne_zero_of_injOn hd hb.injOn hz₀
  have hinv := hstrict.to_localInverse hne
  have hev : (HasStrictDerivAt.localInverse g (deriv g z₀) z₀ hstrict hne)
      =ᶠ[nhds (g z₀)] Function.invFunOn g (Metric.ball 0 1) := by
    have _: Nonempty ℂ := ⟨0⟩
    have h1 := hstrict.eventually_right_inverse hne
    have hcont : ContinuousAt
        (HasStrictDerivAt.localInverse g (deriv g z₀) z₀ hstrict hne) (g z₀) :=
      hinv.hasDerivAt.continuousAt
    have hloc0 : HasStrictDerivAt.localInverse g (deriv g z₀) z₀ hstrict hne (g z₀) = z₀ := by
      unfold HasStrictDerivAt.localInverse
      exact HasStrictFDerivAt.localInverse_apply_image _
    have h2 : ∀ᶠ y in nhds (g z₀),
        HasStrictDerivAt.localInverse g (deriv g z₀) z₀ hstrict hne y ∈ Metric.ball (0 : ℂ) 1 := by
      have : Metric.ball (0 : ℂ) 1 ∈ nhds
          (HasStrictDerivAt.localInverse g (deriv g z₀) z₀ hstrict hne (g z₀)) := by
        rw [hloc0]; exact hopen.mem_nhds hz₀
      exact hcont.eventually_mem this
    filter_upwards [h1, h2] with y hy1 hy2
    have := hb.injOn.leftInvOn_invFunOn hy2
    rw [hy1] at this
    exact this.symm
  have hdA : DifferentiableAt ℂ
      (HasStrictDerivAt.localInverse g (deriv g z₀) z₀ hstrict hne) (g z₀) :=
    hinv.hasDerivAt.differentiableAt
  exact (hdA.congr_of_eventuallyEq hev.symm).differentiableWithinAt

lemma mobiusUnite_mapsTo {a : ℂ} (ha : ‖a‖ < 1) :
    Set.MapsTo (mobiusUnite a) (Metric.ball 0 1) (Metric.ball 0 1) := by
  intro w hw
  rw [mem_ball_zero_iff] at hw ⊢
  exact mobiusUnite_norm_lt ha hw

lemma mobiusUnite_differentiableOn {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (mobiusUnite a) (Metric.ball 0 1) := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  have hden := mobiusUnite_den_ne_zero ha hw
  apply DifferentiableAt.differentiableWithinAt
  unfold mobiusUnite
  exact (differentiableAt_id.sub_const a).div
    (((differentiableAt_const _).sub
      ((differentiableAt_const _).mul differentiableAt_id))) hden

lemma mobiusUnite_zero (a : ℂ) : mobiusUnite a 0 = -a := by
  simp [mobiusUnite]

lemma mobiusUnite_self (a : ℂ) : mobiusUnite a a = 0 := by
  simp [mobiusUnite]

theorem mobiusUnite_bijOn {a : ℂ} (ha : ‖a‖ < 1) :
    Set.BijOn (mobiusUnite a) (Metric.ball 0 1) (Metric.ball 0 1) := by
  have ha' : ‖-a‖ < 1 := by simpa using ha
  have hleft : ∀ w ∈ Metric.ball (0 : ℂ) 1, mobiusUnite (-a) (mobiusUnite a w) = w := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    simpa using mobiusUnite_inv (a := -a) ha' hw
  refine ⟨mobiusUnite_mapsTo ha, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [← hleft x hx, ← hleft y hy, hxy]
  · intro y hy
    refine ⟨mobiusUnite (-a) y, mobiusUnite_mapsTo ha' hy, ?_⟩
    rw [mem_ball_zero_iff] at hy
    exact mobiusUnite_inv ha hy

theorem automorphisme_disque_unite {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hb : Set.BijOn h (Metric.ball 0 1) (Metric.ball 0 1)) :
    ∃ (θ : ℝ) (a : ℂ), ‖a‖ < 1 ∧
      Set.EqOn h (fun w => Complex.exp (θ * Complex.I) * mobiusUnite a w)
        (Metric.ball 0 1) := by
  obtain ⟨a, ha, h0⟩ := hb.surjOn (Metric.mem_ball_self one_pos)
  have ha' : ‖a‖ < 1 := by simpa using ha
  have ha'' : ‖-a‖ < 1 := by simpa using ha'
  set g : ℂ → ℂ := fun w => h (mobiusUnite (-a) w) with hg
  have hg0 : g 0 = 0 := by
    simp only [hg]
    rw [mobiusUnite_zero, neg_neg]
    exact h0
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    hd.comp (mobiusUnite_differentiableOn ha'') (mobiusUnite_mapsTo ha'')
  have hgb : Set.BijOn g (Metric.ball 0 1) (Metric.ball 0 1) :=
    hb.comp (mobiusUnite_bijOn ha'')
  have hmaps : Set.MapsTo g (Metric.ball 0 1) (Metric.ball (g 0) 1) := by
    rw [hg0]; exact hgb.mapsTo
  have hmaps : Set.MapsTo g (Metric.ball 0 1) (Metric.closedBall 0 1) :=
    fun w hw => Metric.ball_subset_closedBall (hgb.mapsTo hw)
  have hle : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖g w‖ ≤ ‖w‖ := by
    intro w hw
    exact Complex.norm_le_norm_of_mapsTo_ball hgd hmaps hg0 (mem_ball_zero_iff.mp hw)
  have hnorm : ∀ w ∈ Metric.ball (0 : ℂ) 1, ‖g w‖ = ‖w‖ := by
    set k : ℂ → ℂ := Function.invFunOn g (Metric.ball 0 1) with hk
    have hkd : DifferentiableOn ℂ k (Metric.ball 0 1) :=
      inverse_holomorphe_disque hgd hgb
    have hleft : ∀ w ∈ Metric.ball (0 : ℂ) 1, k (g w) = w :=
      fun w hw => hgb.injOn (Function.invFunOn_mem ⟨w, hw, rfl⟩) hw
        (Function.invFunOn_eq ⟨w, hw, rfl⟩)
    have hright : ∀ v ∈ Metric.ball (0 : ℂ) 1, g (k v) = v := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := hgb.surjOn hv
      rw [hleft w hw]
    have hkmaps : Set.MapsTo k (Metric.ball 0 1) (Metric.ball 0 1) := by
      intro v hv
      obtain ⟨w, hw, rfl⟩ := hgb.surjOn hv
      rw [hleft w hw]; exact hw
    have hk0 : k 0 = 0 := by
      have h1 := hleft 0 (Metric.mem_ball_self one_pos)
      rwa [hg0] at h1
    have hkmaps' : Set.MapsTo k (Metric.ball 0 1) (Metric.closedBall 0 1) :=
      fun v hv => Metric.ball_subset_closedBall (hkmaps hv)
    intro w hw
    have hgw : g w ∈ Metric.ball (0 : ℂ) 1 := hgb.mapsTo hw
    have h2 : ‖k (g w)‖ ≤ ‖g w‖ :=
      Complex.norm_le_norm_of_mapsTo_ball hkd hkmaps' hk0 (mem_ball_zero_iff.mp hgw)
    rw [hleft w hw] at h2
    exact le_antisymm (hle w hw) h2
  obtain ⟨θ, hcase⟩ : ∃ θ : ℝ, ∀ w ∈ Metric.ball (0 : ℂ) 1,
      g w = Complex.exp (θ * Complex.I) * w := by
    have hmapsc : Set.MapsTo g (Metric.ball 0 1) (Metric.closedBall (g 0) 1) := by
      rw [hg0]; exact hmaps
    have hz₀ : ((1 : ℂ) / 2) ∈ Metric.ball (0 : ℂ) 1 := by
      rw [mem_ball_zero_iff]; norm_num
    have hdsl : ‖dslope g 0 ((1 : ℂ) / 2)‖ = 1 / 1 := by
      rw [dslope_of_ne _ (by norm_num : ((1 : ℂ) / 2) ≠ 0), slope_def_module, hg0]
      simp only [sub_zero, norm_smul, norm_inv]
      rw [hnorm _ hz₀]
      norm_num
    obtain ⟨C, hC, hEq⟩ :=
      Complex.affine_of_mapsTo_ball_of_exists_norm_dslope_eq_div' hgd hmapsc ⟨_, hz₀, hdsl⟩
    have hCn : ‖C‖ = 1 := by simpa using hC
    obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Complex.exp (θ * Complex.I) = C := by
      refine ⟨Complex.arg C, ?_⟩
      have := Complex.norm_mul_exp_arg_mul_I C
      rwa [hCn, Complex.ofReal_one, one_mul] at this
    refine ⟨θ, fun w hw => ?_⟩
    have := hEq hw
    simp only [hg0, zero_add, sub_zero, smul_eq_mul] at this
    rw [this, hθ, mul_comm]
  refine ⟨θ, a, ha', fun w hw => ?_⟩
  have hw' : mobiusUnite a w ∈ Metric.ball (0 : ℂ) 1 := mobiusUnite_mapsTo ha' hw
  have hgw : g (mobiusUnite a w) = Complex.exp (θ * Complex.I) * mobiusUnite a w :=
    hcase _ hw'
  have hhw : g (mobiusUnite a w) = h w := by
    simp only [hg]
    have := mobiusUnite_inv (a := -a) ha'' (mem_ball_zero_iff.mp hw)
    rw [neg_neg] at this
    rw [this]
  rw [← hhw]
  exact hgw

theorem mobiusDisque_eq_comp (c₁ c₂ : ℂ) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁)
    {a : ℂ} (ha : ‖a‖ < 1) (θ : ℝ) {z : ℂ} (hz : z ∈ Metric.ball c₁ R₁) :
    mobiusDisque c₁ c₂ R₁ R₂ a θ z =
      c₂ + (R₂ : ℂ) * (Complex.exp (θ * Complex.I) *
        mobiusUnite a ((z - c₁) / R₁)) := by
  have hR : (R₁ : ℂ) ≠ 0 := by exact_mod_cast hR₁.ne'
  have hden := mobius_den_ne_zero c₁ hR₁ ha hz
  have hu : 1 - (starRingEnd ℂ) a * ((z - c₁) / R₁) ≠ 0 := by
    intro h0
    apply hden
    have : (R₁ : ℂ) - (starRingEnd ℂ) a * (z - c₁)
        = (R₁ : ℂ) * (1 - (starRingEnd ℂ) a * ((z - c₁) / R₁)) := by
      field_simp
    rw [this, h0, mul_zero]
  unfold mobiusDisque mobiusUnite
  have : (z - c₁ - a * R₁) / ((R₁ : ℂ) - (starRingEnd ℂ) a * (z - c₁))
      = ((z - c₁) / R₁ - a) / (1 - (starRingEnd ℂ) a * ((z - c₁) / R₁)) := by
    field_simp
  rw [this]
  ring

theorem mobiusDisque_bijOn (c₁ c₂ : ℂ) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    {a : ℂ} (ha : ‖a‖ < 1) (θ : ℝ) :
    Set.BijOn (mobiusDisque c₁ c₂ R₁ R₂ a θ)
      (Metric.ball c₁ R₁) (Metric.ball c₂ R₂) := by
  have hR₁' : (R₁ : ℂ) ≠ 0 := by exact_mod_cast hR₁.ne'
  have hR₂' : (R₂ : ℂ) ≠ 0 := by exact_mod_cast hR₂.ne'
  have hT₁ : Set.BijOn (fun z : ℂ => (z - c₁) / R₁) (Metric.ball c₁ R₁) (Metric.ball 0 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR₁.le,
        div_lt_one hR₁]
      simpa [dist_eq_norm] using hz
    · intro z hz z' hz' h
      field_simp at h
      linear_combination h
    · intro w hw
      refine ⟨c₁ + R₁ * w, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hR₁.le]
        have := mem_ball_zero_iff.mp hw
        nlinarith
      · field_simp; ring
  have hRot : Set.BijOn (fun w : ℂ => Complex.exp (θ * Complex.I) * w)
      (Metric.ball 0 1) (Metric.ball 0 1) := by
    have hn : ‖Complex.exp (θ * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
    have hne : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rw [mem_ball_zero_iff, norm_mul, hn, one_mul]
      exact mem_ball_zero_iff.mp hw
    · intro w _ w' _ h
      exact mul_left_cancel₀ hne h
    · intro w hw
      refine ⟨(Complex.exp (θ * Complex.I))⁻¹ * w, ?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_mul, norm_inv, hn, inv_one, one_mul]
        exact mem_ball_zero_iff.mp hw
      · field_simp
  have hT₂ : Set.BijOn (fun w : ℂ => c₂ + (R₂ : ℂ) * w) (Metric.ball 0 1) (Metric.ball c₂ R₂) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hR₂.le]
      have := mem_ball_zero_iff.mp hw
      nlinarith
    · intro w _ w' _ h
      have := add_left_cancel h
      exact mul_left_cancel₀ hR₂' this
    · intro v hv
      refine ⟨(v - c₂) / R₂, ?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR₂.le,
          div_lt_one hR₂]
        simpa [dist_eq_norm] using hv
      · field_simp; ring
  have hcomp := hT₂.comp (hRot.comp ((mobiusUnite_bijOn ha).comp hT₁))
  refine hcomp.congr ?_
  intro z hz
  simp only [Function.comp]
  exact (mobiusDisque_eq_comp c₁ c₂ hR₁ ha θ hz).symm

theorem bijection_holomorphe_disques_mp (c₁ c₂ : ℂ) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (Metric.ball c₁ R₁))
    (hb : Set.BijOn φ (Metric.ball c₁ R₁) (Metric.ball c₂ R₂)) :
    ∃ (θ : ℝ) (a : ℂ), ‖a‖ < 1 ∧
      Set.EqOn φ (mobiusDisque c₁ c₂ R₁ R₂ a θ) (Metric.ball c₁ R₁) := by
  have hR₁' : (R₁ : ℂ) ≠ 0 := by exact_mod_cast hR₁.ne'
  have hR₂' : (R₂ : ℂ) ≠ 0 := by exact_mod_cast hR₂.ne'
  set h : ℂ → ℂ := fun w => (φ (c₁ + R₁ * w) - c₂) / R₂ with hh
  have hS₁ : Set.BijOn (fun w : ℂ => c₁ + (R₁ : ℂ) * w) (Metric.ball 0 1) (Metric.ball c₁ R₁) := by
    refine ⟨?_, ?_, ?_⟩
    · intro w hw
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
        Complex.norm_real, Real.norm_of_nonneg hR₁.le]
      have := mem_ball_zero_iff.mp hw
      nlinarith
    · intro w _ w' _ h
      exact mul_left_cancel₀ hR₁' (add_left_cancel h)
    · intro v hv
      refine ⟨(v - c₁) / R₁, ?_, ?_⟩
      · rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR₁.le,
          div_lt_one hR₁]
        simpa [dist_eq_norm] using hv
      · field_simp; ring
  have hS₂ : Set.BijOn (fun v : ℂ => (v - c₂) / R₂) (Metric.ball c₂ R₂) (Metric.ball 0 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro v hv
      rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR₂.le,
        div_lt_one hR₂]
      simpa [dist_eq_norm] using hv
    · intro v _ v' _ h
      field_simp at h
      linear_combination h
    · intro w hw
      refine ⟨c₂ + R₂ * w, ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hR₂.le]
        have := mem_ball_zero_iff.mp hw
        nlinarith
      · field_simp; ring
  have hhd : DifferentiableOn ℂ h (Metric.ball 0 1) := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => c₁ + (R₁ : ℂ) * w) (Metric.ball 0 1) :=
      (differentiableOn_const _).add ((differentiableOn_const _).mul differentiableOn_id)
    have h2 : DifferentiableOn ℂ (fun w => φ (c₁ + (R₁ : ℂ) * w)) (Metric.ball 0 1) :=
      hd.comp h1 hS₁.mapsTo
    exact (h2.sub (differentiableOn_const _)).div_const _
  have hhb : Set.BijOn h (Metric.ball 0 1) (Metric.ball 0 1) :=
    hS₂.comp (hb.comp hS₁)
  obtain ⟨θ, a, ha, heq⟩ := automorphisme_disque_unite hhd hhb
  refine ⟨θ, a, ha, fun z hz => ?_⟩
  have hz' : (z - c₁) / R₁ ∈ Metric.ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_of_nonneg hR₁.le,
      div_lt_one hR₁]
    simpa [dist_eq_norm] using hz
  have hhz : h ((z - c₁) / R₁) = (φ z - c₂) / R₂ := by
    simp only [hh]
    congr 3
    field_simp; ring
  have h3 : (φ z - c₂) / R₂ =
      Complex.exp (θ * Complex.I) * mobiusUnite a ((z - c₁) / R₁) := by
    have h4 := heq hz'
    rw [hhz] at h4
    exact h4
  rw [mobiusDisque_eq_comp c₁ c₂ hR₁ ha θ hz, ← h3]
  field_simp
  ring



----------------------------------------------------------------

open ChangementVar

theorem exists_rayon_denominateur_ne_zero
    (c₁ : ℂ) {R₁ R' : ℝ} (hR₁ : 0 < R₁) (hR' : R₁ < R') {a : ℂ} (ha : ‖a‖ < 1) :
    ∃ R'' : ℝ, R₁ < R'' ∧ R'' ≤ R' ∧
      ∀ z ∈ Metric.ball c₁ R'', (R₁ : ℂ) - (starRingEnd ℂ) a * (z - c₁) ≠ 0 := by
  set m : ℝ := max ‖a‖ (1/2) with hm
  have hm_pos : 0 < m := lt_max_of_lt_right (by norm_num)
  have hm_lt : m < 1 := max_lt ha (by norm_num)
  have ham : ‖a‖ ≤ m := le_max_left _ _
  refine ⟨min R' (R₁ / m), lt_min hR' ?_, min_le_left _ _, ?_⟩
  · rw [lt_div_iff₀ hm_pos]
    nlinarith
  · intro z hz hzero
    rw [mem_ball_iff_norm] at hz
    have h1 : ‖z - c₁‖ < R₁ / m := lt_of_lt_of_le hz (min_le_right _ _)
    have h2 : m * ‖z - c₁‖ < R₁ := by
      rw [lt_div_iff₀ hm_pos] at h1
      linarith
    have h3 : (starRingEnd ℂ) a * (z - c₁) = (R₁ : ℂ) := sub_eq_zero.1 hzero |>.symm
    have h4 : ‖a‖ * ‖z - c₁‖ = R₁ := by
      have := congrArg norm h3
      simpa [norm_mul, Complex.norm_real, abs_of_pos hR₁] using this
    have h5 : ‖a‖ * ‖z - c₁‖ ≤ m * ‖z - c₁‖ :=
      mul_le_mul_of_nonneg_right ham (norm_nonneg _)
    linarith

theorem bijection_holomorphe_disques_iff
    (c₁ c₂ : ℂ) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (φ : ℂ → ℂ) :
    (DifferentiableOn ℂ φ (Metric.ball c₁ R₁) ∧
      Set.BijOn φ (Metric.ball c₁ R₁) (Metric.ball c₂ R₂)) ↔
    ∃ (θ : ℝ) (a : ℂ), ‖a‖ < 1 ∧
      Set.EqOn φ (mobiusDisque c₁ c₂ R₁ R₂ a θ) (Metric.ball c₁ R₁) := by
  constructor
  · rintro ⟨hd, hb⟩
    exact bijection_holomorphe_disques_mp c₁ c₂ hR₁ hR₂ hd hb
  · rintro ⟨θ, a, ha, heq⟩
    refine ⟨?_, ?_⟩
    · intro z hz
      exact ((hasDerivAt_mobiusDisque c₁ c₂ hR₁ ha θ hz).differentiableAt
        |>.differentiableWithinAt).congr heq (heq hz)
    · exact (mobiusDisque_bijOn c₁ c₂ hR₁ hR₂ ha θ).congr
        (fun z hz => (heq hz).symm)

theorem prolongement_mobius_sphere
    {c₁ c₂ : ℂ} {R₁ R₂ R' : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂) (hR' : R₁ < R')
    {φ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ (Metric.ball c₁ R'))
    (hbij : Set.BijOn φ (Metric.ball c₁ R₁) (Metric.ball c₂ R₂)) :
    ∃ (θ : ℝ) (a : ℂ), ‖a‖ < 1 ∧
      Set.EqOn φ (mobiusDisque c₁ c₂ R₁ R₂ a θ) (Metric.sphere c₁ R₁) ∧
      Set.EqOn (deriv φ) (deriv (mobiusDisque c₁ c₂ R₁ R₂ a θ))
        (Metric.sphere c₁ R₁) := by
  obtain ⟨θ, a, ha, heq⟩ :=
    (bijection_holomorphe_disques_iff c₁ c₂ hR₁ hR₂ φ).1
      ⟨hφ.mono (Metric.ball_subset_ball hR'.le), hbij⟩
  obtain ⟨R'', hR₁R'', hR''R', hden⟩ := exists_rayon_denominateur_ne_zero c₁ hR₁ hR' ha
  have hMd : DifferentiableOn ℂ (mobiusDisque c₁ c₂ R₁ R₂ a θ) (Metric.ball c₁ R'') := by
    intro z hz
    unfold mobiusDisque
    refine DifferentiableAt.differentiableWithinAt ?_
    have := hden z hz
    fun_prop (disch := assumption)
  have hφd : DifferentiableOn ℂ φ (Metric.ball c₁ R'') :=
    hφ.mono (Metric.ball_subset_ball hR''R')
  have hEq : Set.EqOn φ (mobiusDisque c₁ c₂ R₁ R₂ a θ) (Metric.ball c₁ R'') := by
    have hfg : φ =ᶠ[nhds c₁] mobiusDisque c₁ c₂ R₁ R₂ a θ :=
      Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds c₁ hR₁) heq
    exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hφd.analyticOnNhd Metric.isOpen_ball) (hMd.analyticOnNhd Metric.isOpen_ball)
      (convex_ball c₁ R'').isPreconnected
      (Metric.mem_ball_self (hR₁.trans hR₁R'')) hfg
  have hsph : Metric.sphere c₁ R₁ ⊆ Metric.ball c₁ R'' := fun z hz => by
    rw [mem_sphere_iff_norm] at hz
    rw [mem_ball_iff_norm]; linarith [hz.le, hR₁R'']
  refine ⟨θ, a, ha, fun z hz => hEq (hsph hz), fun z hz => ?_⟩
  have hnhds : φ =ᶠ[nhds z] mobiusDisque c₁ c₂ R₁ R₂ a θ :=
    Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (hsph hz)) hEq
  exact hnhds.deriv_eq

theorem projection_radiale_mem_closedBall
    {c z : ℂ} {R : ℝ} (hR : 0 ≤ R) (hzR : R < dist z c) :
    c + (R / dist z c) • (z - c) ∈ Metric.closedBall c R := by
  have hd : 0 < dist z c := lt_of_le_of_lt hR hzR
  rw [mem_closedBall_iff_norm, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg hR hd.le),
      ← dist_eq_norm, div_mul_cancel₀ _ hd.ne']

theorem dist_projection_radiale
    {c z : ℂ} {R : ℝ} (hR : 0 ≤ R) (hzR : R < dist z c) :
    dist z (c + (R / dist z c) • (z - c)) = dist z c - R := by
  have hd : 0 < dist z c := lt_of_le_of_lt hR hzR
  have h1 : z - (c + (R / dist z c) • (z - c)) = (1 - R / dist z c) • (z - c) := by
    rw [sub_smul, one_smul]; abel
  rw [dist_eq_norm, h1, norm_smul, Real.norm_of_nonneg, ← dist_eq_norm]
  · field_simp
  · rw [sub_nonneg, div_le_one hd]; exact hzR.le

theorem exists_ball_sup_subset_ouvert
    {c : ℂ} {R : ℝ} {U : Set ℂ} (hR : 0 ≤ R) (hU : IsOpen U)
    (hcU : Metric.closedBall c R ⊆ U) :
    ∃ R' : ℝ, R < R' ∧ Metric.ball c R' ⊆ U := by
  have hK : IsCompact (Metric.closedBall c R) := isCompact_closedBall c R
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hcU
  refine ⟨R + δ, by linarith, fun z hz => hthick ?_⟩
  rw [Metric.mem_thickening_iff]
  by_cases hzR : dist z c ≤ R
  · exact ⟨z, Metric.mem_closedBall.2 hzR, by simpa using hδ⟩
  · push Not at hzR
    refine ⟨_, projection_radiale_mem_closedBall hR hzR, ?_⟩
    rw [dist_projection_radiale hR hzR]
    have := Metric.mem_ball.1 hz
    linarith

theorem forme_explicite_changement_variable
    {c₁ c₂ : ℂ} {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    {φ f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hcU : Metric.closedBall c₁ R₁ ⊆ U)
    (hφ : DifferentiableOn ℂ φ U)
    (hbij : Set.BijOn φ (Metric.ball c₁ R₁) (Metric.ball c₂ R₂)) :
    ∃ (θ : ℝ) (a : ℂ), ‖a‖ < 1 ∧
      Set.EqOn φ (mobiusDisque c₁ c₂ R₁ R₂ a θ) (Metric.sphere c₁ R₁) ∧
      (∮ z in C(c₁, R₁), φ z * (deriv f (φ z) / f (φ z)) * deriv φ z
        = ∮ z in C(c₁, R₁),
            mobiusDisque c₁ c₂ R₁ R₂ a θ z *
              (deriv f (mobiusDisque c₁ c₂ R₁ R₂ a θ z) /
                f (mobiusDisque c₁ c₂ R₁ R₂ a θ z)) *
              deriv (mobiusDisque c₁ c₂ R₁ R₂ a θ) z) := by
  obtain ⟨R', hR₁R', hballU⟩ := exists_ball_sup_subset_ouvert hR₁.le hU hcU
  obtain ⟨θ, a, ha, hval, hder⟩ :=
    prolongement_mobius_sphere hR₁ hR₂ hR₁R' (hφ.mono hballU) hbij
  refine ⟨θ, a, ha, hval, ?_⟩
  unfold circleIntegral
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  have hz : circleMap c₁ R₁ t ∈ Metric.sphere c₁ R₁ := circleMap_mem_sphere c₁ hR₁.le t
  simp only [hval hz, hder hz]


lemma mobiusDisque_zero_zero (c₁ c₂ : ℂ) {R : ℝ} (hR : R ≠ 0) :
    mobiusDisque c₁ c₂ R R 0 0 = fun z => z + (c₂ - c₁) := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR
  funext z
  unfold mobiusDisque
  simp [Complex.exp_zero]
  field_simp
  ring

-------------------------------------------------------------------------

theorem BijHolPresOrient.toContinuity {c₁ c₂ : ℂ} {ε : ℝ} {φ : ℂ → ℂ}
    (h : BijHolPresOrient c₁ c₂ ε φ) :
    BijHolPresOrientContinuity c₁ c₂ ε φ :=
  ⟨h.holo, h.bij, fun G _ => h.chgt G⟩

open XiDecalePropRiemann in
theorem continuousOn_log_deriv_sphere
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm) :
    ContinuousOn (fun w => w * (deriv xiDecale w / xiDecale w))
      (Metric.sphere (-(starRingEnd ℂ) zm) ε) := by
  have hne : ∀ w ∈ Metric.sphere (-(starRingEnd ℂ) zm) ε, xiDecale w ≠ 0 := by
    intro w hw h0
    have hdist : dist w (-(starRingEnd ℂ) zm) = ε := hw
    have := hiso2 w hdist.le h0
    rw [this, dist_self] at hdist
    exact hε.ne hdist
  have hcont : Continuous xiDecale := xiDecale_differentiable.continuous
  have hdcont : Continuous (deriv xiDecale) := by
    rw [continuous_iff_continuousAt]
    intro z
    exact (xiDecale_differentiable.analyticAt z).deriv.continuousAt
  exact continuousOn_id.mul
    (hdcont.continuousOn.div hcont.continuousOn hne)

theorem mobius_norm_egal {ε : ℝ} (_ : 0 < ε) (a u : ℂ) (hu : ‖u‖ = ε) :
    ‖u - a * ε‖ = ‖(ε : ℂ) - (starRingEnd ℂ) a * u‖ := by
  have hsq : ‖u - a * ε‖ ^ 2 = ‖(ε : ℂ) - (starRingEnd ℂ) a * u‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    have hu2 : Complex.normSq u = ε ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, hu]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
      Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im] at hu2 ⊢
    linear_combination (1 - (a.re ^ 2 + a.im ^ 2)) * hu2
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

theorem mobiusDisque_mapsTo {c₁ c₂ : ℂ} {ε : ℝ} (hε : 0 < ε) (a : ℂ) (ha : ‖a‖ < 1) (θ : ℝ) :
    Set.MapsTo (mobiusDisque c₁ c₂ ε ε a θ) (Metric.sphere c₁ ε) (Metric.sphere c₂ ε) := by
  intro z hz
  have hu : ‖z - c₁‖ = ε := by simpa [dist_eq_norm] using hz
  have hden : (ε : ℂ) - (starRingEnd ℂ) a * (z - c₁) ≠ 0 := by
    intro h
    have h1 : ‖(starRingEnd ℂ) a * (z - c₁)‖ = ε := by
      have : (starRingEnd ℂ) a * (z - c₁) = ε := by linear_combination -h
      rw [this]; simp [abs_of_pos hε]
    rw [norm_mul, Complex.norm_conj, hu] at h1
    nlinarith
  rw [mem_sphere_iff_norm]
  unfold mobiusDisque
  have hnorm := mobius_norm_egal hε a (z - c₁) hu
  have hq : ‖(z - c₁ - a * ε) / ((ε : ℂ) - (starRingEnd ℂ) a * (z - c₁))‖ = 1 := by
    rw [norm_div, hnorm, div_self]
    exact norm_ne_zero_iff.mpr hden
  simp only [add_sub_cancel_left, norm_mul, hq, Complex.norm_exp_ofReal_mul_I,
    Complex.norm_real, Real.norm_of_nonneg hε.le, mul_one]

theorem one_sub_conj_mul_ne_zero (a : ℂ) (ha : ‖a‖ < 1) :
    (1 : ℂ) - (starRingEnd ℂ) a * a ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h1] at h
  have h2 : ((1 : ℝ) : ℂ) = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    simpa using sub_eq_zero.mp h
  have h3 : (1 : ℝ) = ‖a‖ ^ 2 := Complex.ofReal_injective h2
  nlinarith [norm_nonneg a]

theorem mobiusDisque_surjOn {c₁ c₂ : ℂ} {ε : ℝ} (hε : 0 < ε) (a : ℂ) (ha : ‖a‖ < 1)
    (θ : ℝ) :
    Set.SurjOn (mobiusDisque c₁ c₂ ε ε a θ) (Metric.sphere c₁ ε) (Metric.sphere c₂ ε) := by
  intro y hy
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hE : Complex.exp (θ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hK : (ε : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := mul_ne_zero hε' hE
  set K : ℂ := (ε : ℂ) * Complex.exp (θ * Complex.I) with hKdef
  have hKn : ‖K‖ = ε := by
    rw [hKdef, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real,
      Real.norm_of_nonneg hε.le, mul_one]
  set s : ℂ := (y - c₂) / K with hs
  have hy' : ‖y - c₂‖ = ε := by simpa [dist_eq_norm] using hy
  have hsn : ‖s‖ = 1 := by
    rw [hs, norm_div, hy', hKn, div_self hε.ne']
  have hsa : ‖s * (starRingEnd ℂ) a‖ < 1 := by
    rw [norm_mul, hsn, Complex.norm_conj, one_mul]; exact ha
  have hd : (1 : ℂ) + s * (starRingEnd ℂ) a ≠ 0 := by
    intro h
    have : s * (starRingEnd ℂ) a = -1 := by linear_combination h
    rw [this] at hsa
    simp at hsa
  have hss : s * (starRingEnd ℂ) s = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hsn]; simp
  refine ⟨c₁ + ε * ((s + a) / (1 + s * (starRingEnd ℂ) a)), ?_, ?_⟩
  · rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg hε.le, norm_div]
    have : ‖(1 : ℂ) + s * (starRingEnd ℂ) a‖ = ‖s + a‖ := by
      have e : (1 : ℂ) + s * (starRingEnd ℂ) a = s * (starRingEnd ℂ) (s + a) := by
        rw [map_add, mul_add, hss]
      rw [e, norm_mul, hsn, one_mul, Complex.norm_conj]
    rw [this, div_self, mul_one]
    intro h0
    have h00 : s + a = 0 := norm_eq_zero.mp h0
    have hna : ‖a‖ = 1 := by
      have : a = -s := by linear_combination h00
      rw [this, norm_neg, hsn]
    linarith
  · unfold mobiusDisque
    have h1a : (1 : ℂ) - (starRingEnd ℂ) a * a ≠ 0 := one_sub_conj_mul_ne_zero a ha
    have hq : (c₁ + (ε : ℂ) * ((s + a) / (1 + s * (starRingEnd ℂ) a)) - c₁ - a * ε) /
        ((ε : ℂ) - (starRingEnd ℂ) a *
          (c₁ + (ε : ℂ) * ((s + a) / (1 + s * (starRingEnd ℂ) a)) - c₁)) = s := by
      have hden : (ε : ℂ) - (starRingEnd ℂ) a *
          (c₁ + (ε : ℂ) * ((s + a) / (1 + s * (starRingEnd ℂ) a)) - c₁) ≠ 0 := by
        have e : (ε : ℂ) - (starRingEnd ℂ) a *
            (c₁ + (ε : ℂ) * ((s + a) / (1 + s * (starRingEnd ℂ) a)) - c₁)
            = ε * (1 - (starRingEnd ℂ) a * a) / (1 + s * (starRingEnd ℂ) a) := by
          have hD : (1 + s * (starRingEnd ℂ) a) * (1 + s * (starRingEnd ℂ) a)⁻¹ = 1 :=
            mul_inv_cancel₀ hd
          rw [add_sub_cancel_left, div_eq_mul_inv, div_eq_mul_inv]
          linear_combination (-(ε : ℂ)) * hD
        rw [e]
        exact div_ne_zero (mul_ne_zero hε' h1a) hd
      rw [div_eq_iff hden]
      field_simp
      ring
    rw [hq, hs]
    field_simp
    ring

theorem mobius_den_sphere_ne_zero (c₁ : ℂ) {ε : ℝ} (hε : 0 < ε) {a : ℂ} (ha : ‖a‖ < 1)
    {z : ℂ} (hz : z ∈ Metric.sphere c₁ ε) :
    (1 : ℂ) - (starRingEnd ℂ) a * ((z - c₁) / ε) ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * ((z - c₁) / ε) = 1 := by linear_combination -h
  have hn : ‖(starRingEnd ℂ) a * ((z - c₁) / ε)‖ = ‖a‖ := by
    have hz' : ‖z - c₁‖ = ε := by simpa [dist_eq_norm] using hz
    rw [norm_mul, Complex.norm_conj, norm_div, hz', Complex.norm_real,
      Real.norm_of_nonneg hε.le, div_self hε.ne', mul_one]
  rw [h1, norm_one] at hn
  linarith

theorem hasDerivAt_mobiusDisque_sphere (c₁ c₂ : ℂ) {ε : ℝ} (hε : 0 < ε)
    {a : ℂ} (ha : ‖a‖ < 1) (θ : ℝ) {z : ℂ} (hz : z ∈ Metric.sphere c₁ ε) :
    HasDerivAt (mobiusDisque c₁ c₂ ε ε a θ)
      (((ε : ℂ) / ε) * Complex.exp (θ * Complex.I) * (1 - (‖a‖ : ℂ)^2) /
        (1 - (starRingEnd ℂ) a * ((z - c₁) / ε))^2) z := by
  have hden0 := mobius_den_sphere_ne_zero c₁ hε ha hz
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hden : (ε : ℂ) - (starRingEnd ℂ) a * (z - c₁) ≠ 0 := by
    have : (ε : ℂ) - (starRingEnd ℂ) a * (z - c₁) =
      ε * (1 - (starRingEnd ℂ) a * ((z - c₁) / ε)) := by
      field_simp
    rw [this]; exact mul_ne_zero hε' hden0
  have hN : HasDerivAt (fun w : ℂ => w - c₁ - a * ε) 1 z :=
    ((hasDerivAt_id z).sub_const c₁).sub_const (a * ε)
  have hD : HasDerivAt (fun w : ℂ => (ε : ℂ) - (starRingEnd ℂ) a * (w - c₁))
      (-((starRingEnd ℂ) a)) z := by
    have h := (((hasDerivAt_id z).sub_const c₁).const_mul ((starRingEnd ℂ) a)).const_sub (ε : ℂ)
    simpa using h
  have hQ := hN.div hD hden
  have hF := (hQ.const_mul ((ε : ℂ) * Complex.exp (θ * Complex.I))).const_add c₂
  unfold mobiusDisque
  convert hF using 1
  have hna : ((‖a‖ : ℂ))^2 = a * (starRingEnd ℂ) a := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hna]
  field_simp
  ring

theorem mobiusPsiDeriv_pos {a : ℂ} (ha : ‖a‖ < 1) (u : ℝ) : 0 < mobiusPsiDeriv a u := by
  unfold mobiusPsiDeriv
  have hn : 0 < 1 - ‖a‖^2 := by nlinarith [norm_nonneg a]
  have hne : (1 : ℂ) - (starRingEnd ℂ) a * Complex.exp (u * Complex.I) ≠ 0 := by
    intro h
    have h1 : (starRingEnd ℂ) a * Complex.exp (u * Complex.I) = 1 := by linear_combination -h
    have := congrArg norm h1
    rw [norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one, norm_one] at this
    linarith
  exact div_pos hn (pow_pos (norm_pos_iff.mpr hne) 2)

theorem mobiusPsiDeriv_continuous {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous (mobiusPsiDeriv a) := by
  unfold mobiusPsiDeriv
  refine continuous_const.div ?_ ?_
  · fun_prop
  · intro u
    have hne : (1 : ℂ) - (starRingEnd ℂ) a * Complex.exp (u * Complex.I) ≠ 0 := by
      intro h
      have h1 : (starRingEnd ℂ) a * Complex.exp (u * Complex.I) = 1 := by
        linear_combination -h
      have h2 := congrArg norm h1
      rw [norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one, norm_one] at h2
      linarith
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

theorem hasDerivAt_mobiusPsi {a : ℂ} (ha : ‖a‖ < 1) (ψ₀ : ℝ) (t : ℝ) :
    HasDerivAt (mobiusPsi a ψ₀) (mobiusPsiDeriv a t) t := by
  have hc : Continuous (mobiusPsiDeriv a) := mobiusPsiDeriv_continuous ha
  have hint : ∀ x y : ℝ, IntervalIntegrable (mobiusPsiDeriv a) MeasureTheory.volume x y :=
    fun x y => hc.intervalIntegrable x y
  have h : HasDerivAt (fun x : ℝ => ∫ u in (0 : ℝ)..x, mobiusPsiDeriv a u)
      (mobiusPsiDeriv a t) t :=
    intervalIntegral.integral_hasDerivAt_right (hint 0 t)
      (hc.aestronglyMeasurable.stronglyMeasurableAtFilter) hc.continuousAt
  have h' := h.const_add ψ₀
  exact h'

theorem re_one_add_div_one_sub {z : ℂ} (hz : ‖z‖ < 1) :
    ((1 + z) / (1 - z)).re = (1 - ‖z‖^2) / ‖1 - z‖^2 := by
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz; exact lt_irrefl _ hz
  rw [Complex.div_re]
  have hn1 : ‖1 - z‖^2 = Complex.normSq (1 - z) := by
    rw [Complex.sq_norm]
  have hn2 : ‖z‖^2 = Complex.normSq z := by
    rw [Complex.sq_norm]
  rw [hn1, hn2]
  have hpos : Complex.normSq (1 - z) ≠ 0 := by
    rwa [Ne, Complex.normSq_eq_zero]
  field_simp
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.add_im,
    Complex.sub_im, Complex.one_im, Complex.normSq_apply]
  ring

theorem one_sub_mul_exp_mem_slitPlane {q : ℂ} (hqn : ‖q‖ < 1) (u : ℝ) :
    (1 : ℂ) - q * Complex.exp (u * Complex.I) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  have h1 : ‖q * Complex.exp (u * Complex.I)‖ < 1 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; exact hqn
  have h2 := Complex.abs_re_le_norm (q * Complex.exp (u * Complex.I))
  have h3 := abs_le.mp h2
  simp only [Complex.sub_re, Complex.one_re]
  linarith [h3.2]

theorem hasDerivAt_F {q : ℂ} (hqn : ‖q‖ < 1) (u : ℝ) :
    HasDerivAt (fun u : ℝ => u - (2 * Complex.log (1 - q * Complex.exp (u * Complex.I))).im)
      ((1 - ‖q‖^2) / ‖1 - q * Complex.exp (u * Complex.I)‖^2) u := by
  set z : ℂ := q * Complex.exp (u * Complex.I) with hz
  have hzn : ‖z‖ < 1 := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]; exact hqn
  have hslit : (1 : ℂ) - z ∈ Complex.slitPlane := one_sub_mul_exp_mem_slitPlane hqn u
  have hne : (1 : ℂ) - z ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hlin : HasDerivAt (fun u : ℝ => (u : ℂ) * Complex.I) Complex.I u := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := u)).mul_const Complex.I
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp ((u : ℂ) * Complex.I))
      (Complex.exp ((u : ℂ) * Complex.I) * Complex.I) u := hlin.cexp
  have hw : HasDerivAt (fun u : ℝ => (1 : ℂ) - q * Complex.exp ((u : ℂ) * Complex.I))
      (-(q * (Complex.exp ((u : ℂ) * Complex.I) * Complex.I))) u :=
    (hexp.const_mul q).const_sub 1
  have hlog : HasDerivAt (fun u : ℝ => Complex.log (1 - q * Complex.exp ((u : ℂ) * Complex.I)))
      (-(q * (Complex.exp ((u : ℂ) * Complex.I) * Complex.I)) / (1 - z)) u := by
    have := hw.clog_real hslit
    simpa [hz] using this
  have h2 := hlog.const_mul (2 : ℂ)
  have him : HasDerivAt
      (fun u : ℝ => (2 * Complex.log (1 - q * Complex.exp ((u : ℂ) * Complex.I))).im)
      ((2 * (-(q * (Complex.exp ((u : ℂ) * Complex.I) * Complex.I)) / (1 - z))).im) u :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt u h2
  have htot := (hasDerivAt_id u).sub him
  have e1 : -(q * (Complex.exp ((u : ℂ) * Complex.I) * Complex.I)) = -(z * Complex.I) := by
    rw [hz]; ring
  have e2 : (2 * (-(z * Complex.I) / (1 - z))).im = -2 * (z / (1 - z)).re := by
    have : 2 * (-(z * Complex.I) / (1 - z)) = (-2 * (z / (1 - z))) * Complex.I := by
      field_simp
    rw [this, Complex.mul_I_im]
    simp [Complex.mul_re]
  have e3 : 1 - -2 * (z / (1 - z)).re = ((1 + z) / (1 - z)).re := by
    have h : (1 + z) / (1 - z) = 1 + 2 * (z / (1 - z)) := by
      field_simp; ring
    rw [h, Complex.add_re, Complex.one_re]
    simp [Complex.mul_re]
  have hnz : ‖z‖ = ‖q‖ := by
    rw [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hval : (1 - ‖q‖^2) / ‖1 - z‖^2 =
      1 - (2 * (-(q * (Complex.exp ((u : ℂ) * Complex.I) * Complex.I)) / (1 - z))).im := by
    rw [e1, e2, e3, re_one_add_div_one_sub hzn, hnz]
  rw [hval]
  exact htot

open Real

theorem integral_mobiusPsiDeriv {a : ℂ} (ha : ‖a‖ < 1) :
    ∫ u in (0 : ℝ)..2 * π, mobiusPsiDeriv a u = 2 * π := by
  set q := (starRingEnd ℂ) a with hq
  have hqn : ‖q‖ < 1 := by rw [hq, Complex.norm_conj]; exact ha
  let F : ℝ → ℝ := fun u => u - (2 * Complex.log (1 - q * Complex.exp (u * Complex.I))).im
  have hF : ∀ u : ℝ, HasDerivAt F (mobiusPsiDeriv a u) u := by
    intro u
    have h := hasDerivAt_F hqn u
    have hnorm : ‖q‖ = ‖a‖ := by rw [hq, Complex.norm_conj]
    have hval : mobiusPsiDeriv a u = (1 - ‖q‖^2) / ‖1 - q * Complex.exp (u * Complex.I)‖^2 := by
      rw [hnorm]
      simp [mobiusPsiDeriv, hq]
    rw [hval]
    exact h
  have hper : Complex.exp (((2 * π : ℝ) : ℂ) * Complex.I) = 1 := by
    have : ((2 * π : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.exp_two_pi_mul_I]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u)
      ((mobiusPsiDeriv_continuous ha).intervalIntegrable _ _)]
  simp only [F, hper, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
  ring

theorem mobiusPsi_two_pi {a : ℂ} (ha : ‖a‖ < 1) (ψ₀ : ℝ) :
    mobiusPsi a ψ₀ (2 * π) = mobiusPsi a ψ₀ 0 + 2 * π := by
  unfold mobiusPsi
  rw [integral_mobiusPsiDeriv ha]
  simp

theorem mobius_den_ne_zero' {a : ℂ} (ha : ‖a‖ < 1) (t : ℝ) :
    (1 : ℂ) - (starRingEnd ℂ) a * Complex.exp (t * Complex.I) ≠ 0 := by
  intro h
  have h' : (starRingEnd ℂ) a * Complex.exp (t * Complex.I) = 1 := by
    linear_combination -h
  have hnorm := congrArg norm h'
  rw [norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one, norm_one] at hnorm
  linarith

theorem mobius_w_norm {a : ℂ} (ha : ‖a‖ < 1) (θ t : ℝ) :
    ‖Complex.exp (θ * Complex.I) *
      ((Complex.exp (t * Complex.I) - a) /
        (1 - (starRingEnd ℂ) a * Complex.exp (t * Complex.I)))‖ = 1 := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_div]
  have hnum : ‖Complex.exp (t * Complex.I) - a‖ =
      ‖(1 : ℂ) - (starRingEnd ℂ) a * Complex.exp (t * Complex.I)‖ := by
    have he : Complex.exp (t * Complex.I) * (starRingEnd ℂ) (Complex.exp (t * Complex.I)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; simp
    have hid : (1 : ℂ) - (starRingEnd ℂ) a * Complex.exp (t * Complex.I)
        = Complex.exp (t * Complex.I) * (starRingEnd ℂ) (Complex.exp (t * Complex.I) - a) := by
      rw [map_sub]; linear_combination -he
    rw [hid, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_conj]
  rw [hnum, div_self]
  exact norm_ne_zero_iff.mpr (mobius_den_ne_zero' ha t)

theorem mobius_w_hasDerivAt {a : ℂ} (ha : ‖a‖ < 1) (θ s : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp (θ * Complex.I) *
      ((Complex.exp (t * Complex.I) - a) /
        (1 - (starRingEnd ℂ) a * Complex.exp (t * Complex.I))))
      (Complex.I * (mobiusPsiDeriv a s : ℂ) *
        (Complex.exp (θ * Complex.I) *
          ((Complex.exp (s * Complex.I) - a) /
            (1 - (starRingEnd ℂ) a * Complex.exp (s * Complex.I))))) s := by
  set e := Complex.exp (s * Complex.I) with he
  set q := (starRingEnd ℂ) a with hq
  have hD : (1 : ℂ) - q * e ≠ 0 := mobius_den_ne_zero' ha s
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I)) (e * Complex.I) s := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const Complex.I
    simpa [he] using h1.cexp
  have hN : HasDerivAt (fun t : ℝ => Complex.exp (t * Complex.I) - a)
    (e * Complex.I) s :=
    hE.sub_const a
  have hDd : HasDerivAt (fun t : ℝ => 1 - q * Complex.exp (t * Complex.I))
      (-(q * (e * Complex.I))) s := by
    simpa using (hE.const_mul q).const_sub 1
  have hQ := (hN.div hDd hD).const_mul (Complex.exp (θ * Complex.I))
  convert hQ using 1
  rw [← he]
  have hee : e * (starRingEnd ℂ) e = 1 := by
    rw [he, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]; simp
  have hna : ((‖a‖ : ℝ) : ℂ) ^ 2 = a * q := by
    rw [hq, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  have hnD : ((‖(1 : ℂ) - q * e‖ : ℝ) : ℂ) ^ 2
      = (1 - q * e) * (1 - a * (starRingEnd ℂ) e) := by
    have h := Complex.mul_conj ((1 : ℂ) - q * e)
    rw [Complex.normSq_eq_norm_sq] at h
    push_cast at h
    rw [← h]
    simp [hq, map_sub, map_mul]
  have hpsi : (mobiusPsiDeriv a s : ℂ)
      = (1 - a * q) / ((1 - q * e) * (1 - a * (starRingEnd ℂ) e)) := by
    unfold mobiusPsiDeriv
    push_cast
    rw [hna, hnD]
  have hconjD : e * (1 - a * (starRingEnd ℂ) e) = e - a := by
    linear_combination (-a) * hee
  have he0 : e ≠ 0 := by rw [he]; exact Complex.exp_ne_zero _
  have hD' : (1 : ℂ) - a * (starRingEnd ℂ) e ≠ 0 := by
    intro h0
    have : e - a = 0 := by rw [← hconjD, h0, mul_zero]
    have hae : a = e := by linear_combination -this
    have : ‖a‖ = 1 := by rw [hae, he, Complex.norm_exp_ofReal_mul_I]
    linarith
  have hNc : e - a = e * (1 - a * (starRingEnd ℂ) e) := hconjD.symm
  rw [hpsi, hNc]
  field_simp
  linear_combination (a * q) * hee

theorem mobiusDisque_circleMap_eq {c₁ c₂ : ℂ} {ε : ℝ} (hε : 0 < ε)
    {a : ℂ} (ha : ‖a‖ < 1) (θ : ℝ) :
    ∃ ψ₀ : ℝ, ∀ t : ℝ,
      mobiusDisque c₁ c₂ ε ε a θ (circleMap c₁ ε t)
        = circleMap c₂ ε (mobiusPsi a ψ₀ t) := by
  set w : ℝ → ℂ := fun t => Complex.exp (θ * Complex.I) *
    ((Complex.exp (t * Complex.I) - a) /
      (1 - (starRingEnd ℂ) a * Complex.exp (t * Complex.I))) with hw
  obtain ⟨ψ₀, hψ₀⟩ : ∃ ψ₀ : ℝ, Complex.exp (ψ₀ * Complex.I) = w 0 := by
    refine ⟨Complex.arg (w 0), ?_⟩
    have hn : ‖w 0‖ = 1 := mobius_w_norm ha θ 0
    have := Complex.norm_mul_exp_arg_mul_I (w 0)
    rw [hn] at this
    simpa using this
  refine ⟨ψ₀, fun t => ?_⟩
  have hψ : Complex.exp (mobiusPsi a ψ₀ t * Complex.I) = w t := by
    have hwd : ∀ s : ℝ, HasDerivAt w
        (Complex.I * (mobiusPsiDeriv a s : ℂ) * w s) s :=
      fun s => mobius_w_hasDerivAt ha θ s
    have hΨ : ∀ s : ℝ, HasDerivAt (fun s => (mobiusPsi a ψ₀ s : ℂ))
        (mobiusPsiDeriv a s : ℂ) s :=
      fun s => (hasDerivAt_mobiusPsi ha ψ₀ s).ofReal_comp
    have hH : ∀ s : ℝ, HasDerivAt
        (fun s => w s * Complex.exp (-(mobiusPsi a ψ₀ s : ℂ) * Complex.I)) 0 s := by
      intro s
      have h1 : HasDerivAt (fun s => Complex.exp (-(mobiusPsi a ψ₀ s : ℂ) * Complex.I))
          (Complex.exp (-(mobiusPsi a ψ₀ s : ℂ) * Complex.I) *
            (-(mobiusPsiDeriv a s : ℂ) * Complex.I)) s := by
        have := ((hΨ s).neg.mul_const Complex.I).cexp
        simpa using this
      have h2 := (hwd s).mul h1
      convert h2 using 1
      ring
    have hconst : ∀ s, w s * Complex.exp (-(mobiusPsi a ψ₀ s : ℂ) * Complex.I) = 1 := by
      intro s
      have hc := is_const_of_deriv_eq_zero
        (fun s => (hH s).differentiableAt) (fun s => (hH s).deriv) s 0
      rw [hc]
      simp [mobiusPsi, ← hψ₀, ← Complex.exp_add]
    have := hconst t
    have hexp : Complex.exp (-(mobiusPsi a ψ₀ t : ℂ) * Complex.I) *
        Complex.exp ((mobiusPsi a ψ₀ t : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]; simp
    calc Complex.exp ((mobiusPsi a ψ₀ t : ℂ) * Complex.I)
        = (w t * Complex.exp (-(mobiusPsi a ψ₀ t : ℂ) * Complex.I)) *
            Complex.exp ((mobiusPsi a ψ₀ t : ℂ) * Complex.I) := by rw [this, one_mul]
      _ = w t * (Complex.exp (-(mobiusPsi a ψ₀ t : ℂ) * Complex.I) *
            Complex.exp ((mobiusPsi a ψ₀ t : ℂ) * Complex.I)) := by ring
      _ = w t := by rw [hexp, mul_one]
  have hM : mobiusDisque c₁ c₂ ε ε a θ (circleMap c₁ ε t) = c₂ + (ε : ℂ) * w t := by
    have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
    have hd := mobius_den_ne_zero' ha t
    have hz : circleMap c₁ ε t - c₁ = (ε : ℂ) * Complex.exp (t * Complex.I) := by
      simp [circleMap, mul_comm]
    have hden : (ε : ℂ) - (starRingEnd ℂ) a * (circleMap c₁ ε t - c₁)
        = (ε : ℂ) * (1 - (starRingEnd ℂ) a * Complex.exp (t * Complex.I)) := by
      rw [hz]; ring
    have hnum : circleMap c₁ ε t - c₁ - a * (ε : ℂ)
        = (ε : ℂ) * (Complex.exp (t * Complex.I) - a) := by
      rw [hz]; ring
    simp only [mobiusDisque, hw]
    rw [hnum, hden]
    field_simp
  rw [hM, circleMap, ← hψ]



theorem mobiusDisque_chgt_var (c₁ c₂ : ℂ) {ε : ℝ} (hε : 0 < ε)
  (a : ℂ) (ha : ‖a‖ < 1) (θ : ℝ) :
    ∀ G : ℂ → ℂ, ContinuousOn G (Metric.sphere c₂ ε) →
      ∮ w in C(c₂, ε), G w =
        ∮ z in C(c₁, ε), G (mobiusDisque c₁ c₂ ε ε a θ z) * deriv
          (mobiusDisque c₁ c₂ ε ε a θ) z := by
  intro G hG
  set M := mobiusDisque c₁ c₂ ε ε a θ with hM
  obtain ⟨ψ₀, hΓ⟩ := mobiusDisque_circleMap_eq (c₁ := c₁) (c₂ := c₂) hε ha θ
  set ψ : ℝ → ℝ := mobiusPsi a ψ₀ with hψ
  have hψd : ∀ t, HasDerivAt ψ (mobiusPsiDeriv a t) t :=
    fun t => hasDerivAt_mobiusPsi ha ψ₀ t
  have hψ2π : ψ (2 * π) = ψ 0 + 2 * π := by
    simp only [hψ, mobiusPsi]
    rw [integral_mobiusPsiDeriv ha]
    simp
  have hchain : ∀ t, deriv (fun s => circleMap c₂ ε (ψ s)) t
      = deriv M (circleMap c₁ ε t) * deriv (circleMap c₁ ε) t := by
    intro t
    have hz : circleMap c₁ ε t ∈ Metric.sphere c₁ ε := circleMap_mem_sphere c₁ hε.le t
    have hMd : HasDerivAt M (deriv M (circleMap c₁ ε t)) (circleMap c₁ ε t) := by
      rw [hM]
      exact (hasDerivAt_mobiusDisque_sphere c₁ c₂ hε ha θ hz).differentiableAt.hasDerivAt
    have hcirc : HasDerivAt (circleMap c₁ ε) (deriv (circleMap c₁ ε) t) t :=
      (hasDerivAt_circleMap c₁ ε t).differentiableAt.hasDerivAt
    have hcomp : HasDerivAt (fun s => M (circleMap c₁ ε s))
        (deriv M (circleMap c₁ ε t) * deriv (circleMap c₁ ε) t) t := by
      have h := HasDerivAt.comp (h₂ := M) (h := circleMap c₁ ε) t hMd hcirc
      exact h
    have heq : (fun s => circleMap c₂ ε (ψ s)) = fun s => M (circleMap c₁ ε s) := by
      funext s; exact (hΓ s).symm
    rw [heq]
    exact hcomp.deriv
  have hfc : Continuous fun t : ℝ => G (circleMap c₂ ε t) * deriv (circleMap c₂ ε) t := by
    have h1 : Continuous fun t : ℝ => G (circleMap c₂ ε t) :=
      hG.comp_continuous (continuous_circleMap c₂ ε)
        (fun t => circleMap_mem_sphere c₂ hε.le t)
    have h2 : Continuous fun t : ℝ => deriv (circleMap c₂ ε) t := by
      simp only [deriv_circleMap]
      exact (continuous_circleMap 0 ε).mul continuous_const
    exact h1.mul h2
  have hfper : Function.Periodic
      (fun t : ℝ => G (circleMap c₂ ε t) * deriv (circleMap c₂ ε) t) (2 * π) := by
    intro t
    simp only [deriv_circleMap]
    rw [periodic_circleMap c₂ ε t, periodic_circleMap 0 ε t]
  have hψc : Continuous (mobiusPsiDeriv a) := mobiusPsiDeriv_continuous ha
  have key := intervalIntegral_reparam_periodic
    (fun t : ℝ => G (circleMap c₂ ε t) * deriv (circleMap c₂ ε) t) hfc hfper
    ψ (mobiusPsiDeriv a) hψd hψc hψ2π
  exact circleIntegral_chgt_var_final c₁ c₂ ε G M ψ (mobiusPsiDeriv a) hΓ hψd hchain key

theorem mobiusDisque_bijHolPresOrient (c₁ c₂ : ℂ) {ε : ℝ} (hε : 0 < ε)
    (a : ℂ) (ha : ‖a‖ < 1) (θ : ℝ) :
    BijHolPresOrientContinuity c₁ c₂ ε (mobiusDisque c₁ c₂ ε ε a θ) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold mobiusDisque
    have hden : ∀ z ∈ Metric.closedBall c₁ ε, (ε : ℂ) - (starRingEnd ℂ) a * (z - c₁) ≠ 0 := by
      intro z hz h
      have h1 : ‖(starRingEnd ℂ) a * (z - c₁)‖ = (ε : ℝ) := by
        have : (starRingEnd ℂ) a * (z - c₁) = ε := by linear_combination -h
        rw [this]; simp [abs_of_pos hε]
      have h2 : ‖(starRingEnd ℂ) a * (z - c₁)‖ ≤ ‖a‖ * ε := by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hz) (norm_nonneg _)
      nlinarith
    have hnum : DifferentiableOn ℂ (fun z : ℂ => z - c₁ - a * ε) (Metric.closedBall c₁ ε) := by
      fun_prop
    have hdenD : DifferentiableOn ℂ
        (fun z : ℂ => (ε : ℂ) - (starRingEnd ℂ) a * (z - c₁)) (Metric.closedBall c₁ ε) := by
      fun_prop
    have hdiv := hnum.div hdenD hden
    exact (hdiv.const_mul _).const_add _
  · refine ⟨mobiusDisque_mapsTo hε a ha θ, ?_, ?_⟩
    · intro z hz w hw hzw
      have hden : ∀ x ∈ Metric.sphere c₁ ε,
          (ε : ℂ) - (starRingEnd ℂ) a * (x - c₁) ≠ 0 := by
        intro x hx h
        have hx' : ‖x - c₁‖ = ε := by simpa [dist_eq_norm] using hx
        have : (starRingEnd ℂ) a * (x - c₁) = ε := by linear_combination -h
        have h1 := congrArg norm this
        rw [norm_mul, Complex.norm_conj, hx'] at h1
        simp [abs_of_pos hε] at h1
        nlinarith
      have hK : (ε : ℂ) * Complex.exp (θ * Complex.I) ≠ 0 := by
        apply mul_ne_zero
        · exact_mod_cast hε.ne'
        · exact Complex.exp_ne_zero _
      unfold mobiusDisque at hzw
      have h1 := add_left_cancel hzw
      have h2 := mul_left_cancel₀ hK h1
      have hz' := hden z hz
      have hw' := hden w hw
      rw [div_eq_div_iff hz' hw'] at h2
      have hne : (1 - (starRingEnd ℂ) a * a) ≠ 0 := by
        exact one_sub_conj_mul_ne_zero a ha
      have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
      have : (ε : ℂ) * (1 - (starRingEnd ℂ) a * a) * (z - w) = 0 := by
        linear_combination h2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (mul_ne_zero hε' hne)
      · exact sub_eq_zero.mp h
    · exact mobiusDisque_surjOn hε a ha θ
  · exact mobiusDisque_chgt_var c₁ c₂ hε a ha θ


theorem circleMap_neg_reflection (c : ℂ) (R : ℝ) (θ : ℝ) :
    circleMap (-c) R θ = -circleMap c R (θ + Real.pi) := by
  unfold circleMap
  have h : Complex.exp (↑(θ + Real.pi) * Complex.I)
      = -Complex.exp (↑θ * Complex.I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [h]
  ring

theorem circleMap_neg_conj (c : ℂ) (R : ℝ) (t : ℝ) :
    circleMap (-(starRingEnd ℂ) c) R t
      = -(starRingEnd ℂ) (circleMap c R (Real.pi - t)) := by
  apply Complex.ext
  · simp [circleMap, Complex.exp_re, Complex.exp_im,
      Real.cos_pi_sub, Real.sin_pi_sub]
    ring
  · simp [circleMap, Complex.exp_re, Complex.exp_im,
      Real.cos_pi_sub, Real.sin_pi_sub]
    ring

theorem deriv_circleMap_reflexion (R : ℝ) (t : ℝ) :
    circleMap 0 R t * Complex.I
      = (starRingEnd ℂ) (circleMap 0 R (Real.pi - t) * Complex.I) := by
  apply Complex.ext <;>
    simp [circleMap, Complex.exp_re, Complex.exp_im,
      Real.cos_pi_sub, Real.sin_pi_sub]

theorem integral_reflexion_periodique (F : ℝ → ℂ)
    (hper : Function.Periodic F (2 * Real.pi)) :
    ∫ t in (0 : ℝ)..2 * Real.pi, F (Real.pi - t)
      = ∫ t in (0 : ℝ)..2 * Real.pi, F t := by
  rw [intervalIntegral.integral_comp_sub_left F Real.pi]
  have h1 : Real.pi - 2 * Real.pi = -Real.pi := by ring
  rw [h1, sub_zero]
  have h2 := hper.intervalIntegral_add_eq (-Real.pi) 0
  have h3 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  rw [h3, zero_add] at h2
  exact h2

theorem intervalIntegral_conj' (f : ℝ → ℂ) (a b : ℝ) :
    (starRingEnd ℂ) (∫ t in a..b, f t) = ∫ t in a..b, (starRingEnd ℂ) (f t) := by
  by_cases hf : IntervalIntegrable f MeasureTheory.volume a b
  · exact (
      (Complex.conjCLE.toContinuousLinearMap.restrictScalars ℝ).intervalIntegral_comp_comm hf).symm
  · have hf' : ¬ IntervalIntegrable (fun t => (starRingEnd ℂ) (f t)) MeasureTheory.volume a b := by
      intro h
      apply hf
      have h2 : IntervalIntegrable (fun t => (starRingEnd ℂ) ((starRingEnd ℂ) (f t)))
          MeasureTheory.volume a b := by
        unfold IntervalIntegrable at h ⊢
        exact ⟨(Complex.conjCLE.toContinuousLinearMap.integrable_comp h.1),
               (Complex.conjCLE.toContinuousLinearMap.integrable_comp h.2)⟩
      simpa using h2
    rw [intervalIntegral.integral_undef hf, intervalIntegral.integral_undef hf']
    simp



end BijHoloDisc
