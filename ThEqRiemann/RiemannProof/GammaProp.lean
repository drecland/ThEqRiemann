import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition

/-! -/
namespace GammaRiemann

open Set Complex RiemannDef

lemma LambdaZeros_eq : LambdaZeros = {γ | GLambda γ = 0} := rfl

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












end GammaRiemann
