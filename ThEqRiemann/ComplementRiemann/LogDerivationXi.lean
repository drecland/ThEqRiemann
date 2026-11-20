import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition

/-! -/
namespace LogDerivXi


open Set Complex
open RiemannDef

lemma deriv_log_mul (f g : ℂ → ℂ) (x : ℂ)
    (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    deriv (fun y => f y * g y) x / (f x * g x)
      = deriv f x / f x + deriv g x / g x := by
  change deriv (f * g) x / (f x * g x) = deriv f x / f x + deriv g x / g x
  rw [deriv_mul hf hg]
  field_simp

lemma deriv_log_pi_cpow (s : ℂ) :
    deriv (fun y : ℂ => (Real.pi : ℂ) ^ (-y / 2)) s / (Real.pi : ℂ) ^ (-s / 2)
      = -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hfun : (fun y : ℂ => (Real.pi : ℂ) ^ (-y / 2))
      = fun y : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-y / 2)) := by
    funext y
    rw [Complex.cpow_def_of_ne_zero hpi]
  have hlog : Complex.log (Real.pi : ℂ) = (Real.log Real.pi : ℂ) := by
    rw [← Complex.ofReal_log Real.pi_pos.le]
  have hderiv : HasDerivAt
      (fun y : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-y / 2)))
      (Complex.exp (Complex.log (Real.pi : ℂ) * (-s / 2))
        * (Complex.log (Real.pi : ℂ) * (-1 / 2))) s := by
    have h1 : HasDerivAt (fun y : ℂ => -y / 2) (-1 / 2) s := by
      simpa using ((hasDerivAt_id s).neg).div_const 2
    have h2 := (h1.const_mul (Complex.log (Real.pi : ℂ))).cexp
    simpa [mul_comm] using h2
  rw [hfun, hderiv.deriv, Complex.cpow_def_of_ne_zero hpi, hlog]
  have hexp : Complex.exp ((Real.log Real.pi : ℂ) * (-s / 2)) ≠ 0 :=
    Complex.exp_ne_zero _
  rw [hlog] at *
  field_simp

lemma deriv_log_gamma_demi (s : ℂ) (hs : 0 < s.re) :
    deriv (fun y : ℂ => Complex.Gamma (y / 2)) s / Complex.Gamma (s / 2)
      = (1 / 2 : ℂ) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) := by
  have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre : (s / 2).re = (-(m : ℂ)).re := by rw [h]
    simp at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ hne
  have hg : HasDerivAt (fun y : ℂ => y / 2) (1 / 2 : ℂ) s := by
    simpa using (hasDerivAt_id s).div_const 2
  have hcomp : HasDerivAt (fun y : ℂ => Complex.Gamma (y / 2))
      (deriv Complex.Gamma (s / 2) * (1 / 2 : ℂ)) s :=
    HasDerivAt.comp s hΓ.hasDerivAt hg
  rw [hcomp.deriv]
  ring

lemma deriv_log_poly (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    deriv (fun y : ℂ => y * (y - 1)) s / (s * (s - 1)) = 1 / s + 1 / (s - 1) := by
  have h1' : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hd : HasDerivAt (fun y : ℂ => y * (y - 1)) (1 * (s - 1) + s * 1) s :=
    (hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)
  rw [hd.deriv]
  field_simp

lemma xi_produit (s : ℂ) (hs : 0 < s.re) :
    xi s = (1 / 2 : ℂ) * (s * (s - 1)) *
      (((Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) * riemannZeta s) := by
  rw [xi_eq_of_re_pos s hs, Complex.Gammaℝ_def]
  ring

lemma differentiableAt_pi_cpow (s : ℂ) :
    DifferentiableAt ℂ (fun y : ℂ => (Real.pi : ℂ) ^ (-y / 2)) s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfun : (fun y : ℂ => (Real.pi : ℂ) ^ (-y / 2))
      = fun y : ℂ => Complex.exp (Complex.log (Real.pi : ℂ) * (-y / 2)) := by
    funext y
    rw [Complex.cpow_def_of_ne_zero hpi]
  rw [hfun]
  fun_prop

lemma deriv_log_Gammaℝ (s : ℂ) (hs : 0 < s.re) :
    deriv Complex.Gammaℝ s / Complex.Gammaℝ s
      = -(1 / 2 : ℂ) * (Real.log Real.pi : ℂ)
        + (1 / 2 : ℂ) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2)) := by
  have hfun : Complex.Gammaℝ = fun y : ℂ => (Real.pi : ℂ) ^ (-y / 2) * Complex.Gamma (y / 2) := by
    funext y
    exact Complex.Gammaℝ_def y
  have hpi : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [Complex.cpow_def_of_ne_zero hpi0]
    exact Complex.exp_ne_zero _
  have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre : (s / 2).re = (-(m : ℂ)).re := by rw [h]
    simp at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hΓ0 : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hne
  have hd1 : DifferentiableAt ℂ (fun y : ℂ => (Real.pi : ℂ) ^ (-y / 2)) s :=
    differentiableAt_pi_cpow s
  have hd2 : DifferentiableAt ℂ (fun y : ℂ => Complex.Gamma (y / 2)) s := by
    have hΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
      Complex.differentiableAt_Gamma _ hne
    exact hΓ.comp s (by fun_prop)
  rw [hfun, deriv_log_mul _ _ s hd1 hd2 hpi hΓ0,
    deriv_log_pi_cpow s, deriv_log_gamma_demi s hs]

lemma deriv_log_polyXi (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    deriv (fun y : ℂ => (1 / 2 : ℂ) * y * (y - 1)) s
        / ((1 / 2 : ℂ) * s * (s - 1))
      = 1 / s + 1 / (s - 1) := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hd : HasDerivAt (fun y : ℂ => (1 / 2 : ℂ) * y * (y - 1))
      ((1 / 2 : ℂ) * (s - 1) + (1 / 2 : ℂ) * s) s := by
    have h1' : HasDerivAt (fun y : ℂ => (1 / 2 : ℂ) * y) (1 / 2 : ℂ) s := by
      simpa using (hasDerivAt_id s).const_mul (1 / 2 : ℂ)
    have h2' : HasDerivAt (fun y : ℂ => y - 1) 1 s :=
      (hasDerivAt_id s).sub_const 1
    have := h1'.mul h2'
    convert this using 1
    ring
  rw [hd.deriv]
  field_simp

lemma deriv_log_xi (s : ℂ) (hs : 0 < s.re) (h1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    deriv xi s / xi s
      = 1 / s + 1 / (s - 1) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ)
        + (1 / 2 : ℂ) * (deriv Complex.Gamma (s / 2) / Complex.Gamma (s / 2))
        + deriv riemannZeta s / riemannZeta s := by
  have h0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hG0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hA0 : (1 / 2 : ℂ) * s * (s - 1) ≠ 0 := by
    have : (1 / 2 : ℂ) ≠ 0 := by norm_num
    exact mul_ne_zero (mul_ne_zero this h0) hs1
  have hne : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre : (s / 2).re = (-(m : ℂ)).re := by rw [h]
    simp at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hGd : DifferentiableAt ℂ Gammaℝ s := by
    have hfun : Gammaℝ = fun y : ℂ => (Real.pi : ℂ) ^ (-y / 2) * Complex.Gamma (y / 2) := by
      funext y; exact Complex.Gammaℝ_def y
    rw [hfun]
    refine (differentiableAt_pi_cpow s).mul ?_
    exact (Complex.differentiableAt_Gamma _ hne).comp s (by fun_prop)
  have hZd : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta h1
  have hAd : DifferentiableAt ℂ (fun y : ℂ => (1 / 2 : ℂ) * y * (y - 1)) s := by
    fun_prop
  have hBd : DifferentiableAt ℂ (fun y : ℂ => Gammaℝ y * riemannZeta y) s :=
    hGd.mul hZd
  have hloc : xi =ᶠ[nhds s]
      fun y : ℂ => ((1 / 2 : ℂ) * y * (y - 1)) * (Gammaℝ y * riemannZeta y) := by
    have hopen : IsOpen {y : ℂ | 0 < y.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds hs] with y hy
    exact xi_eq_of_re_pos y hy
  rw [hloc.deriv_eq, hloc.eq_of_nhds]
  rw [deriv_log_mul _ _ s hAd hBd hA0 (mul_ne_zero hG0 hzeta),
    deriv_log_mul _ _ s hGd hZd hG0 hzeta,
    deriv_log_polyXi s h0 h1, deriv_log_Gammaℝ s hs]
  ring

lemma decomposition_derivee_log_xi (z : ℂ)
    (hre : 0 < (1 / 2 + z).re) (hz : z ≠ 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z) ≠ 0) :
    deriv xi (1 / 2 + z) / xi (1 / 2 + z)
      = 1 / (1 / 2 + z) - 1 / (1 / 2 - z) - (1 / 2 : ℂ) * (Real.log Real.pi : ℂ)
        + (1 / 2 : ℂ) * (deriv Complex.Gamma (1 / 4 + z / 2)
            / Complex.Gamma (1 / 4 + z / 2))
        + deriv riemannZeta (1 / 2 + z) / riemannZeta (1 / 2 + z) := by
  have hs1 : (1 / 2 + z : ℂ) ≠ 1 := by
    intro h; apply hz; linear_combination h
  have h := deriv_log_xi (1 / 2 + z) hre hs1 hzeta
  have e1 : (1 / 2 + z : ℂ) - 1 = -(1 / 2 - z) := by ring
  have e2 : (1 / 2 + z) / 2 = 1 / 4 + z / 2 := by ring
  rw [e2] at h
  rw [h, e1, one_div_neg_eq_neg_one_div]
  ring

end LogDerivXi
