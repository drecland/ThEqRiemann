import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.AnalyticResInt
import ThEqRiemann.IntegralResolutionTheorem.AevalPolynomial
import ThEqRiemann.IntegralResolutionTheorem.TraceMtMul
import ThEqRiemann.RiemannProof.RiemannDefinition

/-! -/
namespace CircInt2

open Set Complex Module End ResDef

lemma circleIntegral_inv_sub (c μ : ℂ) (R : ℝ) (hμ : μ ∈ Metric.ball c R) :
    ∮ z in C(c, R), (z - μ)⁻¹ = 2 * Real.pi * Complex.I := by
  have h := DiffContOnCl.circleIntegral_sub_inv_smul
    (f := fun _ : ℂ => (1 : ℂ)) (c := c) (R := R) (w := μ)
    (differentiableOn_const 1).diffContOnCl hμ
  simpa using h

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


lemma logDeriv_factor (T : End ℂ V) (g : ℂ → ℂ) (z : ℂ)
    (hz : ∀ μ ∈ spec T, z ≠ μ) (hg : DifferentiableAt ℂ g z)
    (hg0 : g z ≠ 0) :
    deriv (fun w => (∏ μ ∈ spec T, (w - μ) ^ mT T μ) * g w) z /
      ((∏ μ ∈ spec T, (z - μ) ^ mT T μ) * g z)
      = ∑ μ ∈ spec T, (mT T μ : ℂ) / (z - μ) + deriv g z / g z := by
  classical
  have hone : ∀ μ ∈ spec T,
      logDeriv (fun w : ℂ => (w - μ) ^ mT T μ) z = (mT T μ : ℂ) / (z - μ) := by
    intro μ hμ
    have hzm : z - μ ≠ 0 := sub_ne_zero.mpr (hz μ hμ)
    rw [logDeriv_apply]
    have hd : deriv (fun w : ℂ => (w - μ) ^ mT T μ) z
        = (mT T μ : ℂ) * (z - μ) ^ (mT T μ - 1) := by
      have h := ((hasDerivAt_id z).sub_const μ).pow (mT T μ)
      simp []
    rw [hd]
    rcases Nat.eq_zero_or_pos (mT T μ) with h0 | hpos
    · simp [h0]
    · have : (z - μ) ^ mT T μ = (z - μ) ^ (mT T μ - 1) * (z - μ) := by
        rw [← pow_succ, Nat.sub_add_cancel hpos]
      rw [this]
      field_simp
  have hprod : ∀ s : Finset ℂ, s ⊆ spec T →
      (∏ μ ∈ s, (z - μ) ^ mT T μ ≠ 0 ∧
       DifferentiableAt ℂ (fun w : ℂ => ∏ μ ∈ s, (w - μ) ^ mT T μ) z ∧
       logDeriv (fun w : ℂ => ∏ μ ∈ s, (w - μ) ^ mT T μ) z
         = ∑ μ ∈ s, (mT T μ : ℂ) / (z - μ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨by simp, by simp, ?_⟩
      simp [logDeriv_apply]
    | insert a s ha ih =>
      intro hs
      obtain ⟨h1, h2, h3⟩ := ih (fun x hx => hs (Finset.mem_insert_of_mem hx))
      have haT : a ∈ spec T := hs (Finset.mem_insert_self a s)
      have hane : (z - a) ^ mT T a ≠ 0 :=
        pow_ne_zero _ (sub_ne_zero.mpr (hz a haT))
      have had : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ mT T a) z := by
        fun_prop
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.prod_insert ha]; exact mul_ne_zero hane h1
      · simp only [Finset.prod_insert ha]; exact had.mul h2
      · have := logDeriv_mul (x := z)
          (f := fun w : ℂ => (w - a) ^ mT T a)
          (g := fun w : ℂ => ∏ μ ∈ s, (w - μ) ^ mT T μ) hane h1 had h2
        simp only [Finset.prod_insert ha, Finset.sum_insert ha]
        rw [show (fun w : ℂ => (w - a) ^ mT T a * ∏ μ ∈ s, (w - μ) ^ mT T μ)
              = (fun w : ℂ => (w - a) ^ mT T a) * (fun w : ℂ => ∏ μ ∈ s, (w - μ) ^ mT T μ)
              from rfl, this, hone a haT, h3]
  obtain ⟨hPne, hPd, hP⟩ := hprod (spec T) (Finset.Subset.refl _)
  have hmul := logDeriv_mul (x := z)
    (f := fun w : ℂ => ∏ μ ∈ spec T, (w - μ) ^ mT T μ) (g := g) hPne hg0 hPd hg
  rw [hP, logDeriv_apply g] at hmul
  exact hmul

-- Cauchy-Goursat ---
lemma circleIntegral_logDeriv_zero (g : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hg : AnalyticOnNhd ℂ g (Metric.closedBall c R))
    (hg0 : ∀ z ∈ Metric.closedBall c R, g z ≠ 0) :
    ∮ z in C(c, R), z * (deriv g z / g z) = 0 := by
  have hdg : AnalyticOnNhd ℂ (deriv g) (Metric.closedBall c R) := hg.deriv
  have hF : AnalyticOnNhd ℂ (fun z => z * (deriv g z / g z))
      (Metric.closedBall c R) := by
    intro z hz
    exact analyticAt_id.mul ((hdg z hz).div (hg z hz) (hg0 z hz))
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR
    Set.countable_empty hF.continuousOn
    (fun x hx => (hF x
      (Metric.ball_subset_closedBall hx.1)).differentiableAt)

open AnalyticRes in
theorem argument_principle_trace'
    (T : End ℂ V) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hnz : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (hzeros : ∀ μ ∈ spec T,
      μ ∈ Metric.ball c R ∧ f μ = 0 ∧ analyticOrderAt f μ = (mT T μ : ℕ∞))
    (hall : ∀ z ∈ Metric.ball c R, f z = 0 → z ∈ spec T) :
    (1 / (2 * Real.pi * Complex.I)) *
      (∮ z in C(c, R), z * (deriv f z / f z)) = ∑ μ ∈ spec T, (mT T μ : ℂ) * μ := by
  classical
  obtain ⟨g, hg, hg0, hfg, hfg'⟩ := factor_f T f c R hR hf hnz hzeros hall
  have hzsph : ∀ z ∈ Metric.sphere c R, ∀ μ ∈ spec T, z ≠ μ := by
    intro z hz μ hμ hzμ
    have := (hzeros μ hμ).1
    rw [← hzμ] at this
    rw [Metric.mem_sphere] at hz
    rw [Metric.mem_ball] at this
    linarith
  have hcirc : ∀ z ∈ Metric.sphere c R,
      z * (deriv f z / f z)
        = ∑ μ ∈ spec T, (mT T μ : ℂ) * (1 + μ / (z - μ)) + z * (deriv g z / g z) := by
    intro z hz
    have hzc : z ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hz
    have hderiv : deriv f z
        = deriv (fun w => (∏ μ ∈ spec T, (w - μ) ^ mT T μ) * g w) z :=
      (hfg' z hzc).deriv_eq
    have hval : f z = (∏ μ ∈ spec T, (z - μ) ^ mT T μ) * g z := hfg z hzc
    have hlog := logDeriv_factor T g z (hzsph z hz)
      ((hg z hzc).differentiableAt) (hg0 z hzc)
    rw [hderiv, hval, hlog]
    have hsum : z * ∑ μ ∈ spec T, (mT T μ : ℂ) / (z - μ)
        = ∑ μ ∈ spec T, (mT T μ : ℂ) * (1 + μ / (z - μ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun μ hμ => ?_)
      have : z - μ ≠ 0 := sub_ne_zero.mpr (hzsph z hz μ hμ)
      field_simp
      ring
    rw [mul_add, hsum]
  have hint : ∮ z in C(c, R), z * (deriv f z / f z)
      = ∮ z in C(c, R),
          (∑ μ ∈ spec T, (mT T μ : ℂ) * (1 + μ / (z - μ)) + z * (deriv g z / g z)) := by
    exact circleIntegral.integral_congr hR.le hcirc
  rw [hint]
  have hcont1 : ∀ μ ∈ spec T, ContinuousOn
      (fun z : ℂ => (mT T μ : ℂ) * (1 + μ / (z - μ))) (Metric.sphere c R) := by
    intro μ hμ
    have hne : ∀ z ∈ Metric.sphere c R, z - μ ≠ 0 :=
      fun z hz => sub_ne_zero.mpr (hzsph z hz μ hμ)
    refine continuousOn_const.mul (continuousOn_const.add (continuousOn_const.div
      (continuousOn_id.sub continuousOn_const) hne))
  have hint1 : ∀ μ ∈ spec T, CircleIntegrable
      (fun z : ℂ => (mT T μ : ℂ) * (1 + μ / (z - μ))) c R := fun μ hμ =>
    ((hcont1 μ hμ).mono (fun z hz => hz)).circleIntegrable hR.le
  have hint2 : CircleIntegrable (fun z : ℂ => z * (deriv g z / g z)) c R := by
    have hF : AnalyticOnNhd ℂ (fun z => z * (deriv g z / g z)) (Metric.closedBall c R) :=
      fun z hz => analyticAt_id.mul ((hg.deriv z hz).div (hg z hz) (hg0 z hz))
    exact (hF.continuousOn.mono Metric.sphere_subset_closedBall).circleIntegrable hR.le
  have hsumint : CircleIntegrable
      (fun z : ℂ => ∑ μ ∈ spec T, (mT T μ : ℂ) * (1 + μ / (z - μ))) c R := by
    have hc : ContinuousOn
        (fun z : ℂ => ∑ μ ∈ spec T, (mT T μ : ℂ) * (1 + μ / (z - μ)))
        (Metric.sphere c R) :=
      continuousOn_finsetSum _ hcont1
    exact hc.circleIntegrable hR.le
  rw [circleIntegral.integral_add hsumint hint2]
  have hsplit : (∮ z in C(c, R), ∑ μ ∈ spec T, (mT T μ : ℂ) * (1 + μ / (z - μ)))
      = ∑ μ ∈ spec T, ∮ z in C(c, R), (mT T μ : ℂ) * (1 + μ / (z - μ)) := by
    unfold circleIntegral
    rw [← intervalIntegral.integral_finsetSum]
    · congr 1
      funext θ
      rw [Finset.smul_sum]
    · intro μ hμ
      have hI : IntervalIntegrable
          (fun θ : ℝ => (fun z : ℂ => (mT T μ : ℂ) * (1 + μ / (z - μ))) (circleMap c R θ))
          MeasureTheory.volume 0 (2 * Real.pi) := hint1 μ hμ
      have hd : Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
        have : deriv (circleMap c R) = fun θ => circleMap 0 R θ * Complex.I := by
          funext θ; exact deriv_circleMap c R θ
        rw [this]
        exact (continuous_circleMap 0 R).mul continuous_const
      exact hI.continuousOn_mul hd.continuousOn
  rw [hsplit]
  have hone : ∀ μ ∈ spec T,
      ∮ z in C(c, R), (mT T μ : ℂ) * (1 + μ / (z - μ))
        = (mT T μ : ℂ) * (2 * Real.pi * Complex.I * μ) := by
    intro μ hμ
    have hμb : μ ∈ Metric.ball c R := (hzeros μ hμ).1
    have hne : ∀ z ∈ Metric.sphere c R, z - μ ≠ 0 :=
      fun z hz => sub_ne_zero.mpr (hzsph z hz μ hμ)
    have hcI : CircleIntegrable (fun _ : ℂ => (1 : ℂ)) c R :=
      continuousOn_const.circleIntegrable hR.le
    have hdiv : CircleIntegrable (fun z : ℂ => μ / (z - μ)) c R :=
      (continuousOn_const.div (continuousOn_id.sub continuousOn_const) hne
        ).circleIntegrable hR.le
    rw [circleIntegral.integral_const_mul,
        circleIntegral.integral_add hcI hdiv]
    have h1 : ∮ z in C(c, R), (1 : ℂ) = 0 := by
      simp only [circleIntegral, deriv_circleMap, smul_eq_mul, mul_one]
      have hprim : ∀ θ ∈ Set.uIcc (0:ℝ) (2 * Real.pi),
          HasDerivAt (fun θ : ℝ => circleMap 0 R θ) (circleMap 0 R θ * Complex.I) θ :=
        fun θ _ => hasDerivAt_circleMap 0 R θ
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hprim
        ((continuous_circleMap 0 R).mul continuous_const |>.intervalIntegrable _ _)]
      simp [circleMap]
    have h2 : ∮ z in C(c, R), μ / (z - μ) = 2 * Real.pi * Complex.I * μ := by
      have hres := circleIntegral.integral_sub_inv_of_mem_ball hμb
      have hfun : (fun z : ℂ => μ / (z - μ)) = fun z => μ * (z - μ)⁻¹ := by
        funext z; rw [div_eq_mul_inv]
      rw [hfun, circleIntegral.integral_const_mul, hres]
      ring
    rw [h1, h2, zero_add]
  rw [Finset.sum_congr rfl hone,
      circleIntegral_logDeriv_zero g c R hR.le hg hg0, add_zero]
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  field_simp



open TraceMtMulRes in
theorem argument_principle_trace
    (T : End ℂ V) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : ∃ r > R, DifferentiableOn ℂ f (Metric.ball c r))
    (hnz : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (hzeros : ∀ μ ∈ spec T,
      μ ∈ Metric.ball c R ∧ f μ = 0 ∧ analyticOrderAt f μ = (mT T μ : ℕ∞))
    (hall : ∀ z ∈ Metric.ball c R, f z = 0 → z ∈ spec T) :
    (1 / (2 * Real.pi * Complex.I)) *
      (∮ z in C(c, R), z * (deriv f z / f z)) = LinearMap.trace ℂ V T := by
  obtain ⟨r, hrR, hdiff⟩ := hf
  have hf' : AnalyticOnNhd ℂ f (Metric.closedBall c R) :=
    (hdiff.analyticOnNhd Metric.isOpen_ball).mono
      (Metric.closedBall_subset_ball hrR)
  rw [argument_principle_trace' T f c R hR hf' hnz hzeros hall,
      ← trace_eq_sum_mT_mul T]


-----------------------------------------------------------------------
open Aeval in
theorem trace_resolvent
    (T : End ℂ V) (z : ℂ) (hz : z ∉ spec T) :
    LinearMap.trace ℂ V (Ring.inverse ((algebraMap ℂ (End ℂ V) z) - T))
      = ∑ μ ∈ spec T, (mT T μ : ℂ) / (z - μ) := by
  obtain ⟨Q, hQ, hQeval⟩ := resolvent_eq_aeval T z hz
  rw [hQ]
  rw [trace_aeval_eq_sum T Q]
  refine Finset.sum_congr rfl (fun μ hμ => ?_)
  rw [hQeval μ hμ, div_eq_mul_inv]


theorem cauchy_formula_circle
    (F : ℂ → ℂ) (c μ : ℂ) (R : ℝ) (_ : 0 < R)
    (hμ : μ ∈ Metric.ball c R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall c R)) :
    (1 / (2 * Real.pi * Complex.I)) * (∮ z in C(c, R), F z / (z - μ)) = F μ := by
  have h := hF.circleIntegral_sub_inv_smul hμ
  have h2 : (∮ z in C(c, R), F z / (z - μ)) =
    (2 * Real.pi * Complex.I) * F μ := by
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  rw [h2]
  have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp


theorem contour_integral_resInt
    (T : End ℂ V) (f F : ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hR : 0 < R)
    (hspec : ∀ μ ∈ spec T, μ ∈ Metric.ball c R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall c R))
    (hFf : ∀ μ ∈ spec T, F μ = f μ) :
    (1 / (2 * Real.pi * Complex.I)) *
      (∮ z in C(c, R), F z * LinearMap.trace ℂ V
        (Ring.inverse ((algebraMap ℂ (End ℂ V) z) - T))) = resInt T f := by
  have hnot : ∀ z ∈ Metric.sphere c R, z ∉ spec T := by
    intro z hz hzs
    have h1 : z ∈ Metric.ball c R := hspec z hzs
    rw [Metric.mem_ball] at h1
    rw [Metric.mem_sphere] at hz
    linarith
  have hcongr : (∮ z in C(c, R), F z * LinearMap.trace ℂ V
        (Ring.inverse ((algebraMap ℂ (End ℂ V) z) - T)))
      = ∮ z in C(c, R), ∑ μ ∈ spec T, (mT T μ : ℂ) * (F z / (z - μ)) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    simp only
    rw [trace_resolvent T z (hnot z hz), Finset.mul_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    ring
  have hint : ∀ μ ∈ spec T,
      CircleIntegrable (fun z => (mT T μ : ℂ) * (F z / (z - μ))) c R := by
    intro μ hμ
    apply ContinuousOn.circleIntegrable hR.le
    have hFc : ContinuousOn F (Metric.sphere c R) :=
      hF.continuousOn.mono Metric.sphere_subset_closedBall
    have hne : ∀ z ∈ Metric.sphere c R, z - μ ≠ 0 := by
      intro z hz h
      exact hnot z hz (sub_eq_zero.mp h ▸ hμ)
    exact continuousOn_const.mul
      (hFc.div (continuousOn_id.sub continuousOn_const) hne)
  have hsum : (∮ z in C(c, R), ∑ μ ∈ spec T, (mT T μ : ℂ) * (F z / (z - μ)))
      = ∑ μ ∈ spec T, ∮ z in C(c, R), (mT T μ : ℂ) * (F z / (z - μ)) := by
    simp only [circleIntegral, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    refine intervalIntegral.integral_finsetSum (fun μ hμ => ?_)
    have hi := hint μ hμ
    unfold CircleIntegrable at hi
    have hd : Continuous (fun θ : ℝ => circleMap 0 R θ * Complex.I) :=
      (continuous_circleMap 0 R).mul continuous_const
    have hI : IntervalIntegrable
        (fun θ : ℝ => circleMap 0 R θ * Complex.I *
          (↑(mT T μ) * (F (circleMap c R θ) / (circleMap c R θ - μ))))
        MeasureTheory.volume 0 (2 * Real.pi) :=
      hi.continuousOn_mul hd.continuousOn
    convert hI using 1
    funext θ
    simp only [deriv_circleMap]
  rw [hcongr, hsum]
  calc (1 / (2 * Real.pi * Complex.I)) *
        ∑ μ ∈ spec T, ∮ z in C(c, R), (mT T μ : ℂ) * (F z / (z - μ))
      = ∑ μ ∈ spec T, (mT T μ : ℂ) *
          ((1 / (2 * Real.pi * Complex.I)) * ∮ z
            in C(c, R), F z / (z - μ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [circleIntegral.integral_const_mul]
        ring
    _ = ∑ μ ∈ spec T, (mT T μ : ℂ) * F μ := by
        refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [cauchy_formula_circle F c μ R hR (hspec μ hμ) hF]
    _ = resInt T f := by
        unfold resInt
        refine Finset.sum_congr rfl fun μ hμ => ?_
        rw [hFf μ hμ, nsmul_eq_mul]



-----------------------------------------------------------------------


lemma logDeriv_sub_pow (μ z : ℂ) (n : ℕ) (hz : z ≠ μ) :
    logDeriv (fun w : ℂ => (w - μ) ^ n) z = (n : ℂ) / (z - μ) := by
  have hne : z - μ ≠ 0 := sub_ne_zero.mpr hz
  rw [logDeriv_apply]
  have hd : deriv (fun w : ℂ => (w - μ) ^ n) z = (n : ℂ) * (z - μ) ^ (n - 1) := by
    have h1 : HasDerivAt (fun w : ℂ => w - μ) 1 z := (hasDerivAt_id z).sub_const μ
    simp
  rw [hd]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    field_simp
    ring

lemma logDeriv_prod_sub_pow (Z : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hZz : ∀ μ ∈ Z, z ≠ μ) :
    logDeriv (fun w : ℂ => ∏ μ ∈ Z, (w - μ) ^ m μ) z
      = ∑ μ ∈ Z, (m μ : ℂ) / (z - μ) := by
  induction Z using Finset.induction_on with
  | empty => simp [logDeriv_apply]
  | insert a s ha ih =>
    have hza : z ≠ a := hZz a (Finset.mem_insert_self a s)
    have hzs : ∀ μ ∈ s, z ≠ μ := fun μ hμ => hZz μ (Finset.mem_insert_of_mem hμ)
    have hsplit : (fun w : ℂ => ∏ μ ∈ insert a s, (w - μ) ^ m μ)
        = fun w => (w - a) ^ m a * ∏ μ ∈ s, (w - μ) ^ m μ := by
      ext w; rw [Finset.prod_insert ha]
    rw [hsplit, Finset.sum_insert ha]
    have hne1 : (z - a) ^ m a ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
    have hne2 : ∏ μ ∈ s, (z - μ) ^ m μ ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun μ hμ => pow_ne_zero _ (sub_ne_zero.mpr (hzs μ hμ))
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => (w - a) ^ m a) z := by fun_prop
    have hd2 : DifferentiableAt ℂ (fun w : ℂ => ∏ μ ∈ s, (w - μ) ^ m μ) z := by fun_prop
    have hmul : logDeriv ((fun w : ℂ => (w - a) ^ m a) *
                          (fun w : ℂ => ∏ μ ∈ s, (w - μ) ^ m μ)) z
        = logDeriv (fun w : ℂ => (w - a) ^ m a) z
          + logDeriv (fun w : ℂ => ∏ μ ∈ s, (w - μ) ^ m μ) z :=
      logDeriv_mul z hne1 hne2 hd1 hd2
    have hgoal : logDeriv (fun w : ℂ => (w - a) ^ m a * ∏ μ ∈ s, (w - μ) ^ m μ) z
        = logDeriv (fun w : ℂ => (w - a) ^ m a) z
          + logDeriv (fun w : ℂ => ∏ μ ∈ s, (w - μ) ^ m μ) z := hmul
    rw [hgoal, logDeriv_sub_pow a z (m a) hza, ih hzs]


lemma logDeriv_inv_eq_neg (h : ℂ → ℂ) (z : ℂ)
    (hd : DifferentiableAt ℂ h z) (hz : h z ≠ 0) :
    logDeriv (fun w => (h w)⁻¹) z = - logDeriv h z := by
  have hinv : HasDerivAt (fun w => (h w)⁻¹) (-(deriv h z) / (h z) ^ 2) z :=
    hd.hasDerivAt.inv hz
  rw [logDeriv_apply, logDeriv_apply, hinv.deriv]
  field_simp


lemma logDeriv_factorisation
    (g : ℂ → ℂ) (Z P : Finset ℂ) (m ν : ℂ → ℕ) (z : ℂ)
    (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0)
    (hZz : ∀ μ ∈ Z, z ≠ μ) (hPz : ∀ p ∈ P, z ≠ p) :
    logDeriv (fun w => g w * (∏ μ ∈ Z, (w - μ) ^ m μ) / ∏ p ∈ P, (w - p) ^ ν p) z
      = logDeriv g z + ∑ μ ∈ Z, (m μ : ℂ) / (z - μ) - ∑ p ∈ P, (ν p : ℂ) / (z - p) := by
  have hZne : ∏ μ ∈ Z, (z - μ) ^ m μ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun μ hμ => pow_ne_zero _ (sub_ne_zero.mpr (hZz μ hμ))
  have hPne : ∏ p ∈ P, (z - p) ^ ν p ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (sub_ne_zero.mpr (hPz p hp))
  have hdg : DifferentiableAt ℂ g z := hg.differentiableAt
  have hdZ : DifferentiableAt ℂ (fun w : ℂ => ∏ μ ∈ Z, (w - μ) ^ m μ) z := by fun_prop
  have hdP : DifferentiableAt ℂ (fun w : ℂ => ∏ p ∈ P, (w - p) ^ ν p) z := by fun_prop
  have hrew : (fun w : ℂ => g w * (∏ μ ∈ Z, (w - μ) ^ m μ) / ∏ p ∈ P, (w - p) ^ ν p)
      = fun w => (g w * ∏ μ ∈ Z, (w - μ) ^ m μ) * (∏ p ∈ P, (w - p) ^ ν p)⁻¹ := by
    ext w; rw [div_eq_mul_inv]
  rw [hrew]
  have hgZne : g z * ∏ μ ∈ Z, (z - μ) ^ m μ ≠ 0 := mul_ne_zero hgz hZne
  have hPinv_ne : (∏ p ∈ P, (z - p) ^ ν p)⁻¹ ≠ 0 := inv_ne_zero hPne
  have hdgZ : DifferentiableAt ℂ (fun w : ℂ => g w * ∏ μ ∈ Z, (w - μ) ^ m μ) z :=
    hdg.mul hdZ
  have hdPinv : DifferentiableAt ℂ (fun w : ℂ => (∏ p ∈ P, (w - p) ^ ν p)⁻¹) z :=
    hdP.inv hPne
  have h4 : logDeriv ((fun w : ℂ => g w * ∏ μ ∈ Z, (w - μ) ^ m μ) *
                      (fun w : ℂ => (∏ p ∈ P, (w - p) ^ ν p)⁻¹)) z
      = logDeriv (fun w : ℂ => g w * ∏ μ ∈ Z, (w - μ) ^ m μ) z
        + logDeriv (fun w : ℂ => (∏ p ∈ P, (w - p) ^ ν p)⁻¹) z :=
    logDeriv_mul z hgZne hPinv_ne hdgZ hdPinv
  have h5 : logDeriv ((g) * (fun w : ℂ => ∏ μ ∈ Z, (w - μ) ^ m μ)) z
      = logDeriv g z + logDeriv (fun w : ℂ => ∏ μ ∈ Z, (w - μ) ^ m μ) z :=
    logDeriv_mul z hgz hZne hdg hdZ
  have h4' : logDeriv (fun w : ℂ => (g w * ∏ μ ∈ Z, (w - μ) ^ m μ) *
                                     (∏ p ∈ P, (w - p) ^ ν p)⁻¹) z
      = logDeriv (fun w : ℂ => g w * ∏ μ ∈ Z, (w - μ) ^ m μ) z
        + logDeriv (fun w : ℂ => (∏ p ∈ P, (w - p) ^ ν p)⁻¹) z := h4
  have h5' : logDeriv (fun w : ℂ => g w * ∏ μ ∈ Z, (w - μ) ^ m μ) z
      = logDeriv g z + logDeriv (fun w : ℂ => ∏ μ ∈ Z, (w - μ) ^ m μ) z := h5
  rw [h4', h5', logDeriv_inv_eq_neg _ z hdP hPne,
      logDeriv_prod_sub_pow Z m z hZz, logDeriv_prod_sub_pow P ν z hPz]
  ring

lemma circleIntegral_id_div_sub
    (c μ : ℂ) (R : ℝ) (_ : 0 < R) (hμ : μ ∈ Metric.ball c R) :
    (1 / (2 * Real.pi * Complex.I)) * (∮ z in C(c, R), z * (1 / (z - μ))) = μ := by
  have h : (∮ z in C(c, R), (z - μ)⁻¹ • z) = (2 * Real.pi * Complex.I) • μ := by
    have hf : DiffContOnCl ℂ (fun z : ℂ => z) (Metric.ball c R) :=
      Differentiable.diffContOnCl differentiable_id
    exact hf.circleIntegral_sub_inv_smul hμ
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : (fun z : ℂ => z * (1 / (z - μ))) =
    fun z => (z - μ)⁻¹ • z := by
    ext z; simp [smul_eq_mul, mul_comm]
  rw [h2, h, smul_eq_mul]
  field_simp

-- Cauchy-goursat on a Disc ---
lemma circleIntegral_eq_zero_of_holo
    (c : ℂ) (R : ℝ) (hR : 0 < R) (h : ℂ → ℂ)
    (hh : DifferentiableOn ℂ h (Metric.closedBall c R)) :
    ∮ z in C(c, R), h z = 0 := by
  have hcont : ContinuousOn h (Metric.closedBall c R) := hh.continuousOn
  have hdiff : ∀ z ∈ Metric.ball c R \ (∅ : Set ℂ), DifferentiableAt ℂ h z := by
    intro z hz
    have hzb : z ∈ Metric.ball c R := by simpa using hz
    exact hh.differentiableAt
      (mem_nhds_iff.mpr ⟨Metric.ball c R, Metric.ball_subset_closedBall, Metric.isOpen_ball, hzb⟩)
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    (s := (∅ : Set ℂ)) hR.le Set.countable_empty hcont hdiff

lemma circleIntegral_deriv_div_zero (g : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (_ : DifferentiableOn ℂ g (Metric.closedBall c R))
    (_ : ∀ z ∈ Metric.closedBall c R, g z ≠ 0)
    (hgd : DifferentiableOn ℂ (fun z => z * (deriv g z / g z)) (Metric.closedBall c R)) :
    (∮ z in C(c, R), z * (deriv g z / g z)) = 0 := by
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
    Set.countable_empty hgd.continuousOn ?_
  intro z hz
  have hzb : z ∈ Metric.ball c R := hz.1
  exact (hgd z (Metric.ball_subset_closedBall hzb)).differentiableAt
    (Metric.closedBall_mem_nhds_of_mem hzb)

lemma circleIntegrable_finset_sum' {ι : Type*}
    (s : Finset ι) (F : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (h : ∀ i ∈ s, CircleIntegrable (F i) c R) :
    CircleIntegrable (fun z => ∑ i ∈ s, F i z) c R := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact circleIntegrable_const 0 c R
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma circleIntegral_finset_sum {ι : Type*}
    (s : Finset ι) (F : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (h : ∀ i ∈ s, CircleIntegrable (F i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, F i z) = ∑ i ∈ s, ∮ z in C(c, R), F i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    simp [circleIntegral]
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, CircleIntegrable (F i) c R :=
      fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' : CircleIntegrable (F a) c R := h a (Finset.mem_insert_self a s)
    have hsum : CircleIntegrable (fun z => ∑ i ∈ s, F i z) c R :=
      circleIntegrable_finset_sum' s F c R hs
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add ha' hsum, ih hs]

lemma circleIntegral_residue_sum
    (c : ℂ) (R : ℝ) (hR : 0 < R)
    (Z P : Finset ℂ) (m ν : ℂ → ℕ)
    (hZ : ∀ μ ∈ Z, μ ∈ Metric.ball c R)
    (hP : ∀ p ∈ P, p ∈ Metric.ball c R)
    (G : ℂ → ℂ)
    (hGc : ContinuousOn G (Metric.sphere c R))
    (hI0 : (∮ z in C(c, R), G z) = 0) :
    (1 / (2 * Real.pi * Complex.I)) *
      (∮ z in C(c, R), (G z
          + ∑ μ ∈ Z, (m μ : ℂ) * (z * (1 / (z - μ)))
          - ∑ p ∈ P, (ν p : ℂ) * (z * (1 / (z - p)))))
      = ∑ μ ∈ Z, (m μ : ℂ) * μ - ∑ p ∈ P, (ν p : ℂ) * p := by
  have hcont : ∀ a ∈ Metric.ball c R,
      ContinuousOn (fun z : ℂ => z * (1 / (z - a))) (Metric.sphere c R) := by
    intro a ha
    refine continuousOn_id.mul (continuousOn_const.div (continuousOn_id.sub continuousOn_const) ?_)
    intro z hz h
    have hza : z = a := sub_eq_zero.mp h
    rw [hza] at hz
    have h1 := Metric.mem_sphere.mp hz
    have h2 := Metric.mem_ball.mp ha
    linarith
  have hintG : CircleIntegrable G c R := hGc.circleIntegrable hR.le
  have hintZ : ∀ μ ∈ Z, CircleIntegrable
      (fun z : ℂ => (m μ : ℂ) * (z * (1 / (z - μ)))) c R := fun μ hμ =>
    (continuousOn_const.mul (hcont μ (hZ μ hμ))).circleIntegrable hR.le
  have hintP : ∀ p ∈ P, CircleIntegrable
      (fun z : ℂ => (ν p : ℂ) * (z * (1 / (z - p)))) c R := fun p hp =>
    (continuousOn_const.mul (hcont p (hP p hp))).circleIntegrable hR.le
  have hintSZ : CircleIntegrable
      (fun z : ℂ => ∑ μ ∈ Z, (m μ : ℂ) * (z * (1 / (z - μ)))) c R := by
    have hc : ContinuousOn
        (fun z : ℂ => ∑ μ ∈ Z, (m μ : ℂ) * (z * (1 / (z - μ)))) (Metric.sphere c R) :=
      continuousOn_finsetSum Z (fun μ hμ =>
        (continuousOn_const (c := (m μ : ℂ))).mul (hcont μ (hZ μ hμ)))
    exact hc.circleIntegrable hR.le
  have hintSP : CircleIntegrable
      (fun z : ℂ => ∑ p ∈ P, (ν p : ℂ) * (z * (1 / (z - p)))) c R := by
    have hc : ContinuousOn
        (fun z : ℂ => ∑ p ∈ P, (ν p : ℂ) * (z * (1 / (z - p)))) (Metric.sphere c R) :=
      continuousOn_finsetSum P (fun p hp =>
        (continuousOn_const (c := (ν p : ℂ))).mul (hcont p (hP p hp)))
    exact hc.circleIntegrable hR.le
  have hsumZ : (∮ z in C(c, R), ∑ μ ∈ Z, (m μ : ℂ) * (z * (1 / (z - μ))))
      = ∑ μ ∈ Z, (m μ : ℂ) * (2 * Real.pi * Complex.I * μ) := by
    rw [circleIntegral_finset_sum Z (fun μ z => (m μ : ℂ) * (z * (1 / (z - μ)))) c R hintZ]
    refine Finset.sum_congr rfl (fun μ hμ => ?_)
    rw [circleIntegral.integral_const_mul]
    congr 1
    have h := circleIntegral_id_div_sub c μ R hR (hZ μ hμ)
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp at h ⊢
    linear_combination h
  have hsumP : (∮ z in C(c, R), ∑ p ∈ P, (ν p : ℂ) * (z * (1 / (z - p))))
      = ∑ p ∈ P, (ν p : ℂ) * (2 * Real.pi * Complex.I * p) := by
    rw [circleIntegral_finset_sum P (fun p z => (ν p : ℂ) * (z * (1 / (z - p)))) c R hintP]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [circleIntegral.integral_const_mul]
    congr 1
    have h := circleIntegral_id_div_sub c p R hR (hP p hp)
    have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    field_simp at h ⊢
    linear_combination h
  have hintGS : CircleIntegrable
      (fun z : ℂ => G z + ∑ μ ∈ Z, (m μ : ℂ) * (z * (1 / (z - μ)))) c R :=
    hintG.add hintSZ
  have hsplit : (∮ z in C(c, R), (G z
        + ∑ μ ∈ Z, (m μ : ℂ) * (z * (1 / (z - μ)))
        - ∑ p ∈ P, (ν p : ℂ) * (z * (1 / (z - p)))))
      = (∮ z in C(c, R), G z)
        + (∮ z in C(c, R), ∑ μ ∈ Z, (m μ : ℂ) * (z * (1 / (z - μ))))
        - (∮ z in C(c, R), ∑ p ∈ P, (ν p : ℂ) * (z * (1 / (z - p)))) := by
    rw [circleIntegral.integral_sub hintGS hintSP,
        circleIntegral.integral_add hintG hintSZ]
  rw [hsplit, hI0, hsumZ, hsumP, zero_add]
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have eZ : (∑ μ ∈ Z, (m μ : ℂ) * (2 * Real.pi * Complex.I * μ))
      = (2 * Real.pi * Complex.I) * ∑ μ ∈ Z, (m μ : ℂ) * μ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  have eP : (∑ p ∈ P, (ν p : ℂ) * (2 * Real.pi * Complex.I * p))
      = (2 * Real.pi * Complex.I) * ∑ p ∈ P, (ν p : ℂ) * p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [eZ, eP]
  field_simp

theorem argument_principle_meromorphic
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (Z P : Finset ℂ) (m ν : ℂ → ℕ)
    (hZ : ∀ μ ∈ Z, μ ∈ Metric.ball c R)
    (hP : ∀ p ∈ P, p ∈ Metric.ball c R)
    (g : ℂ → ℂ) (V : Set ℂ) (hV : IsOpen V) (hVb : Metric.closedBall c R ⊆ V)
    (hgV : DifferentiableOn ℂ g V)
    (hg : DifferentiableOn ℂ g (Metric.closedBall c R))
    (hgnz : ∀ z ∈ Metric.closedBall c R, g z ≠ 0)
    (U : Set ℂ) (hU : IsOpen U) (hUs : Metric.sphere c R ⊆ U)
    (hfg : ∀ z ∈ U,
      f z = g z * (∏ μ ∈ Z, (z - μ) ^ m μ) / ∏ p ∈ P, (z - p) ^ ν p) :
    (1 / (2 * Real.pi * Complex.I)) * (∮ z in C(c, R), z * (deriv f z / f z))
      = ∑ μ ∈ Z, (m μ : ℂ) * μ - ∑ p ∈ P, (ν p : ℂ) * p := by
  set G : ℂ → ℂ := fun z => z * (deriv g z / g z) with hG
  have hgan : ∀ z ∈ Metric.sphere c R, AnalyticAt ℂ g z := fun z hz =>
    (hgV.analyticOnNhd hV) z (hVb (Metric.sphere_subset_closedBall hz))
  have hsphere : ∀ z ∈ Metric.sphere c R,
      z * (deriv f z / f z)
        = z * (deriv g z / g z) + ∑ μ ∈ Z, (m μ : ℂ) * (z * (1 / (z - μ)))
          - ∑ p ∈ P, (ν p : ℂ) * (z * (1 / (z - p))) := by
    intro z hz
    have hzb : z ∈ Metric.closedBall c R := Metric.sphere_subset_closedBall hz
    have hZz : ∀ μ ∈ Z, z ≠ μ := by
      intro μ hμ h
      have := hZ μ hμ
      rw [← h] at this
      simp [Metric.mem_ball, Metric.mem_sphere.mp hz] at this
    have hPz : ∀ p ∈ P, z ≠ p := by
      intro p hp h
      have := hP p hp
      rw [← h] at this
      simp [Metric.mem_ball, Metric.mem_sphere.mp hz] at this
    have hev : f =ᶠ[nhds z] fun w =>
        g w * (∏ μ ∈ Z, (w - μ) ^ m μ) / ∏ p ∈ P, (w - p) ^ ν p :=
      Filter.eventually_of_mem (hU.mem_nhds (hUs hz)) hfg
    have hlog : logDeriv f z = logDeriv (fun w =>
        g w * (∏ μ ∈ Z, (w - μ) ^ m μ) / ∏ p ∈ P, (w - p) ^ ν p) z := by
      simp only [logDeriv_apply, hev.deriv_eq, hev.self_of_nhds]
    have hfac := logDeriv_factorisation g Z P m ν z (hgan z hz) (hgnz z hzb) hZz hPz
    rw [← logDeriv_apply, hlog, hfac]
    simp only [mul_add, mul_sub, Finset.mul_sum, logDeriv_apply]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      ring
    · refine Finset.sum_congr rfl (fun p _ => ?_)
      ring
  have hint : (∮ z in C(c, R), z * (deriv f z / f z))
      = ∮ z in C(c, R), (z * (deriv g z / g z)
          + ∑ μ ∈ Z, (m μ : ℂ) * (z * (1 / (z - μ)))
          - ∑ p ∈ P, (ν p : ℂ) * (z * (1 / (z - p)))) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    exact hsphere z hz
  have hgd : DifferentiableOn ℂ G (Metric.closedBall c R) := by
    have han : AnalyticOnNhd ℂ g V := hgV.analyticOnNhd hV
    have hder : AnalyticOnNhd ℂ (deriv g) V := han.deriv
    intro z hz
    have hzV := hVb hz
    have h1 : DifferentiableAt ℂ g z := (han z hzV).differentiableAt
    have h2 : DifferentiableAt ℂ (deriv g) z := (hder z hzV).differentiableAt
    exact (differentiableAt_id.mul (h2.div h1 (hgnz z hz))).differentiableWithinAt
  have hI0 : (∮ z in C(c, R), G z) = 0 :=
    circleIntegral_deriv_div_zero g c R hR hg hgnz hgd
  have hGc : ContinuousOn G (Metric.sphere c R) :=
    hgd.continuousOn.mono Metric.sphere_subset_closedBall
  rw [hint]
  exact circleIntegral_residue_sum c R hR Z P m ν hZ hP G hGc hI0


------------------------------------------------------------------


lemma norm_deriv_circleMap {c : ℂ} {R : ℝ} (hR : 0 < R) (θ : ℝ) :
    ‖deriv (circleMap c R) θ‖ = R := by
  rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one]
  rw [norm_circleMap_zero, abs_of_pos hR]

lemma norm_integrand_circle_le {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ} {M : ℝ}
    (hg : ∀ z ∈ Metric.sphere c R, ‖g z‖ ≤ M) (θ : ℝ) :
    ‖deriv (circleMap c R) θ • g (circleMap c R θ)‖ ≤ R * M := by
  rw [norm_smul, norm_deriv_circleMap hR]
  exact mul_le_mul_of_nonneg_left (hg _ (circleMap_mem_sphere c hR.le θ)) hR.le

lemma continuous_integrand_circle {c : ℂ} {R : ℝ} (hR : 0 < R) {g : ℂ → ℂ}
    (hg : ContinuousOn g (Metric.sphere c R)) :
    Continuous (fun θ : ℝ => deriv (circleMap c R) θ • g (circleMap c R θ)) := by
  have hc : Continuous (fun θ : ℝ => circleMap c R θ) := continuous_circleMap c R
  have hcont : Continuous (fun θ : ℝ => g (circleMap c R θ)) :=
    hg.comp_continuous hc (fun θ => circleMap_mem_sphere c hR.le θ)
  have hd : Continuous (fun θ : ℝ => deriv (circleMap c R) θ) := by
    simp only [deriv_circleMap]
    fun_prop
  exact hd.smul hcont

lemma circleIntegral_tendsto_of_tendstoUniformlyOn
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : ∀ N, ContinuousOn (F N) (Metric.sphere c R))
    (hf : ContinuousOn f (Metric.sphere c R))
    (hconv : TendstoUniformlyOn F f Filter.atTop (Metric.sphere c R)) :
    Filter.Tendsto (fun N => ∮ z in C(c, R), F N z) Filter.atTop
      (nhds (∮ z in C(c, R), f z)) := by
  have hcomp : IsCompact (Metric.sphere c R) := isCompact_sphere c R
  obtain ⟨Mf, hMf⟩ := hcomp.exists_bound_of_continuousOn hf
  have hev : ∀ᶠ N in Filter.atTop, ∀ z ∈ Metric.sphere c R, ‖F N z - f z‖ < 1 := by
    have := (Metric.tendstoUniformlyOn_iff.mp hconv) 1 one_pos
    filter_upwards [this] with N hN z hz
    rw [← dist_eq_norm, dist_comm]
    exact hN z hz
  have hbd : ∀ᶠ N in Filter.atTop, ∀ z ∈ Metric.sphere c R, ‖F N z‖ ≤ Mf + 1 := by
    filter_upwards [hev] with N hN z hz
    have h1 := hN z hz
    have h2 := hMf z hz
    calc ‖F N z‖ = ‖(F N z - f z) + f z‖ := by ring_nf
      _ ≤ ‖F N z - f z‖ + ‖f z‖ := norm_add_le _ _
      _ ≤ Mf + 1 := by linarith
  unfold circleIntegral
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ => R * (Mf + 1))
  · refine Filter.Eventually.of_forall (fun N => ?_)
    exact (continuous_integrand_circle hR (hF N)).aestronglyMeasurable
  · filter_upwards [hbd] with N hN
    refine Filter.Eventually.of_forall (fun θ _ => ?_)
    exact norm_integrand_circle_le hR hN θ
  · exact intervalIntegrable_const
  · refine Filter.Eventually.of_forall (fun θ _ => ?_)
    exact (hconv.tendsto_at (circleMap_mem_sphere c hR.le θ)).const_smul _

lemma tendstoUniformlyOn_of_locallyUniformlyOn_compact
    {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {U K : Set ℂ} (hU : IsOpen U)
    (h : TendstoLocallyUniformlyOn F f Filter.atTop U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn F f Filter.atTop K :=
  (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp h K hKU hK

lemma tendstoUniformlyOn_comp_add_half
    {G : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {S : Set ℂ}
    (h : TendstoUniformlyOn G g Filter.atTop ((fun z => 1 / 2 + z) '' S)) :
    TendstoUniformlyOn (fun N z => G N (1 / 2 + z)) (fun z => g (1 / 2 + z))
      Filter.atTop S := by
  intro u hu
  filter_upwards [h u hu] with N hN z hz
  exact hN _ ⟨z, hz, rfl⟩

lemma isCompact_image_add_half_sphere (c : ℂ) (R : ℝ) :
    IsCompact ((fun z : ℂ => 1 / 2 + z) '' Metric.sphere c R) :=
  (isCompact_sphere c R).image (continuous_const.add continuous_id)


lemma exists_pos_le_norm_of_compact {g : ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hg : ContinuousOn g K) (hne : ∀ z ∈ K, g z ≠ 0) :
    ∃ m > 0, ∀ z ∈ K, m ≤ ‖g z‖ := by
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨z0, hz0, hmin⟩ := hK.exists_isMinOn hKne hg.norm
  exact ⟨‖g z0‖, norm_pos_iff.mpr (hne z0 hz0), fun z hz => hmin hz⟩


lemma eventually_half_le_norm {b : ℕ → ℂ → ℂ} {b0 : ℂ → ℂ} {K : Set ℂ} {m : ℝ}
    (hm : 0 < m) (hb : TendstoUniformlyOn b b0 Filter.atTop K)
    (hlow : ∀ z ∈ K, m ≤ ‖b0 z‖) :
    ∀ᶠ N in Filter.atTop, ∀ z ∈ K, m / 2 ≤ ‖b N z‖ := by
  have := (Metric.tendstoUniformlyOn_iff.mp hb) (m / 2) (by positivity)
  filter_upwards [this] with N hN z hz
  have h1 : dist (b0 z) (b N z) < m / 2 := hN z hz
  have h2 : ‖b0 z‖ - ‖b N z‖ ≤ ‖b0 z - b N z‖ := norm_sub_norm_le _ _
  rw [← dist_eq_norm] at h2
  linarith [hlow z hz]

lemma norm_div_sub_div_le {a a0 b b0 : ℂ} {A m : ℝ} (hm : 0 < m)
    (hA : ‖a0‖ ≤ A) (hb0 : m ≤ ‖b0‖) (hb : m / 2 ≤ ‖b‖) :
    ‖a0 / b0 - a / b‖ ≤ ‖a0 - a‖ * (2 / m) + A * ‖b0 - b‖ * (2 / m ^ 2) := by
  have hb_pos : 0 < ‖b‖ := lt_of_lt_of_le (by positivity) hb
  have hb0_pos : 0 < ‖b0‖ := lt_of_lt_of_le hm hb0
  have hbne : b ≠ 0 := norm_pos_iff.mp hb_pos
  have hb0ne : b0 ≠ 0 := norm_pos_iff.mp hb0_pos
  have key : a0 / b0 - a / b = (a0 - a) / b + a0 * (b - b0) / (b * b0) := by
    field_simp
    ring
  rw [key]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_div]
    rw [div_eq_mul_inv]
    have : ‖b‖⁻¹ ≤ 2 / m := by
      have h2m : 0 < m / 2 := by positivity
      calc ‖b‖⁻¹ ≤ (m / 2)⁻¹ := inv_anti₀ h2m hb
        _ = 2 / m := by field_simp
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  · rw [norm_div, norm_mul, norm_mul, norm_sub_rev b b0]
    have hden : 0 < ‖b‖ * ‖b0‖ := mul_pos hb_pos hb0_pos
    rw [div_le_iff₀ hden]
    have hnn : 0 ≤ ‖b0 - b‖ := norm_nonneg _
    have hA0 : 0 ≤ A := (norm_nonneg _).trans hA
    have h1 : m * (m / 2) ≤ ‖b‖ * ‖b0‖ := by
      calc m * (m / 2) = (m / 2) * m := by ring
        _ ≤ ‖b‖ * ‖b0‖ := mul_le_mul hb hb0 hm.le (norm_nonneg _)
    calc ‖a0‖ * ‖b0 - b‖ ≤ A * ‖b0 - b‖ := mul_le_mul_of_nonneg_right hA hnn
      _ = (A * ‖b0 - b‖ * (2 / m ^ 2)) * (m * (m / 2)) := by field_simp
      _ ≤ (A * ‖b0 - b‖ * (2 / m ^ 2)) * (‖b‖ * ‖b0‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)

lemma tendstoUniformlyOn_div {a b : ℕ → ℂ → ℂ} {a0 b0 : ℂ → ℂ} {K : Set ℂ}
    {A m : ℝ} (hm : 0 < m)
    (ha : TendstoUniformlyOn a a0 Filter.atTop K)
    (hb : TendstoUniformlyOn b b0 Filter.atTop K)
    (hA : ∀ z ∈ K, ‖a0 z‖ ≤ A)
    (hlow : ∀ z ∈ K, m ≤ ‖b0 z‖)
    (hlowN : ∀ᶠ N in Filter.atTop, ∀ z ∈ K, m / 2 ≤ ‖b N z‖) :
    TendstoUniformlyOn (fun N z => a N z / b N z) (fun z => a0 z / b0 z)
      Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at *
  intro ε hε
  have hA'0 : 0 ≤ max A 0 := le_max_right _ _
  have hAA' : ∀ z ∈ K, ‖a0 z‖ ≤ max A 0 := fun z hz => (hA z hz).trans (le_max_left _ _)
  have hδ1 : 0 < ε * m / 8 := by positivity
  have hδ2 : 0 < ε * m ^ 2 / (8 * (max A 0 + 1)) := by positivity
  filter_upwards [ha _ hδ1, hb _ hδ2, hlowN] with N hNa hNb hNlow z hz
  have h1 := hNa z hz
  have h2 := hNb z hz
  rw [dist_eq_norm] at *
  have hest := norm_div_sub_div_le (a := a N z) (a0 := a0 z) (b := b N z) (b0 := b0 z)
    hm (hAA' z hz) (hlow z hz) (hNlow z hz)
  have t1 : ‖a0 z - a N z‖ * (2 / m) ≤ ε / 4 := by
    calc ‖a0 z - a N z‖ * (2 / m) ≤ (ε * m / 8) * (2 / m) :=
          mul_le_mul_of_nonneg_right h1.le (by positivity)
      _ = ε / 4 := by field_simp; ring
  have t2 : max A 0 * ‖b0 z - b N z‖ * (2 / m ^ 2) ≤ ε / 4 := by
    have hb' : ‖b0 z - b N z‖ ≤ ε * m ^ 2 / (8 * (max A 0 + 1)) := h2.le
    calc max A 0 * ‖b0 z - b N z‖ * (2 / m ^ 2)
        ≤ max A 0 * (ε * m ^ 2 / (8 * (max A 0 + 1))) * (2 / m ^ 2) := by
          gcongr
      _ = ε / 4 * (max A 0 / (max A 0 + 1)) := by field_simp; ring
      _ ≤ ε / 4 := by
          have : max A 0 / (max A 0 + 1) ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          nlinarith [this, hε]
  calc ‖a0 z / b0 z - a N z / b N z‖ ≤ ‖a0 z - a N z‖ * (2 / m)
        + max A 0 * ‖b0 z - b N z‖ * (2 / m ^ 2) := hest
    _ ≤ ε / 4 + ε / 4 := add_le_add t1 t2
    _ < ε := by linarith

lemma tendstoUniformlyOn_mul_left_of_bdd {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {K : Set ℂ}
    {B : ℝ} (hF : TendstoUniformlyOn F f Filter.atTop K) (hB : ∀ z ∈ K, ‖z‖ ≤ B) :
    TendstoUniformlyOn (fun N z => z * F N z) (fun z => z * f z) Filter.atTop K := by
  rw [Metric.tendstoUniformlyOn_iff] at *
  intro ε hε
  have hB0 : 0 < max B 1 := lt_max_of_lt_right one_pos
  filter_upwards [hF (ε / (2 * max B 1)) (by positivity)] with N hN z hz
  have h1 := hN z hz
  rw [dist_eq_norm] at *
  calc ‖z * f z - z * F N z‖ = ‖z‖ * ‖f z - F N z‖ := by rw [← mul_sub, norm_mul]
    _ ≤ max B 1 * (ε / (2 * max B 1)) := by
        apply mul_le_mul (le_trans (hB z hz) (le_max_left _ _)) h1.le (norm_nonneg _) hB0.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

open Real MeasureTheory intervalIntegral

lemma conj_circleIntegral (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (starRingEnd ℂ) (∮ z in C(c, R), f z)
      = - ∮ w in C((starRingEnd ℂ) c, R), (starRingEnd ℂ) (f ((starRingEnd ℂ) w)) := by
  unfold circleIntegral
  have hconj : ∀ g : ℝ → ℂ,
      (starRingEnd ℂ) (∫ θ in (0:ℝ)..2 * π, g θ)
        = ∫ θ in (0:ℝ)..2 * π, (starRingEnd ℂ) (g θ) := by
    intro g
    rw [intervalIntegral.integral_of_le (by positivity),
      intervalIntegral.integral_of_le (by positivity)]
    exact integral_conj.symm
  rw [hconj]
  have hmap : ∀ θ : ℝ, (starRingEnd ℂ) (circleMap c R θ)
      = circleMap ((starRingEnd ℂ) c) R (-θ) := by
    intro θ
    simp [circleMap, map_add, map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
  have hderiv : ∀ θ : ℝ, (starRingEnd ℂ) (deriv (circleMap c R) θ)
      = - deriv (circleMap ((starRingEnd ℂ) c) R) (-θ) := by
    intro θ
    simp [deriv_circleMap, circleMap, map_mul, ← Complex.exp_conj, Complex.conj_ofReal]
  have hint : ∀ θ : ℝ,
      (starRingEnd ℂ) (deriv (circleMap c R) θ • f (circleMap c R θ))
      = - (deriv (circleMap ((starRingEnd ℂ) c) R) (-θ)
          • (starRingEnd ℂ) (f ((starRingEnd ℂ) (circleMap ((starRingEnd ℂ) c) R (-θ))))) := by
    intro θ
    rw [smul_eq_mul, map_mul, hderiv, ← hmap, Complex.conj_conj]
    simp [smul_eq_mul, neg_mul]
  simp_rw [hint]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_neg
    (fun θ => deriv (circleMap ((starRingEnd ℂ) c) R) θ
      • (starRingEnd ℂ) (f ((starRingEnd ℂ) (circleMap ((starRingEnd ℂ) c) R θ))))]
  rw [neg_zero]
  congr 1
  have hper : Function.Periodic (fun θ : ℝ => deriv (circleMap ((starRingEnd ℂ) c) R) θ
      • (starRingEnd ℂ) (f ((starRingEnd ℂ) (circleMap ((starRingEnd ℂ) c) R θ))))
      (2 * π) := by
    intro θ
    simp [deriv_circleMap, periodic_circleMap _ _ θ]
  simpa using hper.intervalIntegral_add_eq (-(2 * π)) 0


----------------------------------------------------------------------

lemma circleIntegral_logDeriv_noZero
    {f h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (hne : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (S : Finset ℂ) (hS : ∀ z, z ∈ S ↔ z ∈ Metric.ball c R ∧ f z = 0)
    (hcard : S.card = 0) :
    (1 / (2 * ↑Real.pi * I)) * ∮ z in C(c, R), h z * (deriv f z / f z)
      = ∑ a ∈ S, ((analyticOrderAt f a).toNat : ℂ) * h a := by
  have hS0 : S = ∅ := Finset.card_eq_zero.mp hcard
  have hnz : ∀ z ∈ Metric.closedBall c R, f z ≠ 0 := by
    intro z hz
    rcases (Metric.mem_closedBall.mp hz).lt_or_eq with hlt | heq
    · intro h0
      have : z ∈ S := (hS z).mpr ⟨Metric.mem_ball.mpr hlt, h0⟩
      simp [hS0] at this
    · exact hne z (Metric.mem_sphere.mpr heq)
  have hdiff : DifferentiableOn ℂ
    (fun z => h z * (deriv f z / f z)) (Metric.closedBall c R) := by
    intro z hz
    have hfz : f z ≠ 0 := hnz z hz
    have hderiv : Differentiable ℂ (deriv f) := hf.deriv
    exact ((hh.differentiableAt.mul (hderiv.differentiableAt.div
      (hf.differentiableAt) hfz)).differentiableWithinAt)
  have hint : ∮ z in C(c, R), h z * (deriv f z / f z) = 0 := by
    have hne_R : 0 < R := hR
    have hdiff' : DifferentiableOn ℂ (fun z => h z * (deriv f z / f z))
        (closure (Metric.ball c R)) := by
      rw [closure_ball c hne_R.ne']
      exact hdiff
    exact (DifferentiableOn.diffContOnCl hdiff').circleIntegral_eq_zero hne_R.le
  rw [hint, hS0]
  simp

-- Cauchy formula ---
lemma cauchy_kernel {h : ℂ → ℂ} {c a : ℂ} {R : ℝ}
    (hh : Differentiable ℂ h) (ha : a ∈ Metric.ball c R) :
    ∮ z in C(c, R), h z / (z - a) = 2 * ↑Real.pi * I * h a := by
  have key := (hh.diffContOnCl (s := Metric.ball c R)).circleIntegral_sub_inv_smul ha
  simpa [smul_eq_mul, div_eq_inv_mul, mul_comm] using key

lemma order_eq_of_ne {f g : ℂ → ℂ} {a b : ℂ} {m : ℕ}
    (hg : AnalyticAt ℂ g b) (hfg : ∀ z, f z = (z - a) ^ m * g z) (hba : b ≠ a) :
    analyticOrderAt f b = analyticOrderAt g b := by
  have hfeq : f = (fun z => (z - a) ^ m) * g := funext hfg
  have hpow : AnalyticAt ℂ (fun z => (z - a) ^ m) b :=
    ((analyticAt_id.sub analyticAt_const).pow m)
  have hord : analyticOrderAt (fun z => (z - a) ^ m) b = 0 :=
    (hpow.analyticOrderAt_eq_zero).mpr (pow_ne_zero _ (sub_ne_zero.mpr hba))
  rw [hfeq, analyticOrderAt_mul hpow hg, hord, zero_add]

lemma circleIntegral_const_mul_add {u v : ℂ → ℂ} {c : ℂ} {R : ℝ} (m : ℂ)
    (hu : CircleIntegrable u c R) (hv : CircleIntegrable v c R) :
    (∮ z in C(c, R), (m * u z + v z))
      = m * (∮ z in C(c, R), u z) + (∮ z in C(c, R), v z) := by
  have hmu : CircleIntegrable (fun z => m * u z) c R := by
    unfold CircleIntegrable at *
    exact hu.const_mul m
  rw [circleIntegral.integral_add hmu hv, circleIntegral.integral_const_mul]

lemma sum_order_split {f g h : ℂ → ℂ} {a : ℂ} {m : ℕ} {S : Finset ℂ}
    (ha : a ∈ S) (hg : Differentiable ℂ g)
    (hfg : ∀ z, f z = (z - a) ^ m * g z)
    (hm : (m : ℕ∞) = analyticOrderAt f a) :
    ∑ b ∈ S, ((analyticOrderAt f b).toNat : ℂ) * h b
      = (m : ℂ) * h a + ∑ b ∈ S.erase a, ((analyticOrderAt g b).toNat : ℂ) * h b := by
  rw [← Finset.add_sum_erase S _ ha]
  congr 1
  · rw [← hm]
    simp
  · refine Finset.sum_congr rfl fun b hb => ?_
    rw [order_eq_of_ne (hg.analyticAt b) hfg (Finset.ne_of_mem_erase hb)]

lemma final_algebra {K L T ha : ℂ} (m : ℂ)
    (_ : (2 * ↑Real.pi * I : ℂ) ≠ 0)
    (hK : K = 2 * ↑Real.pi * I * ha)
    (hL : 1 / (2 * ↑Real.pi * I) * L = T) :
    1 / (2 * ↑Real.pi * I) * (m * K + L) = m * ha + T := by
  rw [← hL, hK]
  field_simp

lemma exists_mem_of_card_succ {α : Type*} {S : Finset α} {n : ℕ}
    (hcard : S.card = n + 1) : ∃ a, a ∈ S := by
  have : S.Nonempty := Finset.card_pos.mp (by omega)
  exact this


lemma analyticOrderAt_ne_top_of_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hf0 : ∃ z, f z ≠ 0) (a : ℂ) : analyticOrderAt f a ≠ ⊤ := by
  obtain ⟨z₀, hz₀⟩ := hf0
  have hAnOn : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hz₀_ord : analyticOrderAt f z₀ ≠ ⊤ := by
    have h0 : analyticOrderAt f z₀ = 0 :=
      (hf.analyticAt z₀).analyticOrderAt_eq_zero.mpr hz₀
    rw [h0]
    exact ENat.natCast_ne_top 0
  exact hAnOn.analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ z₀) (Set.mem_univ a) hz₀_ord

lemma local_factorization {f : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hAn : AnalyticAt ℂ f a) (hm : analyticOrderAt f a = m) :
    ∃ g₀ : ℂ → ℂ, AnalyticAt ℂ g₀ a ∧ g₀ a ≠ 0 ∧
      f =ᶠ[nhds a] fun z => (z - a) ^ m • g₀ z :=
  (hAn.analyticOrderAt_eq_natCast (n := m)).mp hm

lemma global_factor {f g₀ : ℂ → ℂ} {a : ℂ} {m : ℕ}
    (hf : Differentiable ℂ f) (hg₀ : AnalyticAt ℂ g₀ a)
    (hev : f =ᶠ[nhds a] fun z => (z - a) ^ m • g₀ z) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ (∀ z, f z = (z - a) ^ m * g z) ∧ g a = g₀ a := by
  classical
  refine ⟨fun z => if z = a then g₀ a else f z / (z - a) ^ m, ?_, ?_, by simp⟩
  · intro z
    by_cases hz : z = a
    · subst hz
      have hEq : (fun w => if w = z then g₀ z else f w / (w - z) ^ m) =ᶠ[nhds z] g₀ := by
        filter_upwards [hev] with w hw
        by_cases hwz : w = z
        · simp [hwz]
        · simp only [hwz, ite_false, hw, smul_eq_mul]
          field_simp [sub_ne_zero.mpr hwz]
      exact (hg₀.differentiableAt.congr_of_eventuallyEq hEq)
    · have hEq : (fun w => if w = a then g₀ a else f w / (w - a) ^ m)
          =ᶠ[nhds z] fun w => f w / (w - a) ^ m := by
        filter_upwards [isOpen_ne.mem_nhds hz] with w hw
        simp [hw]
      refine DifferentiableAt.congr_of_eventuallyEq ?_ hEq
      exact (hf z).div ((differentiableAt_id.sub_const a).pow m)
        (pow_ne_zero _ (sub_ne_zero.mpr hz))
  · intro z
    by_cases hz : z = a
    · subst hz
      have := hev.self_of_nhds
      simpa [smul_eq_mul] using this
    · simp only [hz, ite_false]
      field_simp [sub_ne_zero.mpr hz]


lemma factor_ne_zero_on_sphere {f g : ℂ → ℂ} {a c : ℂ} {R : ℝ} {m : ℕ}
    (hfg : ∀ z, f z = (z - a) ^ m * g z)
    (hne : ∀ z ∈ Metric.sphere c R, f z ≠ 0) :
    ∀ z ∈ Metric.sphere c R, g z ≠ 0 := by
  intro z hz hgz
  exact hne z hz (by rw [hfg z, hgz, mul_zero])

lemma zeros_of_factor {f g : ℂ → ℂ} {a c : ℂ} {R : ℝ} {m : ℕ} {S : Finset ℂ}
    (hS : ∀ z, z ∈ S ↔ z ∈ Metric.ball c R ∧ f z = 0)
    (hfg : ∀ z, f z = (z - a) ^ m * g z) (hga : g a ≠ 0) :
    ∀ z, z ∈ S.erase a ↔ z ∈ Metric.ball c R ∧ g z = 0 := by
  intro z
  rw [Finset.mem_erase, hS z]
  constructor
  · rintro ⟨hza, hzb, hfz⟩
    refine ⟨hzb, ?_⟩
    rw [hfg z] at hfz
    exact (mul_eq_zero.mp hfz).resolve_left (pow_ne_zero _ (sub_ne_zero.mpr hza))
  · rintro ⟨hzb, hgz⟩
    refine ⟨?_, hzb, by rw [hfg z, hgz, mul_zero]⟩
    rintro rfl
    exact hga hgz


lemma logDeriv_factor' {f g : ℂ → ℂ} {a z : ℂ} {m : ℕ}
    (hg : Differentiable ℂ g) (hfg : ∀ w, f w = (w - a) ^ m * g w)
    (hza : z ≠ a) (hgz : g z ≠ 0) :
    deriv f z / f z = (m : ℂ) / (z - a) + deriv g z / g z := by
  have hfeq : f = fun w => (w - a) ^ m * g w := funext hfg
  have hsub : z - a ≠ 0 := sub_ne_zero.mpr hza
  have hd : deriv f z = m * (z - a) ^ (m - 1) * g z + (z - a) ^ m * deriv g z := by
    rw [hfeq]
    have h1 : HasDerivAt (fun w => (w - a) ^ m) (m * (z - a) ^ (m - 1)) z := by
      have h0 : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
      have hp : HasDerivAt (fun u : ℂ => u ^ m)
        ((m : ℂ) * (z - a) ^ (m - 1)) (z - a) :=
        hasDerivAt_pow m (z - a)
      have := hp.comp z h0
      simpa [Function.comp_def] using this
    exact (h1.mul (hg z).hasDerivAt).deriv
  rw [hd, hfg z]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp;
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring


lemma circleIntegral_logDeriv_succ
    (n : ℕ) {f h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (hne : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (S : Finset ℂ) (hS : ∀ z, z ∈ S ↔ z ∈ Metric.ball c R ∧ f z = 0)
    (hf0 : ∃ z, f z ≠ 0) (hcard : S.card = n + 1)
    (ih : ∀ (f : ℂ → ℂ), Differentiable ℂ f →
      (∀ z ∈ Metric.sphere c R, f z ≠ 0) → (∃ z, f z ≠ 0) →
      ∀ S : Finset ℂ, (∀ z, z ∈ S ↔ z ∈ Metric.ball c R ∧ f z = 0) → S.card = n →
      (1 / (2 * ↑Real.pi * I)) * (∮ z in C(c, R), h z * (deriv f z / f z))
        = ∑ a ∈ S, ((analyticOrderAt f a).toNat : ℂ) * h a) :
    (1 / (2 * ↑Real.pi * I)) * (∮ z in C(c, R), h z * (deriv f z / f z))
      = ∑ a ∈ S, ((analyticOrderAt f a).toNat : ℂ) * h a := by
  obtain ⟨a, ha⟩ := exists_mem_of_card_succ hcard
  have ha' := (hS a).mp ha
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (analyticOrderAt_ne_top_of_entire hf hf0 a)
  obtain ⟨g₀, hg₀an, hg₀a, hev⟩ := local_factorization (hf.analyticAt a) hm.symm
  obtain ⟨g, hg, hfg, hga₀⟩ := global_factor hf hg₀an hev
  have hga : g a ≠ 0 := by rw [hga₀]; exact hg₀a
  have hg_ne := factor_ne_zero_on_sphere hfg hne
  have hS' := zeros_of_factor hS hfg hga
  have hcard' : (S.erase a).card = n := by
    rw [Finset.card_erase_of_mem ha]; omega
  have hIH := ih g hg hg_ne ⟨a, hga⟩ (S.erase a) hS' hcard'
  have hlog : ∀ z ∈ Metric.sphere c R,
      h z * (deriv f z / f z)
        = (m : ℂ) * (h z / (z - a)) + h z * (deriv g z / g z) := by
    intro z hz
    have hza : z ≠ a := by
      rintro rfl
      have := Metric.mem_ball.mp ha'.1
      have := Metric.mem_sphere.mp hz
      linarith
    rw [logDeriv_factor' hg hfg hza (hg_ne z hz)]
    ring
  have hcont_ne : ∀ z ∈ Metric.sphere c R, z - a ≠ 0 := by
    intro z hz hza
    have hza' : z = a := sub_eq_zero.mp hza
    subst hza'
    have := Metric.mem_ball.mp ha'.1
    have := Metric.mem_sphere.mp hz
    linarith
  have hint1 : CircleIntegrable (fun z => h z / (z - a)) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact hh.continuous.continuousOn.div
      (continuous_id.sub continuous_const).continuousOn hcont_ne
  have hint2 : CircleIntegrable (fun z => h z * (deriv g z / g z)) c R := by
    apply ContinuousOn.circleIntegrable hR.le
    have hderiv : Continuous (deriv g) := (hg.contDiff (n := 1)).continuous_deriv le_rfl
    exact hh.continuous.continuousOn.mul
      (hderiv.continuousOn.div hg.continuous.continuousOn hg_ne)
  have hsplit : (∮ z in C(c, R), h z * (deriv f z / f z))
      = (m : ℂ) * (∮ z in C(c, R), h z / (z - a))
        + (∮ z in C(c, R), h z * (deriv g z / g z)) := by
    rw [circleIntegral.integral_congr hR.le hlog]
    exact circleIntegral_const_mul_add (m : ℂ) hint1 hint2
  have hsum := sum_order_split (h := h) ha hg hfg hm
  have h2pi : (2 * ↑Real.pi * I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have hK : (∮ z in C(c, R), h z / (z - a)) = 2 * ↑Real.pi * I * h a :=
    cauchy_kernel hh ha'.1
  rw [hsum, hsplit]
  exact final_algebra (m : ℂ) h2pi hK hIH

lemma argument_principle_circle
    {f h : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : Differentiable ℂ f) (hh : Differentiable ℂ h)
    (hne : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (S : Finset ℂ) (hS : ∀ z, z ∈ S ↔ z ∈ Metric.ball c R ∧ f z = 0) :
    (1 / (2 * ↑Real.pi * I)) * ∮ z in C(c, R), h z * (deriv f z / f z)
      = ∑ a ∈ S, ((analyticOrderAt f a).toNat : ℂ) * h a := by
  have H : ∀ (n : ℕ) (f : ℂ → ℂ), Differentiable ℂ f →
      (∀ z ∈ Metric.sphere c R, f z ≠ 0) → (∃ z, f z ≠ 0) →
      ∀ S : Finset ℂ, (∀ z, z ∈ S ↔ z ∈ Metric.ball c R ∧ f z = 0) → S.card = n →
      (1 / (2 * ↑Real.pi * I)) * ∮ z in C(c, R), h z * (deriv f z / f z)
        = ∑ a ∈ S, ((analyticOrderAt f a).toNat : ℂ) * h a := by
    intro n
    induction n with
    | zero =>
        intro f hf hne hf0 S hS hcard
        exact circleIntegral_logDeriv_noZero hR hf hh hne S hS hcard
    | succ n ih =>
        intro f hf hne hf0 S hS hcard
        exact circleIntegral_logDeriv_succ n hR hf hh hne S hS hf0 hcard ih
  have hf0 : ∃ z, f z ≠ 0 := ⟨c + R, hne _ (by simp [abs_of_pos hR])⟩
  exact H S.card f hf hne hf0 S hS rfl

lemma circleIntegral_rewrite_deriv {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hderiv : ∀ z, deriv (fun w => F (1 / 2 + w)) z = deriv F (1 / 2 + z)) :
    (∮ z in C(c, R), z * (deriv (fun w => F (1 / 2 + w)) z / F (1 / 2 + z)))
      = ∮ z in C(c, R), z * (deriv F (1 / 2 + z) / F (1 / 2 + z)) := by
  congr 1
  funext z
  rw [hderiv z]

-----------------------------------------------------------------------

theorem integrale_reparametrisee_eq
    (F : ℂ → ℂ) (g : ℝ → ℂ) (θ θ' : ℝ → ℝ)
    (hθ : ∀ x ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt θ (θ' x) x)
    (hθc : ContinuousOn θ' (Set.uIcc 0 1))
    (hg : ContinuousOn (fun t => F (g t) * deriv g t) (θ '' Set.uIcc 0 1))
    (h0 : θ 0 = 0) (h1 : θ 1 = 1) :
    ∫ t in (0:ℝ)..1, F (g (θ t)) * deriv g (θ t) * (θ' t : ℂ)
      = ∫ t in (0:ℝ)..1, F (g t) * deriv g t := by
  set G : ℝ → ℂ := fun t => F (g t) * deriv g t with hG
  have h := intervalIntegral.integral_deriv_smul_comp' hθ hθc hg
  rw [h0, h1] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [hG, Function.comp, Complex.real_smul]
  ring

theorem circleIntegral_translation (F : ℂ → ℂ) (c d : ℂ) (R : ℝ) :
    ∮ w in C(c + d, R), F w = ∮ z in C(c, R), F (z + d) := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [circleMap, deriv_circleMap]
  have : c + d + ↑R * Complex.exp (↑θ * Complex.I)
      = c + ↑R * Complex.exp (↑θ * Complex.I) + d := by ring
  rw [this]

theorem circleIntegral_translation_aux (F : ℂ → ℂ) (c d : ℂ) (R : ℝ) :
    ∮ w in C(c + d, R), F w = ∮ z in C(c, R), F (z + d) := by
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [circleMap, deriv_circleMap]
  have h : c + d + ↑R * Complex.exp (↑θ * Complex.I)
      = c + ↑R * Complex.exp (↑θ * Complex.I) + d := by ring
  rw [h]

open RiemannDef

theorem circleIntegrable_translation_integrand
    (zm : ℂ) (ε : ℝ) (d : ℂ)
    (hA : CircleIntegrable
      (fun z => (z + d) *
        (deriv xiDecale (z + d) / xiDecale (z + d))) zm ε)
    (hB : CircleIntegrable
      (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε) :
    CircleIntegrable
      (fun z =>
        ((z + d) * (deriv xiDecale (z + d) / xiDecale (z + d))
          - z * (deriv xiDecale z / xiDecale z))) zm ε := by
  exact hA.sub hB

theorem translation_bijHolPresOrient (c d : ℂ) (ε : ℝ) :
    BijHolPresOrient c (c + d) ε (fun z => z + d) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (differentiable_id.add_const d).differentiableOn
  · refine ⟨?_, ?_, ?_⟩
    · intro z hz
      simpa [Metric.mem_sphere, dist_eq_norm] using hz
    · intro a _ b _ h
      simpa using h
    · intro w hw
      refine ⟨w - d, ?_, by ring⟩
      rw [Metric.mem_sphere, dist_eq_norm] at hw ⊢
      have e : w - d - c = w - (c + d) := by ring
      rw [e]
      exact hw
  · intro G
    have hd : ∀ z : ℂ, deriv (fun z : ℂ => z + d) z = 1 := by
      intro z; simp
    simp_rw [hd, mul_one]
    exact circleIntegral_translation_aux G c d ε

theorem circleIntegrable_const_mul_congr {g h : ℂ → ℂ} {c : ℂ} {ε : ℝ} (a : ℂ)
    (hg : CircleIntegrable g c ε) (hgh : ∀ z, h z = a * g z) :
    CircleIntegrable h c ε := by
  have e : h = fun z => a * g z := funext hgh
  rw [e]
  exact hg.const_mul a

theorem circleIntegrable_mul_const_left {g : ℂ → ℂ} {c : ℂ} {ε : ℝ} (a : ℂ)
    (hg : CircleIntegrable g c ε) : CircleIntegrable (fun z => a * g z) c ε :=
  hg.const_mul a

theorem integrale_diff_nulle_of_moments {P Q : ℂ → ℂ} {c : ℂ} {ε : ℝ}
    (hP : CircleIntegrable P c ε) (hQ : CircleIntegrable Q c ε)
    (hmom : (∮ z in C(c, ε), (-Complex.I) * Q z) =
            ∮ z in C(c, ε), (-Complex.I) * P z) :
    (∮ z in C(c, ε), (P z - Q z)) = 0 := by
  have hpt : ∀ z, P z - Q z =
      Complex.I * ((-Complex.I) * P z - (-Complex.I) * Q z) := by
    intro z
    have h1 : Complex.I * (-Complex.I) = 1 := by
      rw [mul_neg, Complex.I_mul_I]; ring
    calc P z - Q z = (Complex.I * (-Complex.I)) * (P z - Q z) := by rw [h1]; ring
      _ = Complex.I * ((-Complex.I) * P z - (-Complex.I) * Q z) := by ring
  have e : (fun z => P z - Q z) =
      fun z => Complex.I * ((-Complex.I) * P z - (-Complex.I) * Q z) := funext hpt
  have hP' : CircleIntegrable (fun z => (-Complex.I) * P z) c ε := hP.const_mul _
  have hQ' : CircleIntegrable (fun z => (-Complex.I) * Q z) c ε := hQ.const_mul _
  change (∮ z in C(c, ε), (fun z => P z - Q z) z) = 0
  rw [e]
  rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub hP' hQ', hmom]
  simp



end CircInt2
