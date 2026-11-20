import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2
/-! -/
namespace ReducXiDirichlet

open Set Complex
open RiemannDef

lemma differentiableAt_hFacteur {z : ℂ} (hz : z.re < 1 / 2) :
    DifferentiableAt ℂ hFacteur z := by
  have hden : (1 : ℂ) - (2 : ℂ) ^ ((1/2 : ℂ) - z) ≠ 0 := by
    intro h
    have h1 : (2 : ℂ) ^ ((1/2 : ℂ) - z) = 1 := by linear_combination -h
    have h2 : ‖(2 : ℂ) ^ ((1/2 : ℂ) - z)‖ = (2 : ℝ) ^ (1/2 - z.re) := by
      have h2c : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
      rw [h2c, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ) < 2)]
      simp
    rw [h1, norm_one] at h2
    have h3 : (1 : ℝ) < (2 : ℝ) ^ (1/2 - z.re) :=
      Real.one_lt_rpow (by norm_num) (by linarith)
    linarith
  have hlin : DifferentiableAt ℂ (fun t : ℂ => (1/2 : ℂ) - t) z :=
    (differentiableAt_const _).sub differentiableAt_id
  have hA : DifferentiableAt ℂ (fun t : ℂ => (2 : ℂ) ^ ((1/2 : ℂ) - t)) z :=
    hlin.const_cpow (Or.inl (by norm_num))
  have hnum : DifferentiableAt ℂ
      (fun t : ℂ => (2 : ℂ) ^ ((1/2 : ℂ) - t) * Complex.log 2) z :=
    hA.mul (differentiableAt_const _)
  have hdenf : DifferentiableAt ℂ
      (fun t : ℂ => 1 - (2 : ℂ) ^ ((1/2 : ℂ) - t)) z :=
    (differentiableAt_const _).sub hA
  unfold hFacteur
  exact hnum.div hdenf hden

lemma circleIntegral_z_hFacteur_eq_zero {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hdisk : ∀ z ∈ Metric.closedBall c R, z.re < 1 / 2) :
    (∮ z in C(c, R), z * hFacteur z) = 0 := by
  have hdiffAt : ∀ z ∈ Metric.closedBall c R,
      DifferentiableAt ℂ (fun w => w * hFacteur w) z := fun z hz =>
    differentiableAt_id.mul (differentiableAt_hFacteur (hdisk z hz))
  have hcont : ContinuousOn (fun w => w * hFacteur w) (Metric.closedBall c R) :=
    fun z hz => (hdiffAt z hz).continuousAt.continuousWithinAt
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
    hR.le Set.countable_empty hcont
    (fun z hz => hdiffAt z (Metric.ball_subset_closedBall hz.1))

lemma logDeriv_zeta_eq {η ζ : ℂ → ℂ} {s : ℂ}
    (hrel : ∀ w, η w = (1 - (2 : ℂ) ^ (1 - w)) * ζ w)
    (hζ : DifferentiableAt ℂ ζ s) (hζ0 : ζ s ≠ 0)
    (hφ0 : 1 - (2 : ℂ) ^ (1 - s) ≠ 0) :
    deriv ζ s / ζ s =
      deriv η s / η s - (2 : ℂ) ^ (1 - s) *
      Complex.log 2 / (1 - (2 : ℂ) ^ (1 - s)) := by
  have hφ : HasDerivAt (fun w : ℂ => 1 - (2 : ℂ) ^ (1 - w))
      ((2 : ℂ) ^ (1 - s) * Complex.log 2) s := by
    have h1 : HasDerivAt (fun w : ℂ => 1 - w) (-1) s := by
      simpa using (hasDerivAt_id s).const_sub 1
    have h2 : HasDerivAt (fun w : ℂ => (2 : ℂ) ^ (1 - w))
        ((2 : ℂ) ^ (1 - s) * Complex.log 2 * (-1)) s :=
      h1.const_cpow (Or.inl (by norm_num))
    have h3 := h2.const_sub 1
    convert h3 using 1
    ring
  have hη : HasDerivAt η
      ((2 : ℂ) ^ (1 - s) * Complex.log 2 * ζ s
        + (1 - (2 : ℂ) ^ (1 - s)) * deriv ζ s) s := by
    have hprod := hφ.mul hζ.hasDerivAt
    have hfun : η = fun w => (1 - (2 : ℂ) ^ (1 - w)) * ζ w := funext hrel
    rw [hfun]
    exact hprod
  have hη0 : η s ≠ 0 := by
    rw [hrel s]
    exact mul_ne_zero hφ0 hζ0
  rw [hη.deriv, hrel s]
  field_simp
  ring

lemma DeriveeLogZetaEta {η ζ : ℂ → ℂ} {c : ℂ} {R : ℝ} {zm : ℂ} (hR : 0 < R)
    (hdisk : ∀ z ∈ Metric.closedBall c R, z.re < 1 / 2)
    (_ : ∀ w, η w = (1 - (2 : ℂ) ^ (1 - w)) * ζ w)
    (_ : IntervalIntegrable (fun _ => (0 : ℂ)) MeasureTheory.volume 0 0)
    (hζ_circle : (1 / (2 * Real.pi * I)) * ∮ z in C(c, R), z *
      (deriv ζ (1 / 2 + z) / ζ (1 / 2 + z)) = zm)
    (hint1 : CircleIntegrable (fun z => z * (deriv η (1 / 2 + z) / η (1 / 2 + z))) c R)
    (hint2 : CircleIntegrable (fun z => z * hFacteur z) c R)
    (hlog : ∀ z ∈ Metric.sphere c R,
      deriv ζ (1 / 2 + z) / ζ (1 / 2 + z) =
        deriv η (1 / 2 + z) / η (1 / 2 + z) - hFacteur z) :
    (1 / (2 * Real.pi * I)) * ∮ z in C(c, R), z *
      (deriv η (1/2 + z) / η (1/2 + z)) = zm := by
  have h0 : (∮ z in C(c, R), z * hFacteur z) = 0 :=
    circleIntegral_z_hFacteur_eq_zero hR hdisk
  have hcongr : (∮ z in C(c, R), z * (deriv ζ (1 / 2 + z) / ζ (1 / 2 + z)))
      = ∮ z in C(c, R), (z * (deriv η (1 / 2 + z) / η (1 / 2 + z))
          - z * hFacteur z) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    simp only
    rw [hlog z hz]
    ring
  have hsub : (∮ z in C(c, R), (z * (deriv η (1 / 2 + z) / η (1 / 2 + z))
          - z * hFacteur z))
      = (∮ z in C(c, R), z * (deriv η (1 / 2 + z) / η (1 / 2 + z)))
        - ∮ z in C(c, R), z * hFacteur z :=
    circleIntegral.integral_sub hint1 hint2
  rw [hcongr, hsub, h0, sub_zero] at hζ_circle
  exact hζ_circle

open CircInt2 in
lemma EvaluationResidusDirichlet
    {N : ℕ} (_ : 0 < N) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hne : ∀ z ∈ Metric.sphere c R, etaPartial N (1 / 2 + z) ≠ 0)
    (hne' : ∀ z ∈ Metric.sphere ((starRingEnd ℂ) c) R, etaPartial N (1 / 2 + z) ≠ 0)
    (S S' : Finset ℂ)
    (hS : ∀ z, z ∈ S ↔ z ∈ Metric.ball c R ∧ etaPartial N (1 / 2 + z) = 0)
    (hS' : ∀ z, z ∈ S' ↔ z ∈ Metric.ball
      ((starRingEnd ℂ) c) R ∧ etaPartial N (1 / 2 + z) = 0) :
    (1 / (2 * ↑Real.pi * I)) * ∮ z in C(c, R),
        z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z))
      = ∑ a ∈ S, ((analyticOrderAt
        (fun z => etaPartial N (1 / 2 + z)) a).toNat : ℂ) * a
    ∧
    (1 / (2 * ↑Real.pi * I)) * ∮ z in C((starRingEnd ℂ) c, R),
        z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z))
      = ∑ a ∈ S', ((analyticOrderAt
        (fun z => etaPartial N (1 / 2 + z)) a).toNat : ℂ) * a := by
  have hent : Differentiable ℂ (fun z => etaPartial N (1 / 2 + z)) := by
    have hη : Differentiable ℂ (etaPartial N) := by
      unfold etaPartial
      apply Differentiable.fun_sum
      intro n hn
      have hn0 : (n : ℂ) ≠ 0 := by
        have h1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
        exact_mod_cast (by omega : n ≠ 0)
      have hpow : ∀ y : ℂ, (n : ℂ) ^ y = Complex.exp (Complex.log n * y) := by
        intro y
        rw [Complex.cpow_def_of_ne_zero hn0]
      simp only [hpow]
      exact (differentiable_const _).div
        ((differentiable_const _ |>.mul differentiable_id).cexp)
        (fun s => Complex.exp_ne_zero _)
    exact hη.comp (differentiable_const _ |>.add differentiable_id)
  have hderiv : ∀ z, deriv (fun w => etaPartial N (1 / 2 + w)) z
      = deriv (etaPartial N) (1 / 2 + z) := by
    intro z
    exact deriv_comp_const_add (etaPartial N) (1 / 2 : ℂ) z
  have hid : Differentiable ℂ (fun z : ℂ => z) := differentiable_id
  constructor
  · have h1 := argument_principle_circle (f := fun z => etaPartial N (1 / 2 + z))
      (h := fun z => z) hR hent hid hne S hS
    rw [circleIntegral_rewrite_deriv hderiv] at h1
    exact h1
  · have h2 := argument_principle_circle (f := fun z => etaPartial N (1 / 2 + z))
      (h := fun z => z) hR hent hid hne' S' hS'
    rw [circleIntegral_rewrite_deriv hderiv] at h2
    exact h2





end ReducXiDirichlet
