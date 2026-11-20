import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2
import ThEqRiemann.ComplementRiemann.ReductionXiDirichlet

/-! -/
namespace EtaPartialProperty

open Set Complex
open RiemannDef CircInt2




lemma deriv_etaPartial_tendstoUniformlyOn
    {η : ℂ → ℂ} {c : ℂ} {R : ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hsub : (fun z : ℂ => 1 / 2 + z) '' Metric.sphere c R ⊆ U)
    (hdiff : ∀ N, DifferentiableOn ℂ (etaPartial N) U)
    (hloc : TendstoLocallyUniformlyOn etaPartial η Filter.atTop U) :
    TendstoUniformlyOn (fun N z => deriv (etaPartial N) (1 / 2 + z))
      (fun z => deriv η (1 / 2 + z)) Filter.atTop (Metric.sphere c R) := by
  have h1 : TendstoLocallyUniformlyOn (fun N => deriv (etaPartial N)) (deriv η)
      Filter.atTop U :=
    hloc.deriv (Filter.Eventually.of_forall hdiff) hU
  have h2 := tendstoUniformlyOn_of_locallyUniformlyOn_compact hU h1
    (isCompact_image_add_half_sphere c R) hsub
  exact tendstoUniformlyOn_comp_add_half h2

lemma quot_etaPartial_tendstoUniformlyOn
    {η : ℂ → ℂ} {c : ℂ} {R : ℝ} (_ : 0 < R)
    (hη_cont0 : ContinuousOn (fun z => η (1 / 2 + z)) (Metric.sphere c R))
    (hdη_cont0 : ContinuousOn (fun z => deriv η (1 / 2 + z)) (Metric.sphere c R))
    (hηN_conv : TendstoUniformlyOn (fun N z => etaPartial N (1 / 2 + z))
      (fun z => η (1 / 2 + z)) Filter.atTop (Metric.sphere c R))
    (hdηN_conv : TendstoUniformlyOn (fun N z => deriv (etaPartial N) (1 / 2 + z))
      (fun z => deriv η (1 / 2 + z)) Filter.atTop (Metric.sphere c R))
    (hη_ne : ∀ z ∈ Metric.sphere c R, η (1 / 2 + z) ≠ 0) :
    TendstoUniformlyOn
      (fun N z => z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z)))
      (fun z => z * (deriv η (1 / 2 + z) / η (1 / 2 + z)))
      Filter.atTop (Metric.sphere c R) := by
  have hK : IsCompact (Metric.sphere c R) := isCompact_sphere c R
  obtain ⟨m, hm, hlow⟩ := exists_pos_le_norm_of_compact hK hη_cont0 hη_ne
  have hlowN := eventually_half_le_norm hm hηN_conv hlow
  obtain ⟨A, hA⟩ := hK.exists_bound_of_continuousOn hdη_cont0
  have hquot := tendstoUniformlyOn_div hm hdηN_conv hηN_conv hA hlow hlowN
  refine tendstoUniformlyOn_mul_left_of_bdd (B := ‖c‖ + R) hquot ?_
  intro z hz
  have h1 : dist z c = R := Metric.mem_sphere.mp hz
  have h2 : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
    calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
  rw [← dist_eq_norm, h1] at h2
  linarith

open ReducXiDirichlet in
theorem ApproximationSpectraleZeros
    {η ζ : ℂ → ℂ} {c : ℂ} {R : ℝ} {zm : ℂ} {U : Set ℂ} (hR : 0 < R)
    (hdisk : ∀ z ∈ Metric.closedBall c R, z.re < 1 / 2)
    (hrel : ∀ w, η w = (1 - (2 : ℂ) ^ (1 - w)) * ζ w)
    (hζ_circle : (1 / (2 * Real.pi * I)) * ∮ z in C(c, R), z *
      (deriv ζ (1 / 2 + z) / ζ (1 / 2 + z)) = zm)
    (hint1 : CircleIntegrable (fun z => z * (deriv η (1 / 2 + z) / η (1 / 2 + z))) c R)
    (hint2 : CircleIntegrable (fun z => z * hFacteur z) c R)
    (hlog : ∀ z ∈ Metric.sphere c R,
      deriv ζ (1 / 2 + z) / ζ (1 / 2 + z) =
        deriv η (1 / 2 + z) / η (1 / 2 + z) - hFacteur z)
    (hU : IsOpen U)
    (hsub : (fun z : ℂ => 1 / 2 + z) '' Metric.sphere c R ⊆ U)
    (hdiff : ∀ N, DifferentiableOn ℂ (etaPartial N) U)
    (hloc : TendstoLocallyUniformlyOn etaPartial η Filter.atTop U)
    (hηN_conv : TendstoUniformlyOn (fun N z => etaPartial N (1 / 2 + z))
      (fun z => η (1 / 2 + z)) Filter.atTop (Metric.sphere c R))
    (hη_ne : ∀ z ∈ Metric.sphere c R, η (1 / 2 + z) ≠ 0)
    (hη_cont0 : ContinuousOn (fun z => η (1 / 2 + z)) (Metric.sphere c R))
    (hdη_cont0 : ContinuousOn (fun z => deriv η (1 / 2 + z)) (Metric.sphere c R))
    (hηN_cont : ∀ N, ContinuousOn
      (fun z => z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z)))
      (Metric.sphere c R))
    (hη_cont : ContinuousOn
      (fun z => z * (deriv η (1 / 2 + z) / η (1 / 2 + z))) (Metric.sphere c R)) :
    Filter.Tendsto
      (fun N => (1 / (2 * Real.pi * I)) * ∮ z in C(c, R),
        z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z)))
      Filter.atTop (nhds zm)
    ∧ Filter.Tendsto
      (fun N => ((1 / (2 * Real.pi * I)) * ∮ z in C(c, R),
        z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z))).re)
      Filter.atTop (nhds zm.re)
    ∧ Filter.Tendsto
      (fun N => ((1 / (2 * Real.pi * I)) * ∮ z in C(c, R),
        z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z))).im)
      Filter.atTop (nhds zm.im) := by
  have hlim : (1 / (2 * Real.pi * I)) * ∮ z in C(c, R),
      z * (deriv η (1 / 2 + z) / η (1 / 2 + z)) = zm :=
    DeriveeLogZetaEta hR hdisk hrel intervalIntegrable_const hζ_circle hint1 hint2 hlog
  have hdηN_conv := deriv_etaPartial_tendstoUniformlyOn hU hsub hdiff hloc
  have hquot_conv := quot_etaPartial_tendstoUniformlyOn hR hη_cont0 hdη_cont0
    hηN_conv hdηN_conv hη_ne
  have hint_lim := circleIntegral_tendsto_of_tendstoUniformlyOn hR hηN_cont hη_cont hquot_conv
  have hT : Filter.Tendsto
      (fun N => (1 / (2 * Real.pi * I)) * ∮ z in C(c, R),
        z * (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z)))
      Filter.atTop (nhds zm) := by
    rw [← hlim]
    exact hint_lim.const_mul _
  exact ⟨hT, (Complex.continuous_re.tendsto zm).comp hT,
    (Complex.continuous_im.tendsto zm).comp hT⟩


----------------------------------------------------------------------


lemma conj_etaPartial (N : ℕ) (s : ℂ) :
    (starRingEnd ℂ) (etaPartial N s) = etaPartial N ((starRingEnd ℂ) s) := by
  unfold etaPartial
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hn0 : ((n : ℕ) : ℂ) ≠ 0 := by
    have : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact_mod_cast (by omega : n ≠ 0)
  have key : (starRingEnd ℂ) (((n : ℕ) : ℂ) ^ s) = ((n : ℕ) : ℂ) ^ (starRingEnd ℂ) s := by
    rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0,
        ← Complex.exp_conj, map_mul]
    have hlog : (starRingEnd ℂ) (Complex.log ((n : ℕ) : ℂ)) = Complex.log ((n : ℕ) : ℂ) := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
      exact Complex.conj_ofReal _
    rw [hlog]
  rw [map_div₀, map_pow, map_neg, map_one, key]

lemma differentiable_etaPartial (N : ℕ) (w : ℂ) :
    DifferentiableAt ℂ (etaPartial N) w := by
  unfold etaPartial
  refine DifferentiableAt.fun_sum (fun n hn => ?_)
  have hn0 : n ≠ 0 := by
    have : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    omega
  have hn0' : ((n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hn0
  have hnum : DifferentiableAt ℂ (fun _ : ℂ => ((-1 : ℂ) ^ (n - 1))) w :=
    differentiableAt_const _
  have hden : DifferentiableAt ℂ (fun s : ℂ => ((n : ℕ) : ℂ) ^ s) w :=
    differentiableAt_id.const_cpow (Or.inl hn0')
  have hne : ((n : ℕ) : ℂ) ^ w ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hn0']
    exact Complex.exp_ne_zero _
  exact hnum.div hden hne

lemma deriv_conj_comp_conj (f : ℂ → ℂ) (s : ℂ) :
    deriv (fun w => (starRingEnd ℂ) (f ((starRingEnd ℂ) w))) s
      = (starRingEnd ℂ) (deriv f ((starRingEnd ℂ) s)) := by
  have h := congrFun (deriv_conj_conj (f := f)) s
  simpa [Function.comp_def] using h

lemma conj_deriv_etaPartial (N : ℕ) (s : ℂ) :
    (starRingEnd ℂ) (deriv (etaPartial N) s) =
      deriv (etaPartial N) ((starRingEnd ℂ) s) := by
  have hsym : etaPartial N = fun w => (starRingEnd ℂ) (etaPartial N ((starRingEnd ℂ) w)) := by
    funext w
    rw [← conj_etaPartial, Complex.conj_conj]
  have h := deriv_conj_comp_conj (etaPartial N) ((starRingEnd ℂ) s)
  rw [Complex.conj_conj, ← hsym] at h
  exact h.symm

lemma conj_logDeriv_etaPartial (N : ℕ) (z : ℂ) :
    (starRingEnd ℂ) (deriv (etaPartial N) (1 / 2 + z) / etaPartial N (1 / 2 + z))
      = deriv (etaPartial N) (1 / 2 + (starRingEnd ℂ) z)
          / etaPartial N (1 / 2 + (starRingEnd ℂ) z) := by
  have h12 : (starRingEnd ℂ) (1 / 2 + z) = 1 / 2 + (starRingEnd ℂ) z := by
    rw [map_add, map_div₀, map_one]
    congr 2
    exact map_ofNat (starRingEnd ℂ) 2
  rw [map_div₀, conj_deriv_etaPartial, conj_etaPartial, h12]

---------------------------------------------------------------------

lemma conj_integral_etaPartial (N : ℕ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    (starRingEnd ℂ) (∮ z in C(c, R), z * (deriv (etaPartial N) (1 / 2 + z)
        / etaPartial N (1 / 2 + z)))
      = - ∮ w in C((starRingEnd ℂ) c, R), w * (deriv (etaPartial N) (1 / 2 + w)
        / etaPartial N (1 / 2 + w)) := by
  rw [conj_circleIntegral]
  congr 1
  refine circleIntegral.integral_congr hR ?_
  intro w _
  simp only [map_mul, Complex.conj_conj]
  rw [conj_logDeriv_etaPartial, Complex.conj_conj]





end EtaPartialProperty
