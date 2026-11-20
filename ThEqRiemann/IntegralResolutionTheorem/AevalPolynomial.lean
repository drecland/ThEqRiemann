import mathlib
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.MtSpec
import ThEqRiemann.IntegralResolutionTheorem.MaxGenEigenspace

/-! -/
namespace Aeval

open Set Module End Complex
open ResDef MtRes MaxGenEigen

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


omit [FiniteDimensional ℂ V] in
lemma commute_aeval_self (T : End ℂ V) (q : Polynomial ℂ) :
    Commute T (Polynomial.aeval T q) := by
  induction q using Polynomial.induction_on' with
  | add p r hp hr => simpa using hp.add_right hr
  | monomial n a =>
    simp only [map_mul, Polynomial.aeval_C,
      Polynomial.aeval_X_pow, ← Polynomial.C_mul_X_pow_eq_monomial]
    exact ((Commute.refl T).pow_right n).smul_right a

omit [FiniteDimensional ℂ V] in
lemma commute_restrict {W : Submodule ℂ V} {f g : End ℂ V}
    (hf : Set.MapsTo f W W) (hg : Set.MapsTo g W W) (hc : Commute f g) :
    Commute (f.restrict hf) (g.restrict hg) := by
  refine LinearMap.ext fun x => Subtype.ext ?_
  have h := congrArg (fun h => h (x : V)) hc.eq
  simp only [Module.End.mul_apply] at h
  simp only [Module.End.mul_apply]
  exact h

omit [FiniteDimensional ℂ V] in
lemma restrict_mul {W : Submodule ℂ V} {f g : End ℂ V}
    (hf : Set.MapsTo f W W) (hg : Set.MapsTo g W W)
    (hfg : Set.MapsTo (f * g) W W) :
    (f * g).restrict hfg = f.restrict hf * g.restrict hg := by
  ext x
  simp only [Module.End.mul_apply]
  rfl

lemma isNilpotent_restrict_aeval_sub (T : End ℂ V) (p : Polynomial ℂ) (μ : ℂ) :
    IsNilpotent ((Polynomial.aeval T p - algebraMap ℂ (End ℂ V) (p.eval μ)).restrict
      (mapsTo_sub_aeval T p μ)) := by
  have hroot : (p - Polynomial.C (p.eval μ)).IsRoot μ := by simp
  set q := (p - Polynomial.C (p.eval μ)) /ₘ (Polynomial.X - Polynomial.C μ) with hq
  have hfac : (Polynomial.X - Polynomial.C μ) * q = p - Polynomial.C (p.eval μ) :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hop : Polynomial.aeval T p - algebraMap ℂ (End ℂ V) (p.eval μ)
      = (T - algebraMap ℂ (End ℂ V) μ) * Polynomial.aeval T q := by
    have := congrArg (Polynomial.aeval T) hfac
    simpa [map_mul, map_sub] using this.symm
  have hT_maps : Set.MapsTo (T - algebraMap ℂ (End ℂ V) μ)
      (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) := by
    intro x hx
    have h1 : T x ∈ T.maxGenEigenspace μ := T_mem_maxGenEigenspace T μ hx
    have h2 : (algebraMap ℂ (End ℂ V) μ) x ∈ T.maxGenEigenspace μ := by
      rw [Algebra.algebraMap_eq_smul_one]
      simpa using Submodule.smul_mem _ μ hx
    simpa using Submodule.sub_mem _ h1 h2
  have hq_maps := mapsTo_aeval_maxGenEigenspace T q μ
  have hnil := Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap T μ hT_maps
  have hc : Commute (T - algebraMap ℂ (End ℂ V) μ) (Polynomial.aeval T q) :=
    (commute_aeval_self T q).sub_left (Algebra.commute_algebraMap_left μ _)
  have hcomm := commute_restrict hT_maps hq_maps hc
  have hmul : (Polynomial.aeval T p - algebraMap ℂ (End ℂ V) (p.eval μ)).restrict
        (mapsTo_sub_aeval T p μ)
      = (T - algebraMap ℂ (End ℂ V) μ).restrict hT_maps *
        (Polynomial.aeval T q).restrict hq_maps := by
    have hprod : Set.MapsTo ((T - algebraMap ℂ (End ℂ V) μ) * Polynomial.aeval T q)
        (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) := hop ▸ mapsTo_sub_aeval T p μ
    rw [← restrict_mul hT_maps hq_maps hprod]
    congr 1
  rw [hmul]
  exact hcomm.isNilpotent_mul_right hnil

lemma trace_restrict_aeval (T : End ℂ V) (p : Polynomial ℂ) (μ : ℂ) :
    LinearMap.trace ℂ (T.maxGenEigenspace μ)
      ((Polynomial.aeval T p).restrict (mapsTo_aeval_maxGenEigenspace T p μ))
      = (mT T μ : ℂ) * p.eval μ := by
  set A := (Polynomial.aeval T p).restrict (mapsTo_aeval_maxGenEigenspace T p μ)
  set N := (Polynomial.aeval T p - algebraMap ℂ (End ℂ V) (p.eval μ)).restrict
    (mapsTo_sub_aeval T p μ)
  have hN := isNilpotent_restrict_aeval_sub T p μ
  have htrN : LinearMap.trace ℂ (T.maxGenEigenspace μ) N = 0 :=
    (LinearMap.isNilpotent_trace_of_isNilpotent hN).eq_zero
  have hA : A = N + (p.eval μ) • (LinearMap.id : T.maxGenEigenspace μ →ₗ[ℂ] _) := by
    ext x
    simp only [A, N, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.coe_restrict_apply, LinearMap.sub_apply,
      Algebra.algebraMap_eq_smul_one, Submodule.coe_add, Submodule.coe_smul,
      Module.End.one_apply]
    simp
    abel
  rw [hA, map_add, htrN, zero_add, map_smul, LinearMap.trace_id, smul_eq_mul]
  rw [mul_comm]
  congr 2

lemma trace_aeval_eq_sum (T : End ℂ V) (p : Polynomial ℂ) :
    LinearMap.trace ℂ V (Polynomial.aeval T p) =
      ∑ μ ∈ spec T, (mT T μ : ℂ) * p.eval μ := by
  rw [LinearMap.trace_eq_sum_trace_restrict
        (isInternal_maxGenEigenspace_spec T)
        (fun μ : spec T => mapsTo_aeval_maxGenEigenspace T p (μ : ℂ))]
  rw [← Finset.sum_coe_sort (spec T)]
  exact Finset.sum_congr rfl fun μ _ => trace_restrict_aeval T p μ


theorem resolvent_eq_aeval
    (T : End ℂ V) (z : ℂ) (hz : z ∉ spec T) :
    ∃ Q : Polynomial ℂ,
      Ring.inverse ((algebraMap ℂ (End ℂ V) z) - T) = Polynomial.aeval T Q ∧
      ∀ μ ∈ spec T, Q.eval μ = (z - μ)⁻¹ := by
  classical
  set p : Polynomial ℂ := LinearMap.charpoly T with hp
  have hp0 : p ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  have hp0' : LinearMap.charpoly T ≠ 0 := (LinearMap.charpoly_monic T).ne_zero
  have hpz : p.eval z ≠ 0 := by
    intro h
    apply hz
    simp only [spec, Multiset.mem_toFinset, Polynomial.mem_roots hp0']
    exact h
  obtain ⟨R, hR⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := z) (p := p)
  have hCH : Polynomial.aeval T p = 0 := LinearMap.aeval_self_charpoly T
  have h2 : (algebraMap ℂ (End ℂ V) z - T) * Polynomial.aeval T R
      = algebraMap ℂ (End ℂ V) (p.eval z) := by
    have h1 : Polynomial.aeval T (p - Polynomial.C (p.eval z))
        = Polynomial.aeval T ((Polynomial.X - Polynomial.C z) * R) :=
      congrArg (Polynomial.aeval T) hR
    have hL : Polynomial.aeval T (p - Polynomial.C (p.eval z))
        = -(algebraMap ℂ (End ℂ V) (p.eval z)) := by
      rw [map_sub, hCH, Polynomial.aeval_C, zero_sub]
    have hRt : Polynomial.aeval T ((Polynomial.X - Polynomial.C z) * R)
        = (T - algebraMap ℂ (End ℂ V) z) * Polynomial.aeval T R := by
      rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [hL, hRt] at h1
    calc (algebraMap ℂ (End ℂ V) z - T) * Polynomial.aeval T R
        = -((T - algebraMap ℂ (End ℂ V) z) * Polynomial.aeval T R) := by
          rw [← neg_mul, neg_sub]
      _ = algebraMap ℂ (End ℂ V) (p.eval z) := by rw [← h1, neg_neg]
  refine ⟨Polynomial.C (p.eval z)⁻¹ * R, ?_, ?_⟩
  · have hTQ : ∀ Q : Polynomial ℂ, Commute T (Polynomial.aeval T Q) := by
      intro Q
      induction Q using Polynomial.induction_on' with
      | add p q hp hq => simpa using hp.add_right hq
      | monomial n a =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, Polynomial.aeval_C,
              map_pow, Polynomial.aeval_X]
          have h1 : Commute T (algebraMap ℂ (End ℂ V) a) := (Algebra.commutes a T).symm
          have h2 : Commute T (T ^ n) := (Commute.refl T).pow_right n
          exact h1.mul_right h2
    have hmul : (algebraMap ℂ (End ℂ V) z - T) *
        Polynomial.aeval T (Polynomial.C (p.eval z)⁻¹ * R) = 1 := by
      calc (algebraMap ℂ (End ℂ V) z - T) * Polynomial.aeval T (Polynomial.C (p.eval z)⁻¹ * R)
          = (algebraMap ℂ (End ℂ V) (p.eval z)⁻¹) *
              ((algebraMap ℂ (End ℂ V) z - T) * Polynomial.aeval T R) := by
            rw [map_mul, Polynomial.aeval_C, ← mul_assoc, ← mul_assoc,
                (Algebra.commutes _ _)]
        _ = 1 := by
            rw [h2, ← map_mul, inv_mul_cancel₀ hpz, map_one]
    have hcomm : Commute (algebraMap ℂ (End ℂ V) z - T)
        (Polynomial.aeval T (Polynomial.C (p.eval z)⁻¹ * R)) :=
      Commute.sub_left (Algebra.commutes z _) (hTQ _)
    have hmul' : Polynomial.aeval T (Polynomial.C (p.eval z)⁻¹ * R) *
        (algebraMap ℂ (End ℂ V) z - T) = 1 := by
      rw [← hcomm.eq]; exact hmul
    let u : (End ℂ V)ˣ := ⟨_, _, hmul, hmul'⟩
    have hu : (u : End ℂ V) = algebraMap ℂ (End ℂ V) z - T := rfl
    rw [← hu, Ring.inverse_unit]
    rfl
  · intro μ hμ
    have hpμ : p.eval μ = 0 := by
      simp only [spec, Multiset.mem_toFinset, Polynomial.mem_roots hp0'] at hμ
      exact hμ
    have h1 : -(p.eval z) = (μ - z) * R.eval μ := by
      have h1' : Polynomial.eval μ (p - Polynomial.C (p.eval z))
          = Polynomial.eval μ ((Polynomial.X - Polynomial.C z) * R) :=
        congrArg (Polynomial.eval μ) hR
      rw [Polynomial.eval_sub, hpμ, Polynomial.eval_C, zero_sub,
        Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C] at h1'
      exact h1'
    have hne : z - μ ≠ 0 := by
      intro h
      apply hz
      rw [sub_eq_zero.mp h]; exact hμ
    have hR' : Polynomial.eval μ R = (p.eval z) * (z - μ)⁻¹ := by
      field_simp
      linear_combination h1
    rw [Polynomial.eval_mul, Polynomial.eval_C, hR']
    field_simp






end Aeval
