import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.MtSpec


/-! -/
namespace MaxGenEigen

open Set Module End Complex
open ResDef MtRes

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


lemma maxGenEigenspace_eq_bot_of_not_mem (T : End ℂ V) {μ : ℂ} (hμ : μ ∉ spec T) :
    T.maxGenEigenspace μ = ⊥ := by
  rw [mem_spec_iff, Module.End.hasEigenvalue_iff, not_not] at hμ
  have hinj : Function.Injective (T - μ • (1 : End ℂ V)) := by
    rw [← LinearMap.ker_eq_bot]
    simpa [Module.End.eigenspace_def] using hμ
  rw [eq_bot_iff]
  intro x hx
  rw [Module.End.mem_maxGenEigenspace] at hx
  obtain ⟨k, hk⟩ := hx
  have hkinj : Function.Injective ((T - μ • (1 : End ℂ V)) ^ k) := by
    rw [Module.End.coe_pow]
    exact hinj.iterate k
  have : x = 0 := hkinj (by simpa using hk)
  simp [this]

lemma isInternal_maxGenEigenspace_spec (T : End ℂ V) :
    DirectSum.IsInternal (fun μ : spec T =>
      T.maxGenEigenspace (μ : ℂ)) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨(independent_maxGenEigenspace T).comp
    Subtype.val_injective, ?_⟩
  apply eq_top_iff.mpr
  rw [← iSup_maxGenEigenspace_eq_top T]
  refine iSup_le fun μ => ?_
  by_cases hμ : μ ∈ spec T
  · exact le_iSup (fun ν : spec T => T.maxGenEigenspace (ν : ℂ)) ⟨μ, hμ⟩
  · rw [maxGenEigenspace_eq_bot_of_not_mem T hμ]; exact bot_le

omit [FiniteDimensional ℂ V] in
lemma mapsTo_aeval_maxGenEigenspace (T : End ℂ V) (p : Polynomial ℂ) (μ : ℂ) :
    Set.MapsTo (Polynomial.aeval T p) (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) := by
  have h_comm : Commute T (Polynomial.aeval T p) := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [map_add, Commute.add_right hp hq]
    | monomial n a =>
      simp only [Polynomial.aeval_monomial]
      have hscal : Commute T (algebraMap ℂ (End ℂ V) a) :=
        Algebra.commute_algebraMap_right a T
      have hpow : Commute T (T ^ n) := Commute.pow_right (Commute.refl T) n
      exact hscal.mul_right hpow
  exact Module.End.mapsTo_maxGenEigenspace_of_comm h_comm μ

omit [FiniteDimensional ℂ V] in
lemma mapsTo_sub_aeval (T : End ℂ V) (p : Polynomial ℂ) (μ : ℂ) :
    Set.MapsTo (Polynomial.aeval T p - algebraMap ℂ (End ℂ V) (p.eval μ))
      (T.maxGenEigenspace μ) (T.maxGenEigenspace μ) := by
  intro x hx
  have h1 := mapsTo_aeval_maxGenEigenspace T p μ hx
  have h2 : (algebraMap ℂ (End ℂ V) (p.eval μ)) x ∈ T.maxGenEigenspace μ := by
    rw [Algebra.algebraMap_eq_smul_one]
    simpa using Submodule.smul_mem _ (p.eval μ) hx
  simpa using Submodule.sub_mem _ h1 h2

omit [FiniteDimensional ℂ V] in
lemma T_mem_maxGenEigenspace (T : End ℂ V) (μ : ℂ) {x : V}
    (hx : x ∈ T.maxGenEigenspace μ) : T x ∈ T.maxGenEigenspace μ := by
  rw [Module.End.mem_maxGenEigenspace] at hx ⊢
  obtain ⟨k, hk⟩ := hx
  refine ⟨k, ?_⟩
  have hc : Commute T ((T - μ • (1 : End ℂ V)) ^ k) := by
    apply Commute.pow_right
    exact (Commute.refl T).sub_right ((Commute.one_right T).smul_right μ)
  have := congrArg (fun f => f x) hc.eq
  simp only [Module.End.mul_apply] at this
  rw [← this, hk, map_zero]

end MaxGenEigen
