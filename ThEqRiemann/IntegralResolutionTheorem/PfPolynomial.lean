import mathlib
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.AevalPolynomial

/-! -/
namespace PfResIntTh

open Set Module End Complex
open ResDef Aeval

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


lemma pf_eval (T : End ℂ V) (f : ℂ → ℂ) {μ : ℂ} (hμ : μ ∈ spec T) :
    (pf T f).eval μ = f μ :=
  Lagrange.eval_interpolate_at_node f (Set.injOn_id _) hμ

theorem trace_pf (T : End ℂ V) (f : ℂ → ℂ) :
    LinearMap.trace ℂ V (Polynomial.aeval T (pf T f)) = resInt T f := by
  rw [trace_aeval_eq_sum]
  unfold resInt
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [pf_eval T f (by simpa using hμ)]
  simp [nsmul_eq_mul]



end PfResIntTh
