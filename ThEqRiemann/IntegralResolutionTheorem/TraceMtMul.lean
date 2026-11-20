import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.AevalPolynomial


/-! -/
namespace TraceMtMulRes

open Set Module End Complex
open ResDef Aeval

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


lemma trace_eq_sum_mT_mul (T : End ℂ V) :
    LinearMap.trace ℂ V T = ∑ μ ∈ spec T, (mT T μ : ℂ) * μ := by
  have h := trace_aeval_eq_sum T Polynomial.X
  simpa using h

end TraceMtMulRes
