import mathlib
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef

/-! -/
namespace MtRes

open Set Matrix Module End Complex
open DefinitionsThEq ResDef

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

lemma mem_spec_iff (T : End ℂ V) (μ : ℂ) :
    μ ∈ spec T ↔ T.HasEigenvalue μ := by
  unfold spec
  rw [Multiset.mem_toFinset,
      Polynomial.mem_roots (LinearMap.charpoly_monic T).ne_zero,
      Module.End.hasEigenvalue_iff_isRoot_charpoly]

lemma mT_eq_finrank_ker_pow (T : End ℂ V) (μ : ℂ) :
    mT T μ = Module.finrank ℂ
      (LinearMap.ker ((T - μ • (1 : End ℂ V)) ^ (Module.finrank ℂ V))) := by
  have h : T.maxGenEigenspace μ =
      LinearMap.ker ((T - μ • (1 : End ℂ V)) ^ (Module.finrank ℂ V)) := by
    rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank]
    exact Module.End.genEigenspace_nat
  unfold mT
  rw [h]

lemma mT_eq_rootMultiplicity (T : End ℂ V) (μ : ℂ) :
    mT T μ = Polynomial.rootMultiplicity μ (LinearMap.charpoly T) :=
  LinearMap.finrank_maxGenEigenspace_eq T μ

lemma sum_mT_eq_finrank (T : End ℂ V) :
    ∑ μ ∈ spec T, mT T μ = Module.finrank ℂ V := by
  have hdeg : (LinearMap.charpoly T).natDegree = Module.finrank ℂ V :=
    LinearMap.charpoly_natDegree T
  have hsplit : (LinearMap.charpoly T).roots.card = (LinearMap.charpoly T).natDegree :=
  (IsAlgClosed.card_roots_eq_natDegree)
  calc ∑ μ ∈ spec T, mT T μ
      = ∑ μ ∈ spec T, Polynomial.rootMultiplicity μ (LinearMap.charpoly T) := by
        refine Finset.sum_congr rfl fun μ _ => mT_eq_rootMultiplicity T μ
  _ = (LinearMap.charpoly T).roots.card := by
      unfold spec
      rw [← Multiset.toFinset_sum_count_eq]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [Polynomial.count_roots]
    _ = Module.finrank ℂ V := by rw [hsplit, hdeg]




end MtRes
