import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.MtSpec

/-! -/
namespace PartialSum

open Set Complex Module End ResDef

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]



lemma partialSum_card (T : End ℂ V) {E : Type*}
    [AddCommMonoid E] [Module ℂ E]
    (f : ℂ → E) (e : Fin (spec T).card ≃ spec T) :
    partialSum T f e (spec T).card = resInt T f := by
  unfold partialSum resInt
  rw [min_self, Finset.sum_range]
  have : ∀ i : Fin (spec T).card, term T f e i = mT T (e i) • f (e i) := by
    intro i
    simp [term, i.isLt]
  simp_rw [this]
  rw [← Finset.sum_coe_sort (spec T)]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma partialSum_stationary (T : End ℂ V) {E : Type*}
    [AddCommMonoid E] [Module ℂ E]
    (f : ℂ → E) (e : Fin (spec T).card ≃ spec T) {n : ℕ}
    (hn : (spec T).card ≤ n) :
    partialSum T f e n = resInt T f := by
  rw [← partialSum_card T f e]
  unfold partialSum
  rw [min_eq_right hn, min_self]


lemma partialSum_tendsto (T : End ℂ V) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) (e : Fin (spec T).card ≃ spec T) :
    Filter.Tendsto (partialSum T f e) Filter.atTop (nhds (resInt T f)) := by
  apply tendsto_atTop_of_eventually_const (i₀ := (spec T).card)
  intro n hn
  exact partialSum_stationary T f e hn

lemma partialSum_enum_indep (T : End ℂ V) {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (f : ℂ → E) (e₁ e₂ : Fin (spec T).card ≃ spec T) :
    partialSum T f e₁ (spec T).card = partialSum T f e₂ (spec T).card := by
  rw [partialSum_card, partialSum_card]

open MtRes

lemma sum_mT_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : End ℂ V) (f : ℂ → E) (C : ℝ) (hC : ∀ μ ∈ spec T, ‖f μ‖ ≤ C) :
    ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ≤ (Module.finrank ℂ V : ℝ) * C := by
  calc ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖
      ≤ ∑ μ ∈ spec T, (mT T μ : ℝ) * C := by
        refine Finset.sum_le_sum fun μ hμ => ?_
        exact mul_le_mul_of_nonneg_left (hC μ hμ) (Nat.cast_nonneg _)
    _ = (∑ μ ∈ spec T, (mT T μ : ℝ)) * C := by rw [Finset.sum_mul]
    _ = (Module.finrank ℂ V : ℝ) * C := by
        congr 1
        exact_mod_cast sum_mT_eq_finrank T



end PartialSum
