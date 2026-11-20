import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef

/-! -/
namespace IntProp

open MeasureTheory Finset Matrix Complex
open scoped ComplexConjugate
open ResDef

lemma integral_eq_zero_iff_ae (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Continuous f) (hpos : ∀ x, 0 ≤ f x) :
    (∫ x in Set.Icc (0:ℝ) 1, f x ∂μ = 0) ↔
      f =ᵐ[μ.restrict (Set.Icc (0:ℝ) 1)] 0 := by
  refine integral_eq_zero_iff_of_nonneg (fun x => hpos x) ?_
  exact hf.continuousOn.integrableOn_compact isCompact_Icc

lemma ae_zero_iff_measure_zeroSet (μ : Measure ℝ) [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Continuous f) :
    (f =ᵐ[μ.restrict (Set.Icc (0:ℝ) 1)] 0) ↔
      μ ({x | f x = 0} ∩ Set.Icc (0:ℝ) 1) = μ (Set.Icc (0:ℝ) 1) := by
  have hmeas : MeasurableSet {x : ℝ | f x = 0} :=
    (isClosed_eq hf continuous_const).measurableSet
  have hset : {x : ℝ | ¬ (x ∈ Set.Icc (0:ℝ) 1 → f x = 0)}
      = Set.Icc (0:ℝ) 1 \ {x | f x = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff, not_imp]
  have hsplit : μ (Set.Icc (0:ℝ) 1)
      = μ (Set.Icc (0:ℝ) 1 ∩ {x | f x = 0}) + μ (Set.Icc (0:ℝ) 1 \ {x | f x = 0}) :=
    (MeasureTheory.measure_inter_add_sdiff _ hmeas).symm
  have hfin : μ (Set.Icc (0:ℝ) 1) ≠ ⊤ := measure_ne_top _ _
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc, ae_iff]
  simp only [Pi.zero_apply]
  rw [hset, Set.inter_comm {x | f x = 0}]
  constructor
  · intro h0
    rw [hsplit, h0, add_zero]
  · intro h
    rw [h] at hsplit
    have h2 : μ (Set.Icc (0:ℝ) 1) + 0
        = μ (Set.Icc (0:ℝ) 1) + μ (Set.Icc (0:ℝ) 1 \ {x | f x = 0}) := by
      rw [add_zero]; exact hsplit
    exact (ENNReal.add_right_inj hfin |>.mp h2).symm

lemma integrableOn_pow_Icc (μ : Measure ℝ) (hμ : IsBorelOn01 μ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ n) (Set.Icc (0 : ℝ) 1) μ := by
  have _ := hμ.finite
  exact (continuous_pow n).continuousOn.integrableOn_Icc

lemma measure_on_roots (μ : Measure ℝ) (Q : Polynomial ℝ) (hQ : Q ≠ 0)
    (hae : ∀ᵐ x ∂μ, Q.eval x = 0) :
    μ ((Q.roots.toFinset : Set ℝ)ᶜ) = 0 := by
  have hmem : ∀ᵐ x ∂μ, x ∈ (Q.roots.toFinset : Set ℝ) := by
    filter_upwards [hae] with x hx
    simp [Polynomial.mem_roots hQ, hx]
  exact ae_iff.mp hmem

lemma poly_sq_ae_zero (μ : Measure ℝ) (hμ : IsBorelOn01 μ) (Q : Polynomial ℝ)
    (hz : ∫ x in Set.Icc (0 : ℝ) 1, (Q.eval x) ^ 2 ∂μ = 0) :
    ∀ᵐ x ∂(μ.restrict (Set.Icc (0 : ℝ) 1)), (Q.eval x) ^ 2 = 0 := by
  have _ := hμ.finite
  have hI : IntegrableOn (fun x : ℝ => (Q.eval x) ^ 2) (Set.Icc (0 : ℝ) 1) μ :=
    ((Polynomial.continuous Q).pow 2).continuousOn.integrableOn_Icc
  have hnn : 0 ≤ᵐ[μ.restrict (Set.Icc (0 : ℝ) 1)] fun x => (Q.eval x) ^ 2 :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  exact (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnn hI).mp hz

lemma measure_compl_roots_Icc (μ : Measure ℝ) (hμ : IsBorelOn01 μ)
    (Q : Polynomial ℝ) (hQne : Q ≠ 0)
    (hae0 : ∀ᵐ x ∂(μ.restrict (Set.Icc (0 : ℝ) 1)), (Q.eval x) ^ 2 = 0) :
    μ (((Q.roots.toFinset.filter (fun x => x ∈ Set.Icc (0:ℝ) 1) : Finset ℝ) : Set ℝ)ᶜ) = 0 := by
  have hsub : (((Q.roots.toFinset.filter (fun x => x ∈ Set.Icc (0:ℝ) 1) : Finset ℝ) : Set ℝ)ᶜ) ⊆
      (Set.Icc (0:ℝ) 1)ᶜ ∪ {x ∈ Set.Icc (0:ℝ) 1 | (Q.eval x) ^ 2 ≠ 0} := by
    intro x hx
    by_cases hx1 : x ∈ Set.Icc (0:ℝ) 1
    · right
      refine ⟨hx1, fun h0 => hx ?_⟩
      have hQx : Q.eval x = 0 := (pow_eq_zero_iff (two_ne_zero)).mp h0
      rw [Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset,
        Polynomial.mem_roots hQne]
      exact ⟨hQx, hx1⟩
    · left; exact hx1
  refine measure_mono_null hsub (measure_union_null hμ.supp ?_)
  have := (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hae0
  rw [ae_iff] at this
  refine measure_mono_null ?_ this
  intro x hx
  exact fun h => hx.2 (h hx.1)

lemma card_roots_Icc_le (Q : Polynomial ℝ) (D : ℕ) (hdeg : Q.natDegree ≤ D) :
    (Q.roots.toFinset.filter (fun x => x ∈ Set.Icc (0:ℝ) 1)).card ≤ D := by
  calc _ ≤ Q.roots.toFinset.card := Finset.card_le_card (Finset.filter_subset _ _)
    _ ≤ Q.roots.card := Multiset.toFinset_card_le _
    _ ≤ Q.natDegree := Polynomial.card_roots' Q
    _ ≤ D := hdeg


lemma integral_pow_finite_support (μ : Measure ℝ) [IsFiniteMeasure μ]
    (S : Finset ℝ) (hSsub : (S : Set ℝ) ⊆ Set.Icc (0 : ℝ) 1)
    (hSmeas : μ ((S : Set ℝ)ᶜ) = 0) (k : ℕ) :
    ∫ x in Set.Icc (0:ℝ) 1, x ^ k ∂μ = ∑ s ∈ S, (μ {s}).toReal * s ^ k := by
  have hae : (Set.Icc (0:ℝ) 1) =ᵐ[μ] (S : Set ℝ) := by
    refine Filter.EventuallyLE.antisymm ?_ ?_
    · have hS : ∀ᵐ x ∂μ, x ∈ (S : Set ℝ) := by
        rw [ae_iff]
        convert hSmeas using 2
      filter_upwards [hS] with x hx _ using hx
    · exact Filter.Eventually.of_forall (fun x hx => hSsub hx)
  rw [Measure.restrict_congr_set hae]
  have hint : IntegrableOn (fun x : ℝ => x ^ k) (S : Set ℝ) μ :=
    ((continuous_pow k).continuousOn.integrableOn_Icc).mono_set hSsub
  rw [MeasureTheory.setIntegral_finset S hint]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [smul_eq_mul]
  rfl



end IntProp
