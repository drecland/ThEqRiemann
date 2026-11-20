import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.PartialSumProp
import ThEqRiemann.IntegralResolutionTheorem.PfPolynomial
import ThEqRiemann.IntegralResolutionTheorem.MtSpec
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2

/-! -/
namespace ResIntTheorem

open Set Complex Module End
open ResDef PartialSum

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


lemma norm_resInt_le_card_mul_sup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : End ℂ V) (f : ℂ → E) (hne : (spec T).Nonempty) :
    ‖resInt T f‖ ≤ (Module.finrank ℂ V : ℝ) *
      (spec T).sup' hne (fun μ => ‖f μ‖) := by
  refine (norm_resInt_le T f).trans (sum_mT_norm_le T f _ fun μ hμ => ?_)
  exact Finset.le_sup' (fun μ => ‖f μ‖) hμ

lemma infDist_resInt_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W : Submodule ℂ E) (T : End ℂ V) (f : ℂ → E) (hf : ∀ μ ∈ spec T, f μ ∈ W) :
    Metric.infDist (resInt T f) (W : Set E) = 0 :=
  Metric.infDist_zero_of_mem (resInt_mem W T f hf)

lemma Val_univ_eq (T : End ℂ V) {E : Type*} [AddCommMonoid E] [Module ℂ E] :
    Val T (Set.univ : Set E) =
      {x | ∃ v : ℂ → E, x = ∑ μ ∈ spec T, mT T μ • v μ} := by
  ext x
  simp only [Val, Set.mem_ofPred_eq, Set.mem_univ, implies_true, true_and, resInt]
  constructor
  · rintro ⟨f, rfl⟩; exact ⟨f, rfl⟩
  · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩

lemma Val_submodule_eq (T : End ℂ V) {E : Type*} [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ E) :
    Val T (W : Set E) = {x | ∃ w : ℂ → E, (∀ μ ∈ spec T, w μ ∈ W) ∧
      x = ∑ μ ∈ spec T, mT T μ • w μ} := by
  ext x
  simp only [Val, Set.mem_ofPred_eq, SetLike.mem_coe, resInt]
  constructor
  · rintro ⟨f, hf, rfl⟩; exact ⟨f, hf, rfl⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨w, hw, rfl⟩

lemma Val_submodule_subset (T : End ℂ V) {E : Type*} [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ E) : Val T (W : Set E) ⊆ W := by
  rintro x ⟨f, hf, rfl⟩
  exact resInt_mem W T f hf

lemma pf_degree_lt (T : End ℂ V) (f : ℂ → ℂ) :
    (pf T f).degree < (spec T).card := by
  unfold pf
  exact Lagrange.degree_interpolate_lt f (Set.injOn_id _)


open PfResIntTh


lemma pf_unique (T : End ℂ V) (f : ℂ → ℂ) (q : Polynomial ℂ)
    (hq : q.degree < (spec T).card) (hqf : ∀ μ ∈ spec T, q.eval μ = f μ) :
    q = pf T f := by
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (spec T) hq
    ((pf_degree_lt T f))
  intro μ hμ
  rw [hqf μ hμ, pf_eval T f hμ]


theorem resolution_integrale (T : End ℂ V) (f : ℂ → ℂ)
    (e : Fin (spec T).card ≃ spec T) :
    (∀ n ≥ (spec T).card, partialSum T f e n = resInt T f) ∧
    Filter.Tendsto (partialSum T f e) Filter.atTop (nhds (resInt T f)) ∧
    (pf T f).degree < (spec T).card ∧
    (∀ μ ∈ spec T, (pf T f).eval μ = f μ) ∧
    LinearMap.trace ℂ V (Polynomial.aeval T (pf T f)) = resInt T f :=
  ⟨fun _ hn => partialSum_stationary T f e hn,
   partialSum_tendsto T f e,
   pf_degree_lt T f,
   fun _ hμ => pf_eval T f hμ,
   trace_pf T f⟩

theorem resolution_integrale_norme {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : End ℂ V) (f : ℂ → E) :
    ‖resInt T f‖ ≤ ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ∧
    (∀ C : ℝ, (∀ μ ∈ spec T, ‖f μ‖ ≤ C) →
      ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ≤ (Module.finrank ℂ V : ℝ) * C) ∧
    (∀ W : Submodule ℂ E, (∀ μ ∈ spec T, f μ ∈ W) →
      resInt T f ∈ W ∧ Metric.infDist (resInt T f) (W : Set E) = 0) :=
  ⟨norm_resInt_le T f,
   fun C hC => sum_mT_norm_le T f C hC,
   fun W hW => ⟨resInt_mem W T f hW, infDist_resInt_eq_zero W T f hW⟩⟩

---------------------------------------------------------------------
-- integration part

theorem norm_resInt_le_finrank_mul_sup
    (T : End ℂ V) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → E) :
    ‖resInt T f‖ ≤ (Module.finrank ℂ V : ℝ) *
      (((spec T).sup (fun μ => ‖f μ‖₊) : NNReal) : ℝ) := by
  refine le_trans (norm_resInt_le T f) ?_
  apply sum_mT_norm_le T f
  intro μ hμ
  exact_mod_cast Finset.le_sup (f := fun μ => ‖f μ‖₊) hμ

open MtRes in
theorem resolution_integrale_complet (T : End ℂ V) :
    -- (1)
    (∑ μ ∈ spec T, mT T μ = Module.finrank ℂ V) ∧
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]
        (f : ℂ → E) (e : Fin (spec T).card ≃ spec T),
      (∀ n ≥ (spec T).card, partialSum T f e n = resInt T f) ∧
      Filter.Tendsto (partialSum T f e) Filter.atTop (nhds (resInt T f)) ∧
      (∀ e' : Fin (spec T).card ≃ spec T,
        partialSum T f e (spec T).card = partialSum T f e' (spec T).card)) ∧
    -- (2)
    (∀ f : ℂ → ℂ,
      (pf T f).degree < (spec T).card ∧
      (∀ μ ∈ spec T, (pf T f).eval μ = f μ) ∧
      (∀ q : Polynomial ℂ, q.degree < (spec T).card →
        (∀ μ ∈ spec T, q.eval μ = f μ) → q = pf T f) ∧
      LinearMap.trace ℂ V (Polynomial.aeval T (pf T f)) = resInt T f) ∧
    -- (4)
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E),
      ‖resInt T f‖ ≤ ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ∧
      (∀ C : ℝ, (∀ μ ∈ spec T, ‖f μ‖ ≤ C) →
        ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ≤ (Module.finrank ℂ V : ℝ) * C)) ∧
    -- (5)
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]
        (W : Submodule ℂ E) (f : ℂ → E), (∀ μ ∈ spec T, f μ ∈ W) →
      resInt T f ∈ W ∧ Metric.infDist (resInt T f) (W : Set E) = 0) ∧
    -- (6)
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E],
      Val T (Set.univ : Set E) =
        {x | ∃ v : ℂ → E, x = ∑ μ ∈ spec T, mT T μ • v μ}) ∧
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Submodule ℂ E),
      Val T (W : Set E) = {x | ∃ w : ℂ → E, (∀ μ ∈ spec T, w μ ∈ W) ∧
        x = ∑ μ ∈ spec T, mT T μ • w μ} ∧ Val T (W : Set E) ⊆ W) := by
  refine ⟨sum_mT_eq_finrank T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro E _ _ f e
    exact ⟨fun n hn => partialSum_stationary T f e hn,
           partialSum_tendsto T f e,
           fun e' => partialSum_enum_indep T f e e'⟩
  · intro f
    have hinterp : ∀ μ ∈ spec T, (pf T f).eval μ = f μ := by
      intro μ hμ
      unfold pf
      exact Lagrange.eval_interpolate_at_node f Function.injective_id.injOn hμ
    exact ⟨pf_degree_lt T f, hinterp, fun q hq hqf => pf_unique T f q hq hqf,
           trace_pf T f⟩
  · intro E _ _ f
    exact ⟨norm_resInt_le T f, fun C hC => sum_mT_norm_le T f C hC⟩
  · intro E _ _ W f hf
    exact ⟨resInt_mem W T f hf, infDist_resInt_eq_zero W T f hf⟩
  · intro E _ _
    exact Val_univ_eq T
  · intro E _ _ W
    exact ⟨Val_submodule_eq T W, Val_submodule_subset T W⟩

open CircInt2 in
theorem resolution_integrale_residus
    (T : End ℂ V) (f F : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hspec : ∀ μ ∈ spec T, μ ∈ Metric.ball c R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall c R))
    (hFf : ∀ μ ∈ spec T, F μ = f μ) :
    (1 / (2 * Real.pi * Complex.I)) *
      (∮ z in C(c, R), F z * LinearMap.trace ℂ V
        (Ring.inverse ((algebraMap ℂ (End ℂ V) z) - T))) = resInt T f :=
  contour_integral_resInt T f F c R hR hspec hF hFf





end ResIntTheorem
