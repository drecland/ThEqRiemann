import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.MtSpec
import ThEqRiemann.IntegralResolutionTheorem.TraceMtMul
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2
/-! -/
namespace NewtonTraceZero

open Set Complex Module End
open ResDef MtRes


variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


lemma charpoly_coeff_pred (T : End ℂ V) (hV : 0 < Module.finrank ℂ V) :
    (LinearMap.charpoly T).coeff (Module.finrank ℂ V - 1)
      = - LinearMap.trace ℂ V T := by
  let b := Module.finBasis ℂ V
  have _: Nonempty (Fin (Module.finrank ℂ V)) := ⟨⟨0, hV⟩⟩
  have h1 : LinearMap.trace ℂ V T = Matrix.trace (LinearMap.toMatrix b b T) :=
    LinearMap.trace_eq_matrix_trace ℂ b T
  have h2 : (LinearMap.toMatrix b b T).charpoly = LinearMap.charpoly T :=
    LinearMap.charpoly_toMatrix T b
  have h3 := Matrix.trace_eq_neg_charpoly_coeff (LinearMap.toMatrix b b T)
  rw [h1, h3, h2, Fintype.card_fin, neg_neg]


lemma newton_zero (T : End ℂ V) : newton T 0 = Module.finrank ℂ V := by
  unfold newton
  simp only [pow_zero, mul_one]
  exact_mod_cast sum_mT_eq_finrank T


open TraceMtMulRes

lemma newton_one (T : End ℂ V) : newton T 1 = LinearMap.trace ℂ V T := by
  unfold newton
  simp only [pow_one]
  exact (trace_eq_sum_mT_mul T).symm

theorem trace_eq_newton_eq_neg_coeff' (T : End ℂ V) :
    LinearMap.trace ℂ V T = ∑ μ ∈ spec T, (mT T μ : ℂ) * μ ∧
    newton T 1 = LinearMap.trace ℂ V T ∧
    (Module.finrank ℂ V = 0 ∨
      (LinearMap.charpoly T).coeff (Module.finrank ℂ V - 1) = - newton T 1) := by
  refine ⟨trace_eq_sum_mT_mul T, newton_one T, ?_⟩
  rcases Nat.eq_zero_or_pos (Module.finrank ℂ V) with h | h
  · exact Or.inl h
  · right
    rw [newton_one, charpoly_coeff_pred T h]

lemma tendsto_neg_div {x y : ℕ → ℂ} {a : ℂ}
    (hx : Filter.Tendsto x Filter.atTop (nhds a))
    (hy : Filter.Tendsto y Filter.atTop (nhds 1)) :
    Filter.Tendsto (fun n => - x n / y n) Filter.atTop (nhds (-a)) := by
  have h := hx.neg.div hy one_ne_zero
  rw [div_one] at h
  exact h

lemma finrank_pos_of_spec_nonempty (T : End ℂ V) (h : (spec T).Nonempty) :
    0 < Module.finrank ℂ V := by
  rw [← sum_mT_eq_finrank T]
  obtain ⟨μ, hμ⟩ := h
  have hm : 0 < mT T μ := by
    rw [mT_eq_rootMultiplicity]
    exact (Polynomial.rootMultiplicity_pos
      (LinearMap.charpoly_monic T).ne_zero).mpr
      ((Polynomial.mem_roots (LinearMap.charpoly_monic T).ne_zero).mp
        (Multiset.mem_toFinset.mp hμ))
  exact lt_of_lt_of_le hm
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hμ)

theorem limit_S_eq_trace (T : End ℂ V) (hV : 0 < Module.finrank ℂ V)
    {an1 aN : ℕ → ℂ}
    (_ : ∀ n, aN n ≠ 0)
    (hN : Filter.Tendsto aN Filter.atTop (nhds 1))
    (h1 : Filter.Tendsto an1 Filter.atTop
      (nhds ((LinearMap.charpoly T).coeff (Module.finrank ℂ V - 1)))) :
    Filter.Tendsto (fun n => Rrat (an1 n) (aN n)) Filter.atTop
      (nhds (LinearMap.trace ℂ V T)) := by
  have h := tendsto_neg_div h1 hN
  rw [charpoly_coeff_pred T hV, neg_neg] at h
  exact h


open CircInt2

theorem corollaire_trace_zeros_newton
    (T : End ℂ V) (hne : (spec T).Nonempty)
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hf : ∃ r > R, DifferentiableOn ℂ f (Metric.ball c r))
    (hnz : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (hzeros : ∀ μ ∈ spec T,
      μ ∈ Metric.ball c R ∧ f μ = 0 ∧ analyticOrderAt f μ = (mT T μ : ℕ∞))
    (hall : ∀ z ∈ Metric.ball c R, f z = 0 → z ∈ spec T) :
    (1 / (2 * Real.pi * Complex.I)) *
        (∮ z in C(c, R), z * (deriv f z / f z))
      = ∑ μ ∈ spec T, (mT T μ : ℂ) * μ ∧
    ∑ μ ∈ spec T, (mT T μ : ℂ) * μ = LinearMap.trace ℂ V T ∧
    LinearMap.trace ℂ V T = newton T 1 ∧
    newton T 1 = - (LinearMap.charpoly T).coeff (Module.finrank ℂ V - 1) := by
  have hV := finrank_pos_of_spec_nonempty T hne
  have hA := argument_principle_trace T f c R hR hf hnz hzeros hall
  have hB := trace_eq_sum_mT_mul T
  refine ⟨hA.trans hB, hB.symm, (newton_one T).symm, ?_⟩
  rw [newton_one, charpoly_coeff_pred T hV, neg_neg]

theorem corollaire_trace_zeros_newton_general
    (T : End ℂ V) (hne : (spec T).Nonempty)
    (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hzeros : ∀ μ ∈ spec T, μ ∈ Metric.ball c R)
    (P : Finset ℂ) (ν : ℂ → ℕ)
    (hP : ∀ p ∈ P, p ∈ Metric.ball c R)
    (g : ℂ → ℂ) (V' : Set ℂ) (hV' : IsOpen V')
    (hVb : Metric.closedBall c R ⊆ V')
    (hgV : DifferentiableOn ℂ g V')
    (hgnz : ∀ z ∈ Metric.closedBall c R, g z ≠ 0)
    (U : Set ℂ) (hU : IsOpen U) (hUs : Metric.sphere c R ⊆ U)
    (hfg : ∀ z ∈ U,
      f z = g z * (∏ μ ∈ spec T, (z - μ) ^ mT T μ) / ∏ p ∈ P, (z - p) ^ ν p)
    {an1 aN : ℕ → ℂ} (haN0 : ∀ n, aN n ≠ 0)
    (hN : Filter.Tendsto aN Filter.atTop (nhds 1))
    (h1 : Filter.Tendsto an1 Filter.atTop
      (nhds ((LinearMap.charpoly T).coeff (Module.finrank ℂ V - 1)))) :
    ((1 / (2 * Real.pi * Complex.I)) * (∮ z in C(c, R), z * (deriv f z / f z))
        = ∑ μ ∈ spec T, (mT T μ : ℂ) * μ - ∑ p ∈ P, (ν p : ℂ) * p) ∧
    (∑ μ ∈ spec T, (mT T μ : ℂ) * μ = LinearMap.trace ℂ V T) ∧
    (LinearMap.trace ℂ V T = newton T 1) ∧
    (newton T 1 = - (LinearMap.charpoly T).coeff (Module.finrank ℂ V - 1)) ∧
    Filter.Tendsto (fun n => Rrat (an1 n) (aN n)) Filter.atTop
      (nhds (LinearMap.trace ℂ V T)) := by
  have hV := finrank_pos_of_spec_nonempty T hne
  refine ⟨?_, trace_eq_sum_mT_mul T |>.symm, (newton_one T).symm, ?_,
          limit_S_eq_trace T hV haN0 hN h1⟩
  · exact argument_principle_meromorphic f c R hR (spec T) P (mT T) ν
      hzeros hP g V' hV' hVb hgV (hgV.mono hVb) hgnz U hU hUs hfg
  · rw [newton_one, charpoly_coeff_pred T hV, neg_neg]








end NewtonTraceZero
