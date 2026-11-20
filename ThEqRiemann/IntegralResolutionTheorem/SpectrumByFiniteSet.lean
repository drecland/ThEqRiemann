import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.DefPosHankelResInt

/-! -/
namespace SpecFiniteSet

open MeasureTheory Finset Matrix Complex
open scoped ComplexConjugate
open ResDef

lemma spectral_recurrence_abstract
    (u : ℕ → ℕ → ℂ) (m : ℕ → ℂ) (D : ℕ) (a : Fin D → ℝ)
    (hm : ∀ k, Filter.Tendsto (fun q => u k q) Filter.atTop (nhds (m k)))
    (hQ : ∀ n, Filter.Tendsto
      (fun q => u (n + D) q - ∑ j : Fin D, (a j : ℂ) * u (n + j) q)
      Filter.atTop (nhds 0))
    (n : ℕ) :
    m (n + D) = ∑ j : Fin D, (a j : ℂ) * m (n + j) := by
  have h1 : Filter.Tendsto
      (fun q => u (n + D) q - ∑ j : Fin D, (a j : ℂ) * u (n + j) q)
      Filter.atTop (nhds (m (n + D) - ∑ j : Fin D, (a j : ℂ) * m (n + j))) := by
    refine (hm (n + D)).sub ?_
    exact tendsto_finsetSum _ (fun j _ => (hm (n + j)).const_mul (a j : ℂ))
  have h2 := tendsto_nhds_unique h1 (hQ n)
  exact sub_eq_zero.mp h2

lemma quad_poly_linear {D : ℕ} (a : Fin D → ℝ)
    (lam x : (q : ℕ) → Fin q → ℝ) (n q : ℕ) :
    ∑ r : Fin q, lam q r * (x q r ^ n * (x q r ^ D - ∑ j : Fin D, a j * x q r ^ (j : ℕ)))
      = ∑ r : Fin q, lam q r * x q r ^ (n + D)
        - ∑ j : Fin D, a j * ∑ r : Fin q, lam q r * x q r ^ (n + (j : ℕ)) := by
  have h1 : ∀ r : Fin q, lam q r * (x q r ^ n * (x q r ^ D - ∑ j : Fin D, a j * x q r ^ (j : ℕ)))
      = lam q r * x q r ^ (n + D)
        - ∑ j : Fin D, a j * (lam q r * x q r ^ (n + (j : ℕ))) := by
    intro r
    have e1 : x q r ^ n * (x q r ^ D - ∑ j : Fin D, a j * x q r ^ (j : ℕ))
        = x q r ^ (n + D) - ∑ j : Fin D, a j * x q r ^ (n + (j : ℕ)) := by
      have hsum : x q r ^ n * ∑ j : Fin D, a j * x q r ^ (j : ℕ)
          = ∑ j : Fin D, a j * x q r ^ (n + (j : ℕ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [pow_add]; ring
      rw [mul_sub, hsum, pow_add]
    rw [e1, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]

lemma moments_recurrence {m : ℕ → ℝ} {N : ℕ} {x lam : (q : ℕ) → Fin q → ℝ}
    (h : IsElementaryResolution m N x lam) {D : ℕ} (a : Fin D → ℝ) (n : ℕ)
    (hn : n + D ≤ 2 * N)
    (hQ : Filter.Tendsto
      (fun q : ℕ => ∑ r : Fin q, lam q r * (x q r ^ n *
        (x q r ^ D - ∑ j : Fin D, a j * x q r ^ (j : ℕ))))
      Filter.atTop (nhds 0)) :
    m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ)) := by
  obtain ⟨-, -, hmom⟩ := h
  have h1 : Filter.Tendsto
      (fun q : ℕ => ∑ r : Fin q, lam q r * x q r ^ (n + D)
        - ∑ j : Fin D, a j * ∑ r : Fin q, lam q r * x q r ^ (n + (j : ℕ)))
      Filter.atTop (nhds (m (n + D) - ∑ j : Fin D, a j * m (n + (j : ℕ)))) := by
    refine (hmom (n + D) hn).sub ?_
    refine tendsto_finsetSum _ (fun j _ => ?_)
    exact (hmom (n + (j : ℕ)) (by have := j.2; omega)).const_mul (a j)
  have h2 : Filter.Tendsto
      (fun q : ℕ => ∑ r : Fin q, lam q r * x q r ^ (n + D)
        - ∑ j : Fin D, a j * ∑ r : Fin q, lam q r * x q r ^ (n + (j : ℕ)))
      Filter.atTop (nhds 0) := by
    simpa only [quad_poly_linear a lam x n] using hQ
  exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)

open DefPosHankelRes
open scoped ComplexOrder

lemma limit_pos_of_posDef {m : ℕ → ℝ} {N : ℕ} {x lam : (q : ℕ) → Fin q → ℝ}
    (h : IsElementaryResolution m N x lam)
    (hpd : (hankel' m N).PosDef) :
    ∀ c : Fin (N+1) → ℂ, c ≠ 0 → ∃ L : ℝ, 0 < L ∧ Filter.Tendsto
      (fun q : ℕ => ∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2) Filter.atTop (nhds L) :=
  (posDef_iff_limit_pos_vec m N h).mp hpd

lemma support_roots_of_vandermonde {r D : ℕ} (a : Fin D → ℝ)
    (pts w : Fin r → ℝ) (hinj : Function.Injective pts) (hw : ∀ i, 0 < w i)
    (hrec : ∀ n : ℕ, ∑ i : Fin r, w i * (pts i ^ n *
      (pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ))) = 0) :
    ∀ i, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0 := by
  set v : Fin r → ℝ := fun i => w i * (pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ)) with hv
  have hv0 : ∀ n : ℕ, ∑ i, v i * pts i ^ n = 0 := by
    intro n
    have := hrec n
    rw [← this]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [hv]; ring
  have hdet : (Matrix.vandermonde pts).det ≠ 0 := by
    rw [Matrix.det_vandermonde_ne_zero_iff]
    exact hinj
  have hmul : (Matrix.vandermonde pts).transpose.mulVec v = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.vandermonde_apply, Pi.zero_apply]
    have := hv0 (k : ℕ)
    simpa [mul_comm] using this
  have hdetT : (Matrix.vandermonde pts).transpose.det ≠ 0 := by
    rwa [Matrix.det_transpose]
  have hv_zero : v = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hdetT hmul
  intro i
  have hvi : v i = 0 := congrFun hv_zero i
  simp only [hv] at hvi
  rcases mul_eq_zero.mp hvi with h0 | h0
  · exact absurd h0 (hw i).ne'
  · exact h0

theorem caracterisation_globale_finie (m : ℕ → ℝ) {D : ℕ} (a : Fin D → ℝ)
    (hrec : ∀ n, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ)))
    (hK : KroneckerPositive m D) :
    ∃ (r : ℕ) (_ : r ≤ D) (pts : Fin r → ℝ) (w : Fin r → ℝ),
      Function.Injective pts ∧ (∀ i, 0 < w i) ∧
      (∀ k, m k = ∑ i, w i * pts i ^ k) ∧
      ∀ i, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0 := by
  obtain ⟨r, hr, pts, w, hinj, -, hw, hm⟩ := hK
  refine ⟨r, hr, pts, w, hinj, hw, hm, ?_⟩
  apply support_roots_of_vandermonde a pts w hinj hw
  intro n
  have h1 := hrec n
  rw [hm (n + D)] at h1
  simp_rw [hm (n + _)] at h1
  rw [← sub_eq_zero] at h1
  have key : ∑ i, w i * (pts i ^ n * (pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ)))
      = ∑ i, w i * pts i ^ (n + D) - ∑ x : Fin D, a x * ∑ i, w i * pts i ^ (n + (x : ℕ)) := by
    simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [pow_add]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
  rw [key]
  exact h1




end SpecFiniteSet
