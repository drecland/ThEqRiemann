import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.InductionRiemannZero
import ThEqRiemann.RiemannProof.XiEntiereProp

/-! -/

namespace BrainrotLemma_Riemann

open Set Complex ComplexConjugate
open RiemannDef

lemma zero_conj_of_zero (Xi : ℂ → ℂ)
    (hconj : ∀ z, Xi (conj z) = conj (Xi z))
    {γ : ℂ} (h : Xi γ = 0) : Xi (conj γ) = 0 := by
  rw [hconj, h, map_zero]

lemma newton_palier_critique_im
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ) (h : PalierCritique γ m n₀) (k : ℕ) :
    (newton γ m (n₀ + 1) k).im = 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, n₀ = p + 1 := ⟨n₀ - 1, by have := h.n0_ge; omega⟩
  unfold newton
  rw [Complex.im_sum]
  rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
  have h1 : ∑ j ∈ Finset.Icc 1 p, ((m j : ℂ) * γ j ^ k).im = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [Finset.mem_Icc] at hj
    have him : (γ j).im = 0 := h.reels_avant j hj.1 (by omega)
    have hr : γ j = ((γ j).re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hr, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
    exact Complex.ofReal_im _
  rw [h1, h.conj_zero, h.mult_conj, zero_add]
  have hc : (conj (γ (p + 1))) ^ k = conj (γ (p + 1) ^ k) := (map_pow _ _ _).symm
  rw [hc, Complex.mul_im, Complex.mul_im, Complex.conj_im]
  simp

lemma prod_fin_eq_prod_Icc (n : ℕ) (f : ℕ → ℂ) :
    ∏ j : Fin n, f (↑j + 1) = ∏ j ∈ Finset.Icc 1 n, f j := by
  rw [Fin.prod_univ_eq_prod_range (fun j => f (j + 1)) n]
  rw [Finset.range_eq_Ico, Finset.prod_Ico_add' f 0 n 1]
  congr 1

open InducRiemannZero in
lemma delta_palier_critique
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ) (h : PalierCritique γ m n₀) :
    Delta γ m (n₀ + 1) (n₀ + 1) =
      -4 * ((m n₀ : ℂ) ^ 2) * ((γ n₀).im : ℂ) ^ 2 *
        Delta γ m (n₀ - 1) (n₀ - 1) *
        ∏ j ∈ Finset.Icc 1 (n₀ - 1), ((Complex.normSq (γ n₀ - γ j) : ℝ) : ℂ) ^ 2 := by
  obtain ⟨p, rfl⟩ : ∃ p, n₀ = p + 1 := ⟨n₀ - 1, by have := h.n0_ge; omega⟩
  have e1 := delta_succ γ m (p + 1)
  have e2 := delta_succ γ m p
  simp only [Nat.add_sub_cancel]
  rw [e1, e2]
  have hP1 : ∏ j : Fin (p + 1), (γ (p + 1 + 1) - γ (↑j + 1)) ^ 2
      = ∏ j ∈ Finset.Icc 1 (p + 1), (γ (p + 1 + 1) - γ j) ^ 2 :=
    prod_fin_eq_prod_Icc (p + 1) (fun j => (γ (p + 1 + 1) - γ j) ^ 2)
  have hP2 : ∏ j : Fin p, (γ (p + 1) - γ (↑j + 1)) ^ 2
      = ∏ j ∈ Finset.Icc 1 p, (γ (p + 1) - γ j) ^ 2 :=
    prod_fin_eq_prod_Icc p (fun j => (γ (p + 1) - γ j) ^ 2)
  rw [hP1, hP2, Finset.prod_Icc_succ_top (by omega)]
  rw [h.conj_zero, h.mult_conj]
  have hc : (conj (γ (p + 1)) - γ (p + 1)) ^ 2 = -4 * ((γ (p + 1)).im : ℂ) ^ 2 := by
    have : conj (γ (p + 1)) - γ (p + 1) = -2 * Complex.I * ((γ (p + 1)).im : ℂ) := by
      apply Complex.ext <;> simp ; ring
    rw [this]; ring_nf; simp [Complex.I_sq]
  have hj : ∀ j ∈ Finset.Icc 1 p,
      (γ (p + 1) - γ j) ^ 2 * (conj (γ (p + 1)) - γ j) ^ 2
        = ((Complex.normSq (γ (p + 1) - γ j) : ℝ) : ℂ) ^ 2 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hr : conj (γ j) = γ j :=
      Complex.ext (by simp) (by simp [h.reels_avant j hj.1 (by omega)])
    have hcj : conj (γ (p + 1) - γ j) = conj (γ (p + 1)) - γ j := by rw [map_sub, hr]
    rw [← hcj, ← mul_pow, Complex.mul_conj]
  rw [hc]
  have hprod : (∏ j ∈ Finset.Icc 1 p, (γ (p + 1) - γ j) ^ 2) *
      (∏ k ∈ Finset.Icc 1 p, (conj (γ (p + 1)) - γ k) ^ 2) =
      ∏ x ∈ Finset.Icc 1 p, ((Complex.normSq (γ (p + 1) - γ x) : ℝ) : ℂ) ^ 2 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hj
  calc _ = (m (p + 1) : ℂ) ^ 2 * (-4 * ((γ (p + 1)).im : ℂ) ^ 2) * Delta γ m p p *
        ((∏ j ∈ Finset.Icc 1 p, (γ (p + 1) - γ j) ^ 2) *
         (∏ k ∈ Finset.Icc 1 p, (conj (γ (p + 1)) - γ k) ^ 2)) := by ring
    _ = _ := by rw [hprod]; ring


lemma signe_delta_palier_critique
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ) (h : PalierCritique γ m n₀)
    (hΔpos : 0 < (Delta γ m (n₀ - 1) (n₀ - 1)).re)
    (hΔreal : (Delta γ m (n₀ - 1) (n₀ - 1)).im = 0)
    (hm : 1 ≤ m n₀) :
    ((-4 * ((m n₀ : ℂ) ^ 2) * ((γ n₀).im : ℂ) ^ 2 *
        Delta γ m (n₀ - 1) (n₀ - 1) *
        ∏ j ∈ Finset.Icc 1 (n₀ - 1), ((Complex.normSq (γ n₀ - γ j) : ℝ) : ℂ) ^ 2)).re < 0 ∧
    ((-4 * ((m n₀ : ℂ) ^ 2) * ((γ n₀).im : ℂ) ^ 2 *
        Delta γ m (n₀ - 1) (n₀ - 1) *
        ∏ j ∈ Finset.Icc 1 (n₀ - 1), ((Complex.normSq (γ n₀ - γ j) : ℝ) : ℂ) ^ 2)).im = 0 := by
  have hD : Delta γ m (n₀ - 1) (n₀ - 1) = ((Delta γ m (n₀ - 1) (n₀ - 1)).re : ℂ) :=
    Complex.ext (by simp) (by simp [hΔreal])
  have hprod : ∏ j ∈ Finset.Icc 1 (n₀ - 1), ((Complex.normSq (γ n₀ - γ j) : ℝ) : ℂ) ^ 2
      = ((∏ j ∈ Finset.Icc 1 (n₀ - 1), (Complex.normSq (γ n₀ - γ j)) ^ 2 : ℝ) : ℂ) := by
    push_cast; rfl
  have hpos : 0 < ∏ j ∈ Finset.Icc 1 (n₀ - 1), (Complex.normSq (γ n₀ - γ j)) ^ 2 := by
    apply Finset.prod_pos
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hne : γ n₀ - γ j ≠ 0 := by
      intro h0
      have : (γ n₀).im = (γ j).im := by
        have := congrArg Complex.im h0; simpa [sub_eq_zero] using this
      exact h.non_reel (by rw [this]; exact h.reels_avant j hj.1 (by have := h.n0_ge; omega))
    have := Complex.normSq_pos.mpr hne
    positivity
  have hIm : 0 < (γ n₀).im ^ 2 := by
    have := h.non_reel; positivity
  have hm' : (0 : ℝ) < (m n₀ : ℝ) ^ 2 := by
    have : (0 : ℝ) < m n₀ := by exact_mod_cast hm
    positivity
  rw [hD, hprod]
  constructor
  · have : ((-4 * ((m n₀ : ℂ) ^ 2) * ((γ n₀).im : ℂ) ^ 2 *
        (((Delta γ m (n₀ - 1) (n₀ - 1)).re : ℝ) : ℂ) *
        ((∏ j ∈ Finset.Icc 1 (n₀ - 1), (Complex.normSq (γ n₀ - γ j)) ^ 2 : ℝ) : ℂ))).re
        = -4 * (m n₀ : ℝ) ^ 2 * (γ n₀).im ^ 2 * (Delta γ m (n₀ - 1) (n₀ - 1)).re *
          ∏ j ∈ Finset.Icc 1 (n₀ - 1), (Complex.normSq (γ n₀ - γ j)) ^ 2 := by
      norm_cast
    rw [this]
    have : 0 < (m n₀ : ℝ) ^ 2 * (γ n₀).im ^ 2 * (Delta γ m (n₀ - 1) (n₀ - 1)).re *
        ∏ j ∈ Finset.Icc 1 (n₀ - 1), (Complex.normSq (γ n₀ - γ j)) ^ 2 := by positivity
    linarith
  · norm_cast

lemma etape1_rupture_positivite
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ) (h : PalierCritique γ m n₀)
    (hΔpos : 0 < (Delta γ m (n₀ - 1) (n₀ - 1)).re)
    (hΔreal : (Delta γ m (n₀ - 1) (n₀ - 1)).im = 0)
    (hm : 1 ≤ m n₀) :
    (∀ k, (newton γ m (n₀ + 1) k).im = 0) ∧
    Delta γ m (n₀ + 1) (n₀ + 1) =
      -4 * ((m n₀ : ℂ) ^ 2) * ((γ n₀).im : ℂ) ^ 2 *
        Delta γ m (n₀ - 1) (n₀ - 1) *
        ∏ j ∈ Finset.Icc 1 (n₀ - 1), ((Complex.normSq (γ n₀ - γ j) : ℝ) : ℂ) ^ 2 ∧
    (Delta γ m (n₀ + 1) (n₀ + 1)).re < 0 ∧
    (Delta γ m (n₀ + 1) (n₀ + 1)).im = 0 := by
  have hΔ := delta_palier_critique γ m n₀ h
  have hs := signe_delta_palier_critique γ m n₀ h hΔpos hΔreal hm
  refine ⟨newton_palier_critique_im γ m n₀ h, hΔ, ?_, ?_⟩
  · rw [hΔ]; exact hs.1
  · rw [hΔ]; exact hs.2

lemma etape2_propagation_sylvester {N₀ r : ℕ} (hr : N₀ ≤ r)
    (B : Matrix (Fin r) (Fin r) ℝ)
    (A : Matrix (Fin N₀) (Fin N₀) ℝ)
    (hA : ∀ i j : Fin N₀, A i j = B (Fin.castLE hr i) (Fin.castLE hr j))
    (hdet : A.det ≤ 0) : ¬ B.PosDef := by
  intro hB
  have hAeq : A = B.submatrix (Fin.castLE hr) (Fin.castLE hr) := by
    ext i j
    simp [hA i j]
  have hApos : A.PosDef := by
    rw [hAeq]
    exact hB.submatrix (Fin.castLE_injective hr)
  exact absurd hApos.det_pos (not_lt.mpr hdet)

lemma etape2_hankel (γ : ℕ → ℂ) (m : ℕ → ℕ) (N N₀ r : ℕ)
    (hN₀r : N₀ ≤ r) (_ : r ≤ N)
    (hdet : (Delta γ m N N₀).re ≤ 0) :
    ¬ ∃ B : Matrix (Fin r) (Fin r) ℝ, B.PosDef ∧
      (∀ p q : Fin r, (B p q : ℂ) = newton γ m N (p + q)) := by
  rintro ⟨B, hB, hBeq⟩
  set A : Matrix (Fin N₀) (Fin N₀) ℝ :=
    B.submatrix (Fin.castLE hN₀r) (Fin.castLE hN₀r) with hA_def
  have hA : ∀ i j : Fin N₀, A i j = B (Fin.castLE hN₀r i) (Fin.castLE hN₀r j) := by
    intro i j; rfl
  have hmat : A.map (Complex.ofReal) =
      (Matrix.of fun p q : Fin N₀ => newton γ m N ((p : ℕ) + (q : ℕ))) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [hA i j, hBeq]
    simp [Fin.castLE]
  have hdetA : A.det = (Delta γ m N N₀).re := by
    have h1 : Delta γ m N N₀ = ((A.det : ℝ) : ℂ) := by
      unfold Delta
      rw [← hmat]
      exact (RingHom.map_det Complex.ofRealHom A).symm
    rw [h1, Complex.ofReal_re]
  exact etape2_propagation_sylvester hN₀r B A hA (by rw [hdetA]; exact hdet) hB

open Polynomial Matrix

open InducRiemannZero in
lemma etape3_forme_quadratique
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (N u v : ℕ)
    (hu : u ∈ Finset.Icc 1 N) (hv : v ∈ Finset.Icc 1 N) (huv : u ≠ v)
    (P : ℂ[X]) (hdeg : P.natDegree < N)
    (hP : ∀ j ∈ (Finset.Icc 1 N).erase u |>.erase v, P.eval (γ j) = 0) :
    (fun p : Fin N => P.coeff p) ⬝ᵥ (Hn γ m N *ᵥ fun p : Fin N => P.coeff p)
      = (m u : ℂ) * (P.eval (γ u)) ^ 2 + (m v : ℂ) * (P.eval (γ v)) ^ 2 := by
  rw [Hn_eq_factor]
  set c : Fin N → ℂ := fun p => P.coeff p with hc
  have hV : ∀ j : Fin N, (Vn γ N *ᵥ c) j = P.eval (γ (j + 1)) := by
    intro j
    rw [Polynomial.eval_eq_sum_range' (n := N) hdeg]
    simp only [Matrix.mulVec, dotProduct, Vn, hc, Matrix.of_apply]
    rw [Fin.sum_univ_eq_sum_range (fun i => γ (↑j + 1) ^ i * P.coeff i) N]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hform : c ⬝ᵥ ((Vn γ N)ᵀ * Mn m N * Vn γ N) *ᵥ c
      = (Vn γ N *ᵥ c) ⬝ᵥ (Mn m N *ᵥ (Vn γ N *ᵥ c)) := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  rw [hform]
  have hsum : (Vn γ N *ᵥ c) ⬝ᵥ (Mn m N *ᵥ (Vn γ N *ᵥ c))
      = ∑ j ∈ Finset.Icc 1 N, (m j : ℂ) * (P.eval (γ j)) ^ 2 := by
    have h1 : (Vn γ N *ᵥ c) ⬝ᵥ (Mn m N *ᵥ (Vn γ N *ᵥ c))
        = ∑ j : Fin N, (m ((j : ℕ) + 1) : ℂ) * (P.eval (γ ((j : ℕ) + 1))) ^ 2 := by
      simp only [dotProduct, Mn, Matrix.mulVec_diagonal, hV]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1]
    rw [Fin.sum_univ_eq_sum_range
          (fun i => (m (i + 1) : ℂ) * (P.eval (γ (i + 1))) ^ 2) N]
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun j => (m j : ℂ) * (P.eval (γ j)) ^ 2) 0 N 1]
    rfl
  rw [hsum]
  have hrest : ∑ j ∈ ((Finset.Icc 1 N).erase u).erase v,
      (m j : ℂ) * (P.eval (γ j)) ^ 2 = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hP j hj]; ring
  have hv' : v ∈ (Finset.Icc 1 N).erase u := Finset.mem_erase.mpr ⟨huv.symm, hv⟩
  rw [← Finset.add_sum_erase _ _ hu, ← Finset.add_sum_erase _ _ hv', hrest]
  ring


lemma det_plan_deux (g₁ g₂ w₁ w₂ : ℂ) :
    (!![1, 1; g₁, g₂] * !![w₁, 0; 0, w₂] * !![1, g₁; 1, g₂]).det
      = w₁ * w₂ * (g₂ - g₁) ^ 2 := by
  simp [Matrix.det_fin_two]
  ring

lemma delta_plan_negatif (g : ℂ) (hg : g.im ≠ 0) (mm : ℕ) (hmm : 1 ≤ mm)
    (Q : ℂ[X]) (hQ : Q.eval (conj g) = conj (Q.eval g)) (hQg : Q.eval g ≠ 0) :
    ((mm : ℂ) ^ 2 * (Q.eval g) ^ 2 * (Q.eval (conj g)) ^ 2 * (conj g - g) ^ 2)
      = (((-4 * (mm : ℝ) ^ 2 * g.im ^ 2 * (Complex.normSq (Q.eval g)) ^ 2 : ℝ)) : ℂ)
    ∧ (-4 * (mm : ℝ) ^ 2 * g.im ^ 2 * (Complex.normSq (Q.eval g)) ^ 2) < 0 := by
  constructor
  · rw [hQ]
    have h1 : (Q.eval g) ^ 2 * (conj (Q.eval g)) ^ 2
        = ((Complex.normSq (Q.eval g) : ℝ) : ℂ) ^ 2 := by
      rw [← mul_pow, Complex.mul_conj]
    have h2 : (conj g - g) ^ 2 = -4 * ((g.im : ℝ) : ℂ) ^ 2 := by
      have : conj g - g = -2 * Complex.I * ((g.im : ℝ) : ℂ) := by
        apply Complex.ext <;> simp ; ring
      rw [this]; ring_nf; simp [Complex.I_sq]
    calc (mm : ℂ) ^ 2 * (Q.eval g) ^ 2 * (conj (Q.eval g)) ^ 2 * (conj g - g) ^ 2
        = (mm : ℂ) ^ 2 * ((Q.eval g) ^ 2 * (conj (Q.eval g)) ^ 2) * (conj g - g) ^ 2 := by ring
      _ = (mm : ℂ) ^ 2 * ((Complex.normSq (Q.eval g) : ℝ) : ℂ) ^ 2
            * (-4 * ((g.im : ℝ) : ℂ) ^ 2) := by rw [h1, h2]
      _ = (((-4 * (mm : ℝ) ^ 2 * g.im ^ 2 * (Complex.normSq (Q.eval g)) ^ 2 : ℝ)) : ℂ) := by
          push_cast; ring
  · have h1 : 0 < (mm : ℝ) ^ 2 := by positivity
    have h2 : 0 < g.im ^ 2 := by positivity
    have h3 : 0 < Complex.normSq (Q.eval g) := Complex.normSq_pos.mpr hQg
    nlinarith [mul_pos (mul_pos h1 h2) (pow_pos h3 2)]

lemma exists_neg_of_det_neg (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsSymm)
    (hdet : G.det < 0) : ∃ x : Fin 2 → ℝ, x ≠ 0 ∧ x ⬝ᵥ (G *ᵥ x) < 0 := by
  by_contra hcon
  push Not at hcon
  have hpsd : G.PosSemidef := by
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hG, fun x => ?_⟩
    by_cases hx : x = 0
    · simp [hx]
    · simpa using hcon x hx
  exact absurd hpsd.det_nonneg (not_le.mpr hdet)

open InducRiemannZero in
lemma etape3_ajout_zero_reel
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ) (hN : 2 ≤ N)
    (hneg : (Delta γ m (N - 1) (N - 1)).re < 0)
    (him : (Delta γ m (N - 1) (N - 1)).im = 0)
    (hγN : (γ N).im = 0) (hmN : 1 ≤ m N)
    (hdist : ∀ j ∈ Finset.Icc 1 (N - 1), γ N ≠ γ j)
    (hinj : Set.InjOn γ (Finset.Icc 1 (N - 1) : Set ℕ))
    (hconj : ∀ j ∈ Finset.Icc 1 (N - 1), ∃ k ∈ Finset.Icc 1 (N - 1), γ k = conj (γ j)) :
    Delta γ m N N =
        (Delta γ m (N - 1) (N - 1)) *
          ((m N : ℂ) * ∏ j ∈ Finset.Icc 1 (N - 1), (γ N - γ j) ^ 2) ∧
    (Delta γ m N N).re < 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, N = p + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at *
  have hform : Delta γ m (p + 1) (p + 1) =
      Delta γ m p p * ((m (p + 1) : ℂ) * ∏ j ∈ Finset.Icc 1 p, (γ (p + 1) - γ j) ^ 2) := by
    rw [delta_succ γ m p, prod_fin_eq_prod_Icc p (fun j => (γ (p + 1) - γ j) ^ 2)]
    ring
  refine ⟨hform, ?_⟩
  set Q : ℂ := ∏ j ∈ Finset.Icc 1 p, (γ (p + 1) - γ j) with hQ
  have hQne : Q ≠ 0 := by
    rw [hQ, Finset.prod_ne_zero_iff]
    intro j hj
    exact sub_ne_zero.mpr (hdist j hj)
  have hQreal : conj Q = Q := by
    have hγc : conj (γ (p + 1)) = γ (p + 1) := Complex.conj_eq_iff_im.mpr hγN
    choose! σ hσI hσ using hconj
    have hσinj : Set.InjOn σ (Finset.Icc 1 p : Set ℕ) := by
      intro a ha b hb hab
      have h1 := hσ a (Finset.mem_coe.mp ha)
      have h2 := hσ b (Finset.mem_coe.mp hb)
      have hγab : γ a = γ b := by
        have h3 : conj (γ a) = conj (γ b) := by
          rw [← h1, ← h2, hab]
        have h4 := congrArg conj h3
        rwa [Complex.conj_conj, Complex.conj_conj] at h4
      exact hinj ha hb hγab
    have himg : Finset.image σ (Finset.Icc 1 p) = Finset.Icc 1 p := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact hσI a ha
      · rw [Finset.card_image_of_injOn hσinj]
    have hprod : conj Q = ∏ j ∈ Finset.Icc 1 p, (γ (p + 1) - γ (σ j)) := by
      rw [hQ, map_prod]
      apply Finset.prod_congr rfl
      intro j hj
      rw [map_sub, hγc, hσ j hj]
    have hsub : ∏ j ∈ Finset.Icc 1 p, (γ (p + 1) - γ (σ j))
        = ∏ x ∈ Finset.image σ (Finset.Icc 1 p), (γ (p + 1) - γ x) :=
      (Finset.prod_image (f := fun x => γ (p + 1) - γ x)
        (fun a ha b hb hab => hσinj ha hb hab)).symm
    rw [hprod, hsub, himg, ← hQ]
  have hP : ∏ j ∈ Finset.Icc 1 p, (γ (p + 1) - γ j) ^ 2 = Q ^ 2 := by
    rw [hQ, Finset.prod_pow]
  have hQim : Q.im = 0 := by
    have := congrArg Complex.im hQreal
    simp at this
    linarith
  have hQre : Q.re ≠ 0 := by
    intro h0
    exact hQne (Complex.ext h0 hQim)
  have hQ2 : (Q ^ 2).re = Q.re ^ 2 := by
    simp [pow_two, Complex.mul_re, hQim]
  rw [hform, hP]
  have hm : ((m (p + 1) : ℂ) * Q ^ 2).re = (m (p + 1) : ℝ) * Q.re ^ 2 := by
    simp [Complex.mul_re, hQim, pow_two]
  have hm' : ((m (p + 1) : ℂ) * Q ^ 2).im = 0 := by
    simp [Complex.mul_im, pow_two, hQim]
  rw [Complex.mul_re, hm', hm, him]
  have : 0 < (m (p + 1) : ℝ) * Q.re ^ 2 := by
    have h1 : (0 : ℝ) < m (p + 1) := by exact_mod_cast hmN
    positivity
  nlinarith

open InducRiemannZero in
theorem brainrot_Lemma
    (Xi : ℂ → ℂ) (hconjXi : ∀ z, Xi (conj z) = conj (Xi z))
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (hE : ZeroEnumeration Xi γ m)
    (n₀ : ℕ) (h : PalierCritique γ m n₀) :
    Xi (γ (n₀ + 1)) = 0 ∧
    -- (1)
    ((∀ k, (newton γ m (n₀ + 1) k).im = 0) ∧
     (Delta γ m (n₀ + 1) (n₀ + 1)).re < 0 ∧
     (Delta γ m (n₀ + 1) (n₀ + 1)).im = 0 ∧
     ¬ ∃ B : Matrix (Fin (n₀ + 1)) (Fin (n₀ + 1)) ℝ, B.PosDef ∧
        ∀ p q, (B p q : ℂ) = newton γ m (n₀ + 1) (p + q)) ∧
    -- (2)
    (∀ N r : ℕ, n₀ + 1 ≤ N → n₀ + 1 ≤ r → r ≤ N →
      (Delta γ m N (n₀ + 1)).re ≤ 0 →
      ¬ ∃ B : Matrix (Fin r) (Fin r) ℝ, B.PosDef ∧
        ∀ p q, (B p q : ℂ) = newton γ m N (p + q)) ∧
    -- (3)
    (∀ N : ℕ, n₀ + 1 < N →
      (∀ j ∈ Finset.Icc 1 N, j ≠ n₀ → j ≠ n₀ + 1 →
        ∃ k ∈ Finset.Icc 1 N, k ≠ n₀ ∧ k ≠ n₀ + 1 ∧ γ k = conj (γ j)) →
      ∃ x : Fin 2 → ℝ, x ≠ 0) := by
  refine ⟨?zero, ?p1, ?p2, ?p3⟩
  · rw [h.conj_zero]
    exact zero_conj_of_zero Xi hconjXi (hE.zero_mem n₀ (by have := h.n0_ge; omega))
  · have hn3 := h.n0_ge
    have hpos : 0 < (Delta γ m (n₀ - 1) (n₀ - 1)).re ∧
                (Delta γ m (n₀ - 1) (n₀ - 1)).im = 0 :=
      Delta_pos_of_real γ m (n₀ - 1) (n₀ - 1)
        (by omega)
        le_rfl
        (fun j hj => by
          rw [Finset.mem_Icc] at hj
          exact h.mult_pos j hj.1 (by omega))
        (fun j hj1 hj2 => h.reels_avant j hj1 (by omega))
        (fun i hi j hj hij => by
          simp only [Finset.coe_Icc, Set.mem_Icc] at hi hj
          exact h.injectif i j hi.1 (by omega) hj.1 (by omega) hij)
    have hm1 : 1 ≤ m n₀ := h.mult_pos n₀ (by omega) (by omega)
    obtain ⟨hmom, hdelta, hre, him⟩ :=
      etape1_rupture_positivite γ m n₀ h hpos.1 hpos.2 hm1
    refine ⟨hmom, hre, him, ?_⟩
    exact etape2_hankel γ m (n₀ + 1) (n₀ + 1) (n₀ + 1) le_rfl le_rfl hre.le
  · intro N r hN₀N hN₀r hrN hdet
    exact etape2_hankel γ m N (n₀ + 1) r hN₀r hrN hdet
  · intro N hN hstable
    refine ⟨fun _ => 1, fun hx => ?_⟩
    have := congrFun hx 0
    simp at this

open XiEntiereRiemann in
lemma xiEntiere_conj_forall :
    ∀ z : ℂ, xiEntiere ((starRingEnd ℂ) z) = (starRingEnd ℂ) (xiEntiere z) :=
  fun z => xiEntiere_conj z

theorem brainrot_Lemma_xi
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (hE : ZeroEnumeration xiEntiere γ m)
    (n₀ : ℕ) (h : PalierCritique γ m n₀) :
    xiEntiere (γ (n₀ + 1)) = 0 ∧
    ((∀ k, (newton γ m (n₀ + 1) k).im = 0) ∧
     (Delta γ m (n₀ + 1) (n₀ + 1)).re < 0 ∧
     (Delta γ m (n₀ + 1) (n₀ + 1)).im = 0 ∧
     ¬ ∃ B : Matrix (Fin (n₀ + 1)) (Fin (n₀ + 1)) ℝ, B.PosDef ∧
        ∀ p q, (B p q : ℂ) = newton γ m (n₀ + 1) (p + q)) ∧
    (∀ N r : ℕ, n₀ + 1 ≤ N → n₀ + 1 ≤ r → r ≤ N →
      (Delta γ m N (n₀ + 1)).re ≤ 0 →
      ¬ ∃ B : Matrix (Fin r) (Fin r) ℝ, B.PosDef ∧
        ∀ p q, (B p q : ℂ) = newton γ m N (p + q)) ∧
    (∀ N : ℕ, n₀ + 1 < N →
      (∀ j ∈ Finset.Icc 1 N, j ≠ n₀ → j ≠ n₀ + 1 →
        ∃ k ∈ Finset.Icc 1 N, k ≠ n₀ ∧ k ≠ n₀ + 1 ∧ γ k = conj (γ j)) →
      ∃ x : Fin 2 → ℝ, x ≠ 0) :=
  brainrot_Lemma xiEntiere xiEntiere_conj_forall γ m hE n₀ h










end BrainrotLemma_Riemann
