import mathlib


/-! -/
namespace SylvesterCrit

open Set Complex Matrix
open scoped ComplexOrder

lemma posDef_minor_pos' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (r : ℕ) (hr : r ≤ n) :
    0 < (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).det :=
  (hA.submatrix (Fin.castLE_injective hr)).det_pos

lemma det_eq_schur {p : ℕ} (A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ)
    (hsymm : A.IsSymm)
    (hinv : IsUnit (A.submatrix Fin.castSucc Fin.castSucc).det) :
    A.det = (A.submatrix Fin.castSucc Fin.castSucc).det *
      (A (Fin.last p) (Fin.last p) -
        (fun i : Fin p => A (Fin.castSucc i) (Fin.last p)) ⬝ᵥ
          ((A.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
            (fun i : Fin p => A (Fin.castSucc i) (Fin.last p)))) := by
  set A' := A.submatrix Fin.castSucc Fin.castSucc with hA'
  set b : Fin p → ℝ := fun i => A (Fin.castSucc i) (Fin.last p) with hb
  set c : ℝ := A (Fin.last p) (Fin.last p) with hc
  have _ : Invertible A' := Matrix.invertibleOfIsUnitDet A' hinv
  have hrow : (fun j : Fin p => A (Fin.last p) (Fin.castSucc j)) = b := by
    funext j
    have := congrFun (congrFun hsymm (Fin.castSucc j)) (Fin.last p)
    simpa [Matrix.transpose_apply, hb] using this
  set M : Matrix (Fin p ⊕ Fin 1) (Fin p ⊕ Fin 1) ℝ :=
    Matrix.fromBlocks A' (Matrix.replicateCol (Fin 1) b) (Matrix.replicateRow (Fin 1) b)
      (Matrix.of fun _ _ => c)
    with hM
  have hAeq : A = Matrix.reindex finSumFinEquiv finSumFinEquiv M := by
    ext i j
    refine Fin.lastCases ?_ (fun i' => ?_) i <;>
      refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp [hM, hc, Matrix.reindex_apply, Matrix.submatrix_apply]
    · have h := congrFun hrow j'
      simp [hM, Matrix.reindex_apply, Matrix.submatrix_apply, h]
    · simp [hM, hb, Matrix.reindex_apply, Matrix.submatrix_apply]
    · simp [hM, hA', Matrix.reindex_apply, Matrix.submatrix_apply]
  have hdetM : A.det = M.det := by
    rw [hAeq, Matrix.det_reindex_self]
  rw [hdetM, hM, Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique]
  simp only [Fin.default_eq_zero, Matrix.sub_apply, Matrix.of_apply, sub_right_inj]
  simp only [invOf_eq_nonsing_inv, Fin.isValue, Matrix.mul_apply, dotProduct, Matrix.mulVec,
    hb, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm


lemma quad_form_split {p : ℕ} (A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ)
    (hsymm : A.IsSymm)
    (hinv : IsUnit (A.submatrix Fin.castSucc Fin.castSucc).det)
    (x : Fin (p + 1) → ℝ) :
    x ⬝ᵥ (A *ᵥ x) =
      (fun i : Fin p => x (Fin.castSucc i) +
          x (Fin.last p) * ((A.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
            (fun j : Fin p => A (Fin.castSucc j) (Fin.last p))) i) ⬝ᵥ
        ((A.submatrix Fin.castSucc Fin.castSucc) *ᵥ
          (fun i : Fin p => x (Fin.castSucc i) +
            x (Fin.last p) * ((A.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
              (fun j : Fin p => A (Fin.castSucc j) (Fin.last p))) i)) +
      x (Fin.last p) ^ 2 *
        (A (Fin.last p) (Fin.last p) -
          (fun i : Fin p => A (Fin.castSucc i) (Fin.last p)) ⬝ᵥ
            ((A.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
              (fun i : Fin p => A (Fin.castSucc i) (Fin.last p)))) := by
  set A' := A.submatrix Fin.castSucc Fin.castSucc with hA'
  set b : Fin p → ℝ := fun i => A (Fin.castSucc i) (Fin.last p) with hb
  set c : ℝ := A (Fin.last p) (Fin.last p) with hc
  set y : Fin p → ℝ := fun i => x (Fin.castSucc i) with hy
  set t : ℝ := x (Fin.last p) with ht
  set w : Fin p → ℝ := A'⁻¹ *ᵥ b with hw
  have _ : Invertible A' := Matrix.invertibleOfIsUnitDet A' hinv
  have hA'symm : A'.IsSymm := by
    ext i j
    simpa [hA', Matrix.transpose_apply] using
      (congrFun (congrFun hsymm (Fin.castSucc j)) (Fin.castSucc i)).symm
  have hrow : (fun j : Fin p => A (Fin.last p) (Fin.castSucc j)) = b := by
    funext j
    have := congrFun (congrFun hsymm (Fin.castSucc j)) (Fin.last p)
    simpa [Matrix.transpose_apply, hb] using this
  have hAw : A' *ᵥ w = b := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A' hinv, Matrix.one_mulVec]
  have hsplit : x ⬝ᵥ (A *ᵥ x) =
      y ⬝ᵥ (A' *ᵥ y) + t * (b ⬝ᵥ y) + t * (b ⬝ᵥ y) + t ^ 2 * c := by
    have hrow' : ∀ i : Fin p, A (Fin.last p) (Fin.castSucc i) = b i :=
      fun i => congrFun hrow i
    have h1 : ∑ i : Fin p, x i.castSucc * ∑ k : Fin p, A i.castSucc k.castSucc * x k.castSucc
        = y ⬝ᵥ (A' *ᵥ y) := by
      simp [dotProduct, Matrix.mulVec, hA', hy]
    have h2 : ∑ i : Fin p, x i.castSucc * (A i.castSucc (Fin.last p) * t) = t * (b ⬝ᵥ y) := by
      simp only [dotProduct, hb, hy, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have h3 : t * ∑ i : Fin p, A (Fin.last p) i.castSucc * x i.castSucc = t * (b ⬝ᵥ y) := by
      simp only [dotProduct, hrow', hy]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc, mul_add,
      Finset.sum_add_distrib]
    rw [h1, h2]
    have h3'' : x (Fin.last p) * ∑ i : Fin p, A (Fin.last p) i.castSucc * x i.castSucc
        = t * ∑ i : Fin p, b i * y i := by
      simp only [hrow', hy, ht]
    rw [h3'']
    simp only [dotProduct, Matrix.mulVec]
    have hc' : x (Fin.last p) * (A (Fin.last p) (Fin.last p) * x (Fin.last p)) = t ^ 2 * c := by
      simp only [ht, hc]; ring
    rw [hc']
    ring
  have hsq : (y + t • w) ⬝ᵥ (A' *ᵥ (y + t • w)) =
      y ⬝ᵥ (A' *ᵥ y) + 2 * t * (b ⬝ᵥ y) + t ^ 2 * (b ⬝ᵥ w) := by
    have hsw : w ⬝ᵥ (A' *ᵥ y) = b ⬝ᵥ y := by
      rw [dotProduct_mulVec]
      have h := Matrix.vecMul_transpose A' w
      rw [hA'symm.eq] at h
      rw [h, hAw]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hAw, dotProduct_add, add_dotProduct,
      add_dotProduct, smul_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_smul]
    rw [hsw, dotProduct_comm y b, dotProduct_comm w b]
    simp only [smul_eq_mul]
    ring
  change x ⬝ᵥ (A *ᵥ x) = (y + t • w) ⬝ᵥ (A' *ᵥ (y + t • w)) + t ^ 2 * (c - b ⬝ᵥ w)
  rw [hsplit, hsq]
  ring

lemma posDef_of_block_posDef_of_det_pos {p : ℕ}
    (A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℝ) (hsymm : A.IsSymm)
    (hA' : (A.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hdet : 0 < A.det) :
    A.PosDef := by
  set A' := A.submatrix Fin.castSucc Fin.castSucc with hA'def
  set b : Fin p → ℝ := fun i => A (Fin.castSucc i) (Fin.last p) with hbdef
  set w : Fin p → ℝ := A'⁻¹ *ᵥ b with hwdef
  set s : ℝ := A (Fin.last p) (Fin.last p) - b ⬝ᵥ w with hsdef
  have hdet' : 0 < A'.det := hA'.det_pos
  have hinv : IsUnit A'.det := (hdet'.ne').isUnit
  have hs : 0 < s := by
    have h := det_eq_schur A hsymm hinv
    have h2 : 0 < A'.det * s := by rw [← h]; exact hdet
    exact (mul_pos_iff_of_pos_left hdet').mp h2
  have hherm : A.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hherm, ?_⟩
  intro x hx
  simp only [star_trivial]
  rw [quad_form_split A hsymm hinv x]
  set y' : Fin p → ℝ := fun i => x (Fin.castSucc i) + x (Fin.last p) * w i with hy'
  by_cases hy : y' = 0
  · have ht : x (Fin.last p) ≠ 0 := by
      intro ht
      apply hx
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using ht
      · have := congrFun hy j
        simpa [hy', ht] using this
    have h1 : 0 ≤ y' ⬝ᵥ (A' *ᵥ y') := by rw [hy]; simp
    have h2 : 0 < x (Fin.last p) ^ 2 * s := by positivity
    exact add_pos_of_nonneg_of_pos h1 h2
  · have h1 : 0 < y' ⬝ᵥ (A' *ᵥ y') := by
      have := hA'.dotProduct_mulVec_pos hy
      simpa [star_trivial] using this
    have h2 : 0 ≤ x (Fin.last p) ^ 2 * s := by positivity
    exact add_pos_of_pos_of_nonneg h1 h2

lemma posDef_of_leading_minors {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : H.IsSymm)
    (hminors : ∀ r : ℕ, (hr : r ≤ n) → 0 < (H.submatrix
      (Fin.castLE hr) (Fin.castLE hr)).det) :
    H.PosDef := by
  induction n with
  | zero =>
    refine ⟨hsymm, ?_⟩
    intro x hx
    exact absurd (Subsingleton.elim x 0) hx
  | succ p ih =>
    have hsymm' : (H.submatrix Fin.castSucc Fin.castSucc).IsSymm := by
      ext i j
      simpa using congrFun (congrFun hsymm (Fin.castSucc i)) (Fin.castSucc j)
    have hminors' : ∀ r : ℕ, (hr : r ≤ p) → 0 < ((H.submatrix Fin.castSucc Fin.castSucc).submatrix
        (Fin.castLE hr) (Fin.castLE hr)).det := by
      intro r hr
      have := hminors r (by omega)
      simpa [Matrix.submatrix_submatrix, Function.comp_def] using this
    have hA' := ih (H.submatrix Fin.castSucc Fin.castSucc) hsymm' hminors'
    have hdet : 0 < H.det := by
      have := hminors (p + 1) le_rfl
      simpa using this
    exact posDef_of_block_posDef_of_det_pos H hsymm hA' hdet

lemma Sylvester_minor_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (r : ℕ) (hr : r ≤ n) :
    0 < (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).det :=
  posDef_minor_pos' A hA r hr

theorem Sylvester_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : A.IsSymm)
    (hminors : ∀ r (hr : r ≤ n), 0 < (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).det) :
    A.PosDef :=
  posDef_of_leading_minors A hsymm hminors

theorem Sylvester_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hsymm : A.IsSymm) :
    A.PosDef ↔ ∀ r : ℕ, (hr : r ≤ n) →
      0 < (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).det :=
  ⟨fun hA r hr => posDef_minor_pos' A hA r hr,
   fun h => posDef_of_leading_minors A hsymm h⟩


end SylvesterCrit
