import mathlib
import ThEqRiemann.EqTheorem.DefThEq

/-! -/
namespace VandermondeThEq

open Set Matrix Complex DefinitionsThEq


lemma diagPoids_diag_eq {K : ℕ} (w : Fin K → ℤ) (a : Fin K) :
    diagPoids w a a = (w a : ℂ) := by
  simp only [diagPoids, Matrix.diagonal_apply_eq]

lemma diagPoids_ne_eq {K : ℕ} (w : Fin K → ℤ)
  (a b : Fin K) (hab : a ≠ b) :
    diagPoids w a b = 0 := by
  simp only [diagPoids, Matrix.diagonal_apply]
  split_ifs with h
  · -- Cas a = b, contredit hab
    exact absurd h hab
  · -- Cas a ≠ b, résultat = 0
    rfl

lemma vand_diag_apply {K : ℕ}
  (lam : Fin K → ℂ) (w : Fin K → ℤ) (i a : Fin K) :
    (vandermonde' lam * diagPoids w) i a = vandermonde'
      lam i a * (w a : ℂ) := by
  rw [Matrix.mul_apply]
  simp only [diagPoids, Matrix.diagonal_apply, mul_ite, mul_zero]
  simp_rw [Finset.sum_ite]
  simp only [Finset.filter_eq']
  by_cases h : a ∈ Finset.univ
  · simp [h]
  · simp at h

lemma vand_transpose_apply {K : ℕ} (lam : Fin K → ℂ) (a j : Fin K) :
    (vandermonde' lam).transpose a j = lam a ^ (j : ℕ) := by
  simp only [Matrix.transpose_apply, vandermonde']


lemma diag_vand_transpose_apply {K : ℕ}
  (lam : Fin K → ℂ) (w : Fin K → ℤ) (a j : Fin K) :
    (diagPoids w * (vandermonde' lam).transpose) a j =
      (w a : ℂ) * (lam a ^ (j : ℕ)) := by
  rw [Matrix.mul_apply]
  simp only [diagPoids, Matrix.diagonal_apply]
  simp_rw [ite_mul]
  simp only [zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true,
    Matrix.transpose_apply, vandermonde']


lemma vand_diag_transpose_expanded {K : ℕ}
  (lam : Fin K → ℂ) (w : Fin K → ℤ) (i j : Fin K) :
    (vandermonde' lam * diagPoids w *
      (vandermonde' lam).transpose) i j
      = ∑ a : Fin K, vandermonde' lam i a * (w a : ℂ) *
        (lam a ^ (j : ℕ)) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [diag_vand_transpose_apply]
  ring

lemma lam_pow_combine {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (a i j : Fin K) :
    vandermonde' lam i a * ((w a : ℂ) * lam a ^ (j : ℕ))
      = (w a : ℂ) * (lam a ^ (i : ℕ) * lam a ^ (j : ℕ)) := by
  simp only [vandermonde']
  ring

lemma vandermonde_diag_transpose_apply
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (i j : Fin K) :
    (vandermonde' lam * diagPoids w * (vandermonde' lam).transpose) i j
      = ∑ r : Fin K, (w r : ℂ) * (lam r) ^ (i : ℕ) * (lam r) ^ (j : ℕ) := by
  rw [vand_diag_transpose_expanded]
  apply Finset.sum_congr rfl
  intro r _
  simp only [vandermonde']
  ring

lemma vandermonde_diag_transpose_apply_pow
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (i j : Fin K) :
    (vandermonde' lam * diagPoids w * (vandermonde' lam).transpose) i j
      = ∑ r : Fin K, (w r : ℂ) * (lam r) ^ ((i : ℕ) + (j : ℕ)) := by
  rw [vandermonde_diag_transpose_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [pow_add]
  ring

-----------------------------------------------------------------------------



lemma factorisation_hankel
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) :
    hankel0 lam w = vandermonde' lam * diagPoids w * (vandermonde' lam).transpose := by
  ext i j
  calc hankel0 lam w i j
      = ∑ r : Fin K, (w r : ℂ) * (lam r) ^ ((i : ℕ) + (j : ℕ)) := rfl
    _ = (vandermonde' lam * diagPoids w * (vandermonde' lam).transpose) i j :=
        (vandermonde_diag_transpose_apply_pow lam w i j).symm


-----------------------------------------------------------------------------

lemma vandermonde'_eq_transpose_vandermonde
    {K : ℕ} (lam : Fin K → ℂ) :
    vandermonde' lam = (Matrix.vandermonde lam).transpose := by
  ext i r
  rfl

lemma det_vandermonde'_eq_prod
    {K : ℕ} (lam : Fin K → ℂ) :
    (vandermonde' lam).det =
      ∏ a : Fin K, ∏ b ∈ Finset.Ioi a, (lam b - lam a) := by
  rw [vandermonde'_eq_transpose_vandermonde, Matrix.det_transpose]
  exact Matrix.det_vandermonde lam


lemma det_vandermonde'_ne_zero
    {K : ℕ} (lam : Fin K → ℂ)
    (hlam : Function.Injective lam) :
    (vandermonde' lam).det ≠ 0 := by
  rw [vandermonde'_eq_transpose_vandermonde, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr hlam


lemma vandermonde_prod_ne_zero
    {K : ℕ} (lam : Fin K → ℂ)
    (hlam : Function.Injective lam) :
    (∏ a : Fin K, ∏ b ∈ Finset.Ioi a, (lam b - lam a)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun a _ =>
    Finset.prod_ne_zero_iff.mpr fun b hb => ?_
  have hlt : a < b := Finset.mem_Ioi.mp hb
  exact sub_ne_zero.mpr (fun h => hlt.ne' (hlam h))


lemma det_diagPoids_eq_prod
    {K : ℕ} (w : Fin K → ℤ) :
    (diagPoids w).det = ∏ r : Fin K, (w r : ℂ) := by
  simp only [diagPoids, Matrix.det_diagonal]

lemma det_diagPoids_ne_zero
    {K : ℕ} (w : Fin K → ℤ) (hw : ∀ r : Fin K, w r ≠ 0) :
    (diagPoids w).det ≠ 0 := by
  rw [det_diagPoids_eq_prod]
  exact Finset.prod_ne_zero_iff.mpr fun r _ =>
    Int.cast_ne_zero.mpr (hw r)


lemma det_hankel0_eq_sq_mul
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) :
    (hankel0 lam w).det =
      (vandermonde' lam).det ^ 2 * (diagPoids w).det := by
  rw [factorisation_hankel, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

lemma hankel0_det_ne_zero
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam) (hw : ∀ r : Fin K, w r ≠ 0) :
    (hankel0 lam w).det ≠ 0 := by
  rw [det_hankel0_eq_sq_mul]
  exact mul_ne_zero (pow_ne_zero 2 (det_vandermonde'_ne_zero lam hlam))
    (det_diagPoids_ne_zero w hw)

lemma isUnit_hankel0
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam) (hw : ∀ r : Fin K, w r ≠ 0) :
    IsUnit (hankel0 lam w) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr
    (hankel0_det_ne_zero lam w hlam hw).isUnit

@[instance_reducible]
noncomputable def hankel0_invertible
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam) (hw : ∀ r : Fin K, w r ≠ 0) :
    Invertible (hankel0 lam w) :=
  Matrix.invertibleOfIsUnitDet (hankel0 lam w)
    (isUnit_iff_ne_zero.mpr (hankel0_det_ne_zero lam w hlam hw))


lemma hankelOfMoments_eq_hankel0
    {K : ℕ} (mu : ℕ → ℂ) (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hmu : ∀ k : ℕ, mu k = ∑ r : Fin K, (w r : ℂ) * (lam r) ^ k) :
    hankelOfMoments K mu = hankel0 lam w := by
  ext i j
  simp only [hankelOfMoments, hankel0]
  exact hmu (i.1 + j.1)

@[instance_reducible]
noncomputable def hankelOfMoments_invertible
    {K : ℕ} (mu : ℕ → ℂ) (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam)
    (hw : ∀ r : Fin K, w r ≠ 0)
    (hmu : ∀ k : ℕ, mu k = ∑ r : Fin K, (w r : ℂ) * (lam r) ^ k) :
    Invertible (hankelOfMoments K mu) := by
  rw [hankelOfMoments_eq_hankel0 mu lam w hmu]
  exact hankel0_invertible lam w hlam hw

-----------------------------------------------------------------------

lemma vandermonde_inj_zero (D : ℕ) (pts : Fin D → ℝ) (hinj : Function.Injective pts) :
    ∀ v : Fin D → ℝ, (∀ l : Fin D, ∑ i, v i * pts i ^ (l : ℕ) = 0) → v = 0 := by
  intro v hv
  have hdet : (Matrix.vandermonde pts).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hmul : (Matrix.vandermonde pts).transpose.mulVec v = 0 := by
    funext l
    simpa [Matrix.mulVec, dotProduct, Matrix.vandermonde, mul_comm] using hv l
  have hdetT : (Matrix.vandermonde pts).transpose.det ≠ 0 := by
    rwa [Matrix.det_transpose]
  exact Matrix.eq_zero_of_mulVec_eq_zero hdetT hmul

lemma vandermonde_zero_of_roots_complex (D : ℕ) (pts : Fin D → ℝ)
    (hinj : Function.Injective pts) (x : Fin D → ℂ)
    (hx : ∀ i, ∑ j : Fin D, x j * (pts i : ℂ) ^ (j : ℕ) = 0) : x = 0 := by
  classical
  set v : Fin D → ℂ := fun i => (pts i : ℂ) with hv
  have hvinj : Function.Injective v := by
    intro a b hab
    exact hinj (Complex.ofReal_injective hab)
  have hdet : (Matrix.vandermonde v).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hvinj
  apply Matrix.eq_zero_of_mulVec_eq_zero hdet
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
  rw [← hx i]
  exact Finset.sum_congr rfl (fun j _ => by rw [mul_comm])

------------------------------------------------------------------------

lemma det_vandermonde_snoc (n : ℕ) (v : Fin n → ℂ) (x : ℂ) :
    (Matrix.vandermonde (Fin.snoc v x : Fin (n + 1) → ℂ)).det =
      (Matrix.vandermonde v).det * ∏ k : Fin n, (x - v k) := by
  rw [Matrix.det_vandermonde, Matrix.det_vandermonde]
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ j ∈ Finset.Ioi (Fin.last n),
      ((Fin.snoc v x : Fin (n + 1) → ℂ) j - (Fin.snoc v x : Fin (n + 1) → ℂ) (Fin.last n)) = 1 := by
    have : Finset.Ioi (Fin.last n) = ∅ := by
      ext j
      simp [not_lt.mpr (Fin.le_last j)]
    rw [this]; simp
  rw [hlast, mul_one]
  have hcast : ∀ i : Fin n,
      ∏ j ∈ Finset.Ioi i.castSucc,
        ((Fin.snoc v x : Fin (n + 1) → ℂ) j - (Fin.snoc v x : Fin (n + 1) → ℂ) i.castSucc) =
      (∏ j ∈ Finset.Ioi i, (v j - v i)) * (x - v i) := by
    intro i
    have hsplit : Finset.Ioi i.castSucc =
        insert (Fin.last n) ((Finset.Ioi i).map Fin.castSuccEmb) := by
      ext j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · simp [Fin.castSucc_lt_last]
      · simp only [Finset.mem_Ioi, Fin.castSucc_lt_castSucc_iff, Fin.map_castSuccEmb_Ioi,
          Fin.castSucc_lt_last, Finset.Ioo_insert_right, Finset.mem_Ioc, iff_self_and]
        intro _
        exact Fin.le_last _
    rw [hsplit, Finset.prod_insert (by simp), Finset.prod_map]
    simp [Fin.snoc_castSucc, Fin.snoc_last, mul_comm]
  simp_rw [hcast]
  rw [Finset.prod_mul_distrib]

lemma vandermonde_conjugue_carre (n : ℕ) (τ : Fin n → ℝ) (τn σn : ℝ) :
    (Matrix.vandermonde
        (Fin.snoc (Fin.snoc (fun k => (τ k : ℂ)) ((τn : ℂ) - σn * Complex.I))
          ((τn : ℂ) + σn * Complex.I))).det ^ 2 =
      (Matrix.vandermonde (fun k => (τ k : ℂ))).det ^ 2 * (-(4 * σn ^ 2 : ℝ) : ℂ) *
        ∏ k : Fin n, (((τn - τ k) ^ 2 + σn ^ 2 : ℝ) : ℂ) ^ 2 := by
  rw [det_vandermonde_snoc, det_vandermonde_snoc]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hfac : ∀ k : Fin n,
      ((τn : ℂ) - σn * Complex.I - τ k) * ((τn : ℂ) + σn * Complex.I - τ k) =
      (((τn - τ k) ^ 2 + σn ^ 2 : ℝ) : ℂ) := by
    intro k
    push_cast
    ring_nf
    simp [Complex.I_sq]
  have hprod : (∏ k : Fin n, ((τn : ℂ) - σn * Complex.I - τ k)) *
      (∏ k : Fin n, ((τn : ℂ) + σn * Complex.I - τ k)) =
      ∏ k : Fin n, (((τn - τ k) ^ 2 + σn ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun k _ => hfac k)
  have hdiff : ((τn : ℂ) + σn * Complex.I - ((τn : ℂ) - σn * Complex.I)) ^ 2 =
      (-(4 * σn ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring_nf
    simp [Complex.I_sq]
  calc _ = ((Matrix.vandermonde (fun k => (τ k : ℂ))).det) ^ 2 *
        ((τn : ℂ) + σn * Complex.I - ((τn : ℂ) - σn * Complex.I)) ^ 2 *
        ((∏ k : Fin n, ((τn : ℂ) - σn * Complex.I - τ k)) *
          (∏ k : Fin n, ((τn : ℂ) + σn * Complex.I - τ k))) ^ 2 := by ring
    _ = _ := by
      rw [hprod, hdiff, Finset.prod_pow]




lemma det_hn1_eq_vandermonde_carre (k : ℕ) (τ : Fin (k + 2) → ℝ) (τn σn : ℝ) :
    let γn : ℂ := (τn : ℂ) - (σn : ℂ) * Complex.I
    let Hn1 : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ :=
      Matrix.of fun i j =>
        ∑ l : Fin (k + 2), τ l ^ ((i : ℕ) + j) +
          ((γn ^ ((i : ℕ) + j) + (starRingEnd ℂ γn) ^ ((i : ℕ) + j) : ℂ)).re
    (Hn1.det : ℂ) =
      (Matrix.vandermonde
        (Fin.snoc (Fin.snoc (fun j => (τ j : ℂ)) ((τn : ℂ) - σn * Complex.I))
          ((τn : ℂ) + σn * Complex.I))).det ^ 2 := by
  intro γn Hn1
  set z : Fin (k + 4) → ℂ :=
    Fin.snoc (Fin.snoc (fun j => (τ j : ℂ)) ((τn : ℂ) - σn * Complex.I))
      ((τn : ℂ) + σn * Complex.I) with hz
  have h1 : (Hn1.det : ℂ) = (Hn1.map (algebraMap ℝ ℂ)).det := by
    simpa using (RingHom.map_det (algebraMap ℝ ℂ) Hn1)
  have h2 : Hn1.map (algebraMap ℝ ℂ) = (Matrix.vandermonde z)ᵀ * Matrix.vandermonde z := by
    ext i j
    have hR : ((Matrix.vandermonde z)ᵀ * Matrix.vandermonde z) i j
        = ∑ l : Fin (k + 4), z l ^ ((i : ℕ) + (j : ℕ)) := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.vandermonde_apply]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [pow_add]
    rw [hR]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [hz, Fin.snoc_castSucc, Fin.snoc_last]
    have hreel : ((γn ^ ((i : ℕ) + (j : ℕ)) + (starRingEnd ℂ γn) ^ ((i : ℕ) + (j : ℕ)) : ℂ).re : ℂ)
        = γn ^ ((i : ℕ) + (j : ℕ)) + (starRingEnd ℂ γn) ^ ((i : ℕ) + (j : ℕ)) := by
      have hc : (starRingEnd ℂ) (γn ^ ((i : ℕ) + (j : ℕ)) +
        (starRingEnd ℂ γn) ^ ((i : ℕ) + (j : ℕ)))
          = γn ^ ((i : ℕ) + (j : ℕ)) + (starRingEnd ℂ γn) ^ ((i : ℕ) + (j : ℕ)) := by
        simp [map_add, map_pow, add_comm]
      exact (Complex.conj_eq_iff_re.mp hc)
    simp only [Matrix.map_apply, Hn1, Matrix.of_apply]
    rw [Complex.coe_algebraMap, Complex.ofReal_add, Complex.ofReal_sum]
    simp only [Complex.ofReal_pow]
    rw [hreel]
    have hγc : (starRingEnd ℂ) γn = (τn : ℂ) + (σn : ℂ) * Complex.I := by
      simp [γn, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [hγc]
    simp only [γn]
    ring
  rw [h1, h2, Matrix.det_mul, Matrix.det_transpose, sq]


lemma vandermonde_carre_eq_delta (m : ℕ) (τ : Fin m → ℝ) :
    (Matrix.vandermonde (fun k => (τ k : ℂ))).det ^ 2 =
      ((∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_vandermonde, ← Finset.prod_pow]
  push_cast
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Finset.prod_pow]

theorem det_hankel_vandermonde {n : ℕ} (τ : Fin n → ℝ) :
    (Matrix.of fun (i j : Fin n) => ∑ k : Fin n, (τ k) ^ ((i : ℕ) + j)).det =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2 := by
  have h : (Matrix.of fun (i j : Fin n) => ∑ k : Fin n, (τ k) ^ ((i : ℕ) + j)) =
      (Matrix.vandermonde τ)ᵀ * Matrix.vandermonde τ := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vandermonde, pow_add]
  rw [h, Matrix.det_mul, Matrix.det_transpose, Matrix.det_vandermonde, ← sq,
      ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_pow]

lemma vandermonde_prod_succ (f : ℕ → ℂ) (n : ℕ) :
    (∏ i : Fin (n + 1), ∏ j ∈ Finset.Ioi i, (f (j : ℕ) - f (i : ℕ))) =
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (f (j : ℕ) - f (i : ℕ))) *
      ∏ j : Fin n, (f n - f (j : ℕ)) := by
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ j ∈ Finset.Ioi (Fin.last n),
  (f (j : ℕ) - f ((Fin.last n : Fin (n+1)) : ℕ)) = 1 := by
    have : Finset.Ioi (Fin.last n) = ∅ := by
      ext j
      simp [not_lt.mpr (Fin.le_last j)]
    rw [this]; simp
  rw [hlast, mul_one]
  have hcast : ∀ i : Fin n,
      ∏ j ∈ Finset.Ioi i.castSucc, (f (j : ℕ) - f ((i.castSucc : Fin (n+1)) : ℕ)) =
      (∏ j ∈ Finset.Ioi i, (f (j : ℕ) - f (i : ℕ))) * (f n - f (i : ℕ)) := by
    intro i
    have hsplit : Finset.Ioi i.castSucc =
        insert (Fin.last n) ((Finset.Ioi i).map Fin.castSuccEmb) := by
      ext j
      refine Fin.lastCases ?_ (fun j' => ?_) j
      · simp [Fin.castSucc_lt_last]
      · simp only [Finset.mem_Ioi, Fin.castSucc_lt_castSucc_iff, Fin.map_castSuccEmb_Ioi,
          Fin.castSucc_lt_last, Finset.Ioo_insert_right, Finset.mem_Ioc, iff_self_and]
        intro _
        exact Fin.le_last _
    rw [hsplit, Finset.prod_insert (by simp), Finset.prod_map]
    simp [mul_comm]
  simp_rw [hcast]
  rw [Finset.prod_mul_distrib]

lemma vandermonde_split (γ : ℕ → ℂ) (p : ℕ) :
    (∏ i : Fin (p + 2), ∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) =
      (∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) *
      (∏ j : Fin p, (γ (p + 1) - γ ((j : ℕ) + 1)) * (γ (p + 2) - γ ((j : ℕ) + 1))) *
      (γ (p + 2) - γ (p + 1)) := by
  set f : ℕ → ℂ := fun k => γ (k + 1) with hf
  have h1 := vandermonde_prod_succ f (p + 1)
  have h2 := vandermonde_prod_succ f p
  simp only [hf] at h1 h2
  rw [h1, h2, Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [Finset.prod_mul_distrib]
  ring

lemma prod_Ioi_castSucc (γ : ℕ → ℂ) (p : ℕ) (i : Fin p) :
    (∏ j ∈ Finset.Ioi (Fin.castSucc i), (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) =
      (∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) *
        (γ (p + 1) - γ ((i : ℕ) + 1)) := by
  have hset : Finset.Ioi (Fin.castSucc i) =
      insert (Fin.last p) ((Finset.Ioi i).map Fin.castSuccEmb) := by
    ext j
    simp only [Finset.mem_Ioi, Finset.mem_insert, Finset.mem_map, Fin.coe_castSuccEmb]
    constructor
    · intro hj
      rcases Fin.eq_castSucc_or_eq_last j with ⟨k, rfl⟩ | rfl
      · right
        exact ⟨k, by simpa using hj, rfl⟩
      · left
        rfl
    · rintro (rfl | ⟨k, hk, rfl⟩)
      · exact Fin.castSucc_lt_last i
      · simpa using hk
  have hnot : Fin.last p ∉ (Finset.Ioi i).map Fin.castSuccEmb := by
    simp only [Finset.mem_map, not_exists, not_and]
    intro k _ hk
    exact absurd hk (Fin.castSucc_lt_last k).ne
  rw [hset, Finset.prod_insert hnot, Finset.prod_map]
  simp [mul_comm]

lemma vandermonde_succ (γ : ℕ → ℂ) (p : ℕ) :
    (∏ i : Fin (p + 1), ∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) =
      (∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) *
        ∏ i : Fin p, (γ (p + 1) - γ ((i : ℕ) + 1)) := by
  rw [Fin.prod_univ_castSucc]
  have hlast : (∏ j ∈ Finset.Ioi (Fin.last p),
      (γ ((j : ℕ) + 1) - γ (((Fin.last p : Fin (p + 1)) : ℕ) + 1))) = 1 := by
    have : Finset.Ioi (Fin.last p) = (∅ : Finset (Fin (p + 1))) := by
      ext j
      simp [not_lt.mpr (Fin.le_last j)]
    rw [this]
    simp
  rw [hlast, mul_one, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact prod_Ioi_castSucc γ p i



end VandermondeThEq
