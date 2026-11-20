import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.SylvesterCriterium
import ThEqRiemann.RiemannProof.SchurMatrixInverse

/-! -/
namespace InducRiemannZero

open Set Complex Matrix
open RiemannDef

lemma newton_eq_fin_sum (γ : ℕ → ℂ) (m : ℕ → ℕ) (n k : ℕ) :
    newton γ m n k = ∑ j : Fin n, (m ((j : ℕ) + 1) : ℂ) * γ ((j : ℕ) + 1) ^ k := by
  unfold newton
  rw [Fin.sum_univ_eq_sum_range (fun j => (m (j + 1) : ℂ) * γ (j + 1) ^ k) n]
  rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun j => (m j : ℂ) * γ j ^ k) 0 n 1]
  rfl

lemma Hn_eq_factor (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    Hn γ m n = (Vn γ n)ᵀ * Mn m n * Vn γ n := by
  ext p q
  simp only [Hn, Matrix.of_apply, Mn, Matrix.mul_apply, Matrix.transpose_apply, Vn,
    Matrix.diagonal_apply]
  rw [newton_eq_fin_sum]
  simp [pow_add, mul_comm, mul_left_comm, mul_assoc]

lemma Hn_shift_eq_factor (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    Hn_shift γ m n = (Vn γ n)ᵀ * Mn m n * Dn' γ n * Vn γ n := by
  ext p q
  simp only [Hn_shift, Matrix.of_apply, Mn, Dn', Matrix.mul_apply, Matrix.transpose_apply, Vn,
    Matrix.diagonal_apply]
  rw [newton_eq_fin_sum]
  simp [pow_add, pow_succ, mul_comm, mul_left_comm, mul_assoc]

lemma det_Mn (m : ℕ → ℕ) (n : ℕ) :
    (Mn m n).det = ∏ j : Fin n, (m ((j : ℕ) + 1) : ℂ) := by
  simp [Mn, Matrix.det_diagonal]

lemma det_Vn (γ : ℕ → ℂ) (n : ℕ) :
    (Vn γ n).det = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
      (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1)) := by
  rw [Vn_eq_vandermonde, Matrix.det_vandermonde]

lemma Vn_det_ne_zero (γ : ℕ → ℂ) (n : ℕ)
    (hdist : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → γ i = γ j → i = j) :
    (Vn γ n).det ≠ 0 := by
  rw [Vn_eq_vandermonde, Matrix.det_vandermonde_ne_zero_iff]
  intro i j hij
  have := hdist (i + 1) (j + 1) (by omega) (by omega) (by omega) (by omega) hij
  exact Fin.ext (by omega)

lemma Mn_det_ne_zero (m : ℕ → ℕ) (n : ℕ) (hm : ∀ j, 1 ≤ j → j ≤ n → 1 ≤ m j) :
    (Mn m n).det ≠ 0 := by
  rw [det_Mn]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  have := hm ((j : ℕ) + 1) (by omega) (by omega)
  exact_mod_cast (by omega : m ((j : ℕ) + 1) ≠ 0)

lemma det_Hn_eq (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    (Hn γ m n).det = (∏ j : Fin n, (m ((j : ℕ) + 1) : ℂ)) * (Vn γ n).det ^ 2 := by
  rw [Hn_eq_factor, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_Mn]
  ring

lemma Hn_det_ne_zero (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hdist : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → γ i = γ j → i = j)
    (hm : ∀ j, 1 ≤ j → j ≤ n → 1 ≤ m j) :
    (Hn γ m n).det ≠ 0 := by
  rw [det_Hn_eq]
  refine mul_ne_zero ?_ (pow_ne_zero 2 (Vn_det_ne_zero γ n hdist))
  have := Mn_det_ne_zero m n hm
  rwa [det_Mn] at this

lemma Cn_eq (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hV : IsUnit (Vn γ n).det) (hM : IsUnit (Mn m n).det) :
    Cn γ m n = (Vn γ n)⁻¹ * Dn' γ n * Vn γ n := by
  have hVt : IsUnit (Vn γ n)ᵀ.det := by rwa [Matrix.det_transpose]
  unfold Cn
  rw [Hn_eq_factor, Hn_shift_eq_factor]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have h1 : ((Vn γ n)ᵀ)⁻¹ * (Vn γ n)ᵀ = 1 := Matrix.nonsing_inv_mul _ hVt
  have h2 : (Mn m n)⁻¹ * Mn m n = 1 := Matrix.nonsing_inv_mul _ hM
  calc _ = (Vn γ n)⁻¹ * ((Mn m n)⁻¹ * (((Vn γ n)ᵀ)⁻¹ * (Vn γ n)ᵀ) * Mn m n)
            * Dn' γ n * Vn γ n := by simp only [Matrix.mul_assoc]
    _ = (Vn γ n)⁻¹ * Dn' γ n * Vn γ n := by
        rw [h1, Matrix.mul_one, h2, Matrix.mul_one]

lemma similarity_Cn (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hV : IsUnit (Vn γ n).det) (hM : IsUnit (Mn m n).det) :
    Vn γ n * Cn γ m n * (Vn γ n)⁻¹ = Dn' γ n := by
  rw [Cn_eq γ m n hV hM]
  calc Vn γ n * ((Vn γ n)⁻¹ * Dn' γ n * Vn γ n) * (Vn γ n)⁻¹
      = (Vn γ n * (Vn γ n)⁻¹) * Dn' γ n * (Vn γ n * (Vn γ n)⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = Dn' γ n := by
        rw [Matrix.mul_nonsing_inv _ hV, Matrix.one_mul, Matrix.mul_one]

lemma newton_two_eq (γ : ℕ → ℂ) (m : ℕ → ℕ) (g₁ g₂ : ℝ)
    (h1 : γ 1 = (g₁ : ℂ)) (h2 : γ 2 = (g₂ : ℂ)) (k : ℕ) :
    newton γ m 2 k = (((m 1 : ℝ) * g₁ ^ k + (m 2 : ℝ) * g₂ ^ k : ℝ) : ℂ) := by
  unfold newton
  have : Finset.Icc 1 2 = {1, 2} := by decide
  rw [this, Finset.sum_pair (by norm_num), h1, h2]
  push_cast
  ring

lemma newton_two_im (γ : ℕ → ℂ) (m : ℕ → ℕ) (g₁ g₂ : ℝ)
    (h1 : γ 1 = (g₁ : ℂ)) (h2 : γ 2 = (g₂ : ℂ)) (k : ℕ) :
    (newton γ m 2 k).im = 0 := by
  rw [newton_two_eq γ m g₁ g₂ h1 h2 k]
  exact Complex.ofReal_im _

lemma Hn_two_eq_map (γ : ℕ → ℂ) (m : ℕ → ℕ) (g₁ g₂ : ℝ)
    (h1 : γ 1 = (g₁ : ℂ)) (h2 : γ 2 = (g₂ : ℂ)) :
    Hn γ m 2 = (H2R (m 1) (m 2) g₁ g₂).map (algebraMap ℝ ℂ) := by
  ext p q
  simp [Hn, H2R, newton_two_eq γ m g₁ g₂ h1 h2]

lemma H2R_isSymm (m₁ m₂ : ℕ) (g₁ g₂ : ℝ) : (H2R m₁ m₂ g₁ g₂).IsSymm := by
  ext p q
  simp [H2R, Matrix.transpose_apply, add_comm]

lemma H2R_minor_one (m₁ m₂ : ℕ) (g₁ g₂ : ℝ) (hr : 1 ≤ 2) :
    ((H2R m₁ m₂ g₁ g₂).submatrix (Fin.castLE hr) (Fin.castLE hr)).det
      = (m₁ : ℝ) + m₂ := by
  simp [Matrix.det_unique, H2R]

lemma H2R_det (m₁ m₂ : ℕ) (g₁ g₂ : ℝ) :
    (H2R m₁ m₂ g₁ g₂).det = (m₁ : ℝ) * m₂ * (g₂ - g₁) ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [H2R]
  ring


open SylvesterCrit in
theorem H2R_posDef (m₁ m₂ : ℕ) (g₁ g₂ : ℝ)
    (hm₁ : 1 ≤ m₁) (hm₂ : 1 ≤ m₂) (hne : g₁ ≠ g₂) :
    (H2R m₁ m₂ g₁ g₂).PosDef := by
  have hm₁' : (0 : ℝ) < m₁ := by exact_mod_cast hm₁
  have hm₂' : (0 : ℝ) < m₂ := by exact_mod_cast hm₂
  have hsq : 0 < (g₂ - g₁) ^ 2 := by
    have : g₂ - g₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    positivity
  apply Sylvester_posDef _ (H2R_isSymm m₁ m₂ g₁ g₂)
  intro r hr
  interval_cases r
  · simp
  · rw [H2R_minor_one]; positivity
  · have : (Fin.castLE hr : Fin 2 → Fin 2) = id := by
      ext i; simp
    simp only [this, Matrix.submatrix_id_id]
    rw [H2R_det]; positivity


theorem init_rank_two (Xi : ℂ → ℂ) (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (h : ZeroEnumeration Xi γ m) :
    (∀ k, (newton γ m 2 k).im = 0) ∧
    (0 < (Delta γ m 2 1).re ∧ (Delta γ m 2 1).im = 0) ∧
    (0 < (Delta γ m 2 2).re ∧ (Delta γ m 2 2).im = 0) ∧
    ∃ (g₁ g₂ : ℝ), g₁ ≠ g₂ ∧ γ 1 = g₁ ∧ γ 2 = g₂ ∧
      (H2R (m 1) (m 2) g₁ g₂).PosDef ∧
      Hn γ m 2 = (H2R (m 1) (m 2) g₁ g₂).map (algebraMap ℝ ℂ) := by
  have h1 : γ 1 = ((γ 1).re : ℂ) := (Complex.ext (by simp) (by simpa using h.real_one))
  have h2 : γ 2 = ((γ 2).re : ℂ) := (Complex.ext (by simp) (by simpa using h.real_two))
  set g₁ := (γ 1).re with hg₁
  set g₂ := (γ 2).re with hg₂
  have hne : g₁ ≠ g₂ := by
    intro heq
    have : γ 1 = γ 2 := by rw [h1, h2, heq]
    have := h.injective 1 2 le_rfl (by norm_num) this
    omega
  have hm₁ := h.mult_pos 1 le_rfl
  have hm₂ := h.mult_pos 2 (by norm_num)
  have hm₁' : (0 : ℝ) < m 1 := by exact_mod_cast hm₁
  have hm₂' : (0 : ℝ) < m 2 := by exact_mod_cast hm₂
  have hsq : 0 < (g₂ - g₁) ^ 2 := by
    have : g₂ - g₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    positivity
  refine ⟨newton_two_im γ m g₁ g₂ h1 h2, ?_, ?_, g₁, g₂, hne, h1, h2,
    H2R_posDef _ _ _ _ hm₁ hm₂ hne, Hn_two_eq_map γ m g₁ g₂ h1 h2⟩
  · have : Delta γ m 2 1 = (((m 1 : ℝ) + m 2 : ℝ) : ℂ) := by
      simp [Delta, Matrix.det_unique, newton_two_eq γ m g₁ g₂ h1 h2]
    rw [this]
    simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
    have hsum : (0 : ℝ) < (m 1 : ℝ) + m 2 := by positivity
    exact hsum
  · have hD : Delta γ m 2 2 = (((m 1 : ℝ) * m 2 * (g₂ - g₁) ^ 2 : ℝ) : ℂ) := by
      simp only [Delta, Matrix.det_fin_two, Matrix.of_apply,
        newton_two_eq γ m g₁ g₂ h1 h2]
      norm_num
      ring
    have hpos : 0 < (m 1 : ℝ) * m 2 * (g₂ - g₁) ^ 2 := by
      have := mul_pos hm₁' hm₂'
      exact mul_pos this hsq
    rw [hD]
    exact ⟨by rw [Complex.ofReal_re]; exact hpos, by rw [Complex.ofReal_im]⟩

lemma newton_succ (γ : ℕ → ℂ) (m : ℕ → ℕ) (n k : ℕ) :
    newton γ m (n + 1) k = newton γ m n k + (m (n + 1) : ℂ) * γ (n + 1) ^ k := by
  unfold newton
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma quad_form_eq (g : ℕ → ℝ) (m : ℕ → ℕ) (n r : ℕ) (c : Fin r → ℝ) :
    ∑ p : Fin r, ∑ q : Fin r, c p * c q * (∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * g j ^ ((p : ℕ) + q))
    = ∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * (∑ p : Fin r, c p * g j ^ (p : ℕ)) ^ 2 := by
  have hsq : ∀ j, (∑ p : Fin r, c p * g j ^ (p : ℕ)) ^ 2
      = ∑ p : Fin r, ∑ q : Fin r, c p * c q * g j ^ ((p : ℕ) + q) := by
    intro j
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [pow_add]; ring
  have hL : ∀ p q : Fin r,
      c p * c q * (∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * g j ^ ((p : ℕ) + q))
      = ∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * (c p * c q * g j ^ ((p : ℕ) + q)) := by
    intro p q
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hR : ∀ j, (m j : ℝ) * (∑ p : Fin r, c p * g j ^ (p : ℕ)) ^ 2
      = ∑ p : Fin r, ∑ q : Fin r, (m j : ℝ) * (c p * c q * g j ^ ((p : ℕ) + q)) := by
    intro j
    rw [hsq j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [Finset.mul_sum]
  simp only [hL, hR]
  have h1 : ∀ p : Fin r,
      ∑ q : Fin r, ∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * (c p * c q * g j ^ ((p : ℕ) + q))
      = ∑ j ∈ Finset.Icc 1 n, ∑ q : Fin r, (m j : ℝ) * (c p * c q * g j ^ ((p : ℕ) + q)) :=
    fun p => Finset.sum_comm
  simp only [h1]
  exact Finset.sum_comm

lemma quad_form_pos (g : ℕ → ℝ) (m : ℕ → ℕ) (n r : ℕ) (hr : r ≤ n)
    (hm : ∀ j ∈ Finset.Icc 1 n, 1 ≤ m j)
    (hinj : Set.InjOn g (Finset.Icc 1 n : Set ℕ))
    (c : Fin r → ℝ) (hc : c ≠ 0) :
    0 < ∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * (∑ p : Fin r, c p * g j ^ (p : ℕ)) ^ 2 := by
  classical
  set P : Polynomial ℝ := ∑ p : Fin r, Polynomial.C (c p) * Polynomial.X ^ (p : ℕ) with hP
  have hev : ∀ x : ℝ, P.eval x = ∑ p : Fin r, c p * x ^ (p : ℕ) := by
    intro x; simp [hP, Polynomial.eval_finsetSum]
  have hPne : P ≠ 0 := by
    intro h0
    apply hc
    funext p
    have := congrArg (fun Q => Q.coeff (p : ℕ)) h0
    simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single p] at this
    · simpa using this
    · intro q _ hq
      have : (p : ℕ) ≠ q := fun h => hq (Fin.ext h.symm)
      simp [this]
    · simp
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      apply hc
      funext p
      exact absurd p.isLt (by omega)
    · exact h0
  have hdeg : P.natDegree < n := by
    have hle : P.natDegree ≤ r - 1 := by
      refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
      intro p _
      refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
      have := p.isLt
      omega
    omega
  have hnon : ∀ j ∈ Finset.Icc 1 n, 0 ≤ (m j : ℝ) * (P.eval (g j)) ^ 2 :=
    fun j _ => by positivity
  have hex : ∃ j ∈ Finset.Icc 1 n, P.eval (g j) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hcard : (Finset.Icc 1 n).card ≤ P.roots.toFinset.card := by
      have himg : (Finset.Icc 1 n).image g ⊆ P.roots.toFinset := by
        intro x hx
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        simp [Polynomial.mem_roots hPne, hall j hj]
      calc (Finset.Icc 1 n).card = ((Finset.Icc 1 n).image g).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ _ := Finset.card_le_card himg
    have := (Multiset.toFinset_card_le P.roots).trans (Polynomial.card_roots' P)
    simp at hcard
    omega
  obtain ⟨j₀, hj₀, hne⟩ := hex
  simp_rw [← hev]
  refine Finset.sum_pos' hnon ⟨j₀, hj₀, ?_⟩
  have : (0 : ℝ) < m j₀ := by exact_mod_cast hm j₀ hj₀
  positivity

lemma Delta_self_eq (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    Delta γ m n n = (∏ j : Fin n, (m ((j : ℕ) + 1) : ℂ)) * (Vn γ n).det ^ 2 :=
  det_Hn_eq γ m n

lemma det_Vn_succ (γ : ℕ → ℂ) (n : ℕ) :
    (Vn γ (n + 1)).det
      = (Vn γ n).det * ∏ j : Fin n, (γ (n + 1) - γ ((j : ℕ) + 1)) := by
  rw [Vn_eq_vandermonde γ (n + 1), Vn_eq_vandermonde γ n,
    Matrix.det_vandermonde, Matrix.det_vandermonde]
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ j ∈ Finset.Ioi (Fin.last n),
      (γ ((j : ℕ) + 1) - γ (((Fin.last n : Fin (n + 1)) : ℕ) + 1)) = 1 := by
    have : Finset.Ioi (Fin.last n) = ∅ := by
      ext j; simp [not_lt.mpr (Fin.le_last j)]
    simp [this]
  rw [hlast, mul_one]
  have hinner : ∀ i : Fin n,
      ∏ j ∈ Finset.Ioi (Fin.castSucc i),
        (γ ((j : ℕ) + 1) - γ (((Fin.castSucc i : Fin (n + 1)) : ℕ) + 1))
      = (∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1)))
        * (γ (n + 1) - γ ((i : ℕ) + 1)) := by
    intro i
    have hset : Finset.Ioi (Fin.castSucc i)
        = insert (Fin.last n) ((Finset.Ioi i).map Fin.castSuccEmb) := by
      ext j
      simp only [Finset.mem_Ioi, Finset.mem_insert, Finset.mem_map, Fin.castSuccEmb_apply]
      constructor
      · intro h
        rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
        · exact Or.inr ⟨j', by simpa [Fin.castSucc_lt_castSucc_iff] using h, rfl⟩
        · exact Or.inl rfl
      · rintro (rfl | ⟨j', hj', rfl⟩)
        · exact Fin.castSucc_lt_last i
        · simpa [Fin.castSucc_lt_castSucc_iff] using hj'
    have hnot : Fin.last n ∉ (Finset.Ioi i).map Fin.castSuccEmb := by
      simp only [Finset.mem_map, Fin.castSuccEmb_apply, not_exists, not_and]
      intro j' _ h
      exact absurd h (Fin.castSucc_lt_last j').ne
    rw [hset, Finset.prod_insert hnot, Finset.prod_map]
    simp only [Fin.castSuccEmb_apply, Fin.val_castSucc, Fin.val_last]
    ring
  simp only [hinner, Finset.prod_mul_distrib]

lemma delta_succ (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    Delta γ m (n + 1) (n + 1)
      = (m (n + 1) : ℂ) * Delta γ m n n * ∏ j : Fin n,
        (γ (n + 1) - γ ((j : ℕ) + 1)) ^ 2 := by
  rw [Delta_self_eq γ m (n + 1), Delta_self_eq γ m n, det_Vn_succ γ n,
    Fin.prod_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [mul_pow, Finset.prod_pow]
  ring

lemma newton_im_zero (γ : ℕ → ℂ) (m : ℕ → ℕ) (n k : ℕ)
    (hr : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0) :
    (newton γ m n k).im = 0 := by
  unfold newton
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hγ : γ j = ((γ j).re : ℂ) := by
    apply Complex.ext <;> simp [hr j hj.1 hj.2]
  rw [hγ, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact Complex.ofReal_im _


open SchurInverse in
lemma Delta_eq_jacobi (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hA : IsUnit (Hsub γ m n).det) :
    Delta γ m n n = Delta γ m n (n - 1) * Schur γ m n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hA ⊢
  have h1 : Delta γ m (k + 1) k = (Hsub γ m (k + 1)).det := rfl
  let e : Fin (k + 1) ≃ Fin k ⊕ Unit :=
    (finSumFinEquiv (m := k) (n := 1)).symm.trans
      (Equiv.sumCongr (Equiv.refl _) (Equiv.equivPUnit (Fin 1)))
  have e_cast : ∀ i : Fin k, e (Fin.castSucc i) = Sum.inl i := by
    intro i
    have : (Fin.castSucc i : Fin (k + 1)) = Fin.castAdd 1 i := rfl
    simp only [e, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_castAdd,
      Equiv.sumCongr_apply, Sum.map_inl, Equiv.refl_apply]
  have e_last : e (Fin.last k) = Sum.inr () := by
    have : (Fin.last k : Fin (k + 1)) = Fin.natAdd k (0 : Fin 1) := by
      ext; simp
    simp only [e, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd,
      Equiv.sumCongr_apply, Sum.map_inr]
  set M : Matrix (Fin k ⊕ Unit) (Fin k ⊕ Unit) ℂ :=
    Matrix.fromBlocks (Hsub γ m (k + 1))
      (Matrix.replicateCol Unit (bn γ m (k + 1)))
      (Matrix.replicateRow Unit (bn γ m (k + 1)))
      (Matrix.of fun (_ _ : Unit) => newton γ m (k + 1) (2 * k)) with hM
  have h2 : Delta γ m (k + 1) (k + 1) = M.det := by
    have hsub : (Matrix.of fun (p q : Fin (k + 1)) => newton γ m (k + 1) (p + q))
        = M.submatrix e e := by
      ext p q
      refine Fin.lastCases ?_ (fun p' => ?_) p <;>
        refine Fin.lastCases ?_ (fun q' => ?_) q
      · rw [Matrix.of_apply, Matrix.submatrix_apply, e_last, hM,
          Matrix.fromBlocks_apply₂₂]
        simp [two_mul]
      · rw [Matrix.of_apply, Matrix.submatrix_apply, e_last, e_cast, hM,
          Matrix.fromBlocks_apply₂₁]
        simp [bn]
      · rw [Matrix.of_apply, Matrix.submatrix_apply, e_cast, e_last, hM,
          Matrix.fromBlocks_apply₁₂]
        simp [bn, add_comm]
      · rw [Matrix.of_apply, Matrix.submatrix_apply, e_cast, e_cast, hM,
          Matrix.fromBlocks_apply₁₁]
        simp [Hsub]
    unfold Delta
    rw [hsub, Matrix.det_submatrix_equiv_self]
  rw [h2, hM, jacobi_schur _ _ _ hA, h1]
  unfold Schur
  have hidx : 2 * (k + 1) - 2 = 2 * k := by omega
  rw [hidx]

lemma Delta_pos_of_real (γ : ℕ → ℂ) (m : ℕ → ℕ) (n r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n)
    (hm : ∀ j ∈ Finset.Icc 1 n, 1 ≤ m j)
    (hreal : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0)
    (hinj : Set.InjOn γ (Finset.Icc 1 n : Set ℕ)) :
    0 < (Delta γ m n r).re ∧ (Delta γ m n r).im = 0 := by
  set g : ℕ → ℝ := fun j => (γ j).re with hg
  set Hr : Matrix (Fin r) (Fin r) ℝ :=
    Matrix.of fun p q => ∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * g j ^ ((p : ℕ) + q) with hHr
  have hcast : Delta γ m n r = ((Hr.det : ℝ) : ℂ) := by
    unfold Delta
    have h := RingHom.map_det Complex.ofRealHom Hr
    rw [RingHom.mapMatrix_apply] at h
    have h' : ((Hr.det : ℝ) : ℂ) = (Hr.map Complex.ofRealHom).det := h
    rw [h']
    congr 1
    ext p q
    simp only [Matrix.of_apply, Matrix.map_apply, hHr, newton, Complex.ofRealHom_eq_coe]
    push_cast
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' := Finset.mem_Icc.mp hj
    have him := hreal j hj'.1 hj'.2
    have hγ : γ j = ((g j : ℝ) : ℂ) :=
      Complex.ext (by simp [hg]) (by simp [hg, him])
    rw [hγ]
  have hsymm : Hr.IsSymm := by
    ext p q
    simp [hHr, Matrix.transpose_apply, add_comm]
  have hpd : Hr.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hsymm, fun v hv => ?_⟩
    have hquad : star v ⬝ᵥ Hr.mulVec v
        = ∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * (∑ p : Fin r, v p * g j ^ (p : ℕ)) ^ 2 := by
      simp only [hHr, Matrix.mulVec, dotProduct, Matrix.of_apply, star_trivial]
      have key : ∀ j ∈ Finset.Icc 1 n,
          (m j : ℝ) * (∑ p : Fin r, v p * g j ^ (p : ℕ)) ^ 2
          = ∑ p : Fin r, v p * ∑ q : Fin r, ((m j : ℝ) * g j ^ ((p : ℕ) + q)) * v q := by
        intro j _
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        rw [pow_add]; ring
      rw [Finset.sum_congr rfl key]
      have hB : ∀ p q : Fin r,
          v p * ((∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * g j ^ ((p : ℕ) + q)) * v q)
          = ∑ j ∈ Finset.Icc 1 n, v p * ((m j : ℝ) * g j ^ ((p : ℕ) + q) * v q) := by
        intro p q
        rw [Finset.sum_mul, Finset.mul_sum]
      have hL : ∀ p : Fin r,
          v p * ∑ q : Fin r, (∑ j ∈ Finset.Icc 1 n, (m j : ℝ) * g j ^ ((p : ℕ) + q)) * v q
          = ∑ j ∈ Finset.Icc 1 n, ∑ q : Fin r, v p * ((m j : ℝ) * g j ^ ((p : ℕ) + q) * v q) := by
        intro p
        rw [Finset.mul_sum]
        simp_rw [hB]
        exact Finset.sum_comm
      have hR : ∀ j ∈ Finset.Icc 1 n,
          ∑ p : Fin r, v p * ∑ q : Fin r, (m j : ℝ) * g j ^ ((p : ℕ) + q) * v q
          = ∑ p : Fin r, ∑ q : Fin r, v p * ((m j : ℝ) * g j ^ ((p : ℕ) + q) * v q) := by
        intro j _
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl hR]
      rw [Finset.sum_congr rfl (fun p _ => hL p)]
      exact Finset.sum_comm
    rw [hquad]
    have hnn : ∀ j ∈ Finset.Icc 1 n,
        0 ≤ (m j : ℝ) * (∑ p : Fin r, v p * g j ^ (p : ℕ)) ^ 2 :=
      fun j _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) (fun h0 => hv ?_)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0.symm
    have hP : ∀ j ∈ Finset.Icc 1 n, ∑ p : Fin r, v p * g j ^ (p : ℕ) = 0 := by
      intro j hj
      have h1 := hzero j hj
      have hmj : (m j : ℝ) ≠ 0 := by
        have := hm j hj
        positivity
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hmj
      · exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    have hginj : Set.InjOn g (Finset.Icc 1 n : Set ℕ) := by
      intro a ha b hb hab
      apply hinj ha hb
      have hra := hreal a (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp ha).2
      have hrb := hreal b (Finset.mem_Icc.mp hb).1 (Finset.mem_Icc.mp hb).2
      exact Complex.ext hab (by rw [hra, hrb])
    set P : Polynomial ℝ := ∑ p : Fin r, Polynomial.C (v p) * Polynomial.X ^ (p : ℕ) with hP_def
    have hPeval : ∀ j ∈ Finset.Icc 1 n, P.eval (g j) = 0 := by
      intro j hj
      rw [hP_def, Polynomial.eval_finsetSum]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact hP j hj
    have hcard : (Finset.Icc 1 n).card = n := by simp
    have hroots : ∀ x ∈ (Finset.Icc 1 n).image g, P.IsRoot x := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact hPeval j hj
    have himgcard : ((Finset.Icc 1 n).image g).card = n := by
      rw [Finset.card_image_of_injOn hginj, hcard]
    have hdeg : P.degree < r := by
      rw [hP_def]
      refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
      intro p _
      refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
      exact_mod_cast p.isLt
    have hndeg : P.natDegree < n := by
      by_cases hP0' : P = 0
      · rw [hP0']; simp; omega
      · have := Polynomial.natDegree_lt_iff_degree_lt hP0' |>.mpr hdeg
        omega
    have hP0 : P = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' P
        ((Finset.Icc 1 n).image g) hroots ?_
      rw [himgcard]
      exact hndeg
    funext p
    have hcoef : P.coeff (p : ℕ) = v p := by
      rw [hP_def, Polynomial.finsetSum_coeff]
      simp only [Polynomial.coeff_C_mul_X_pow]
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hqp
        have : (p : ℕ) ≠ q := fun h => hqp (Fin.ext h.symm)
        simp [this]
      · simp
    rw [← hcoef, hP0]
    simp
  have hdet : 0 < Hr.det := hpd.det_pos
  rw [hcast]
  exact ⟨by simpa using hdet, by simp⟩

lemma Delta_im_zero_of_moments_real (γ : ℕ → ℂ) (m : ℕ → ℕ) (n r : ℕ)
    (hr : r ≤ n)
    (hmom : ∀ k ≤ 2 * n - 1, (newton γ m n k).im = 0) :
    (Delta γ m n r).im = 0 := by
  set Hr : Matrix (Fin r) (Fin r) ℝ :=
    Matrix.of fun p q => (newton γ m n ((p : ℕ) + (q : ℕ))).re with hHr
  have hmap : (Matrix.of fun (p q : Fin r) => newton γ m n ((p : ℕ) + (q : ℕ)))
      = Hr.map (algebraMap ℝ ℂ) := by
    ext p q
    have hk : (p : ℕ) + (q : ℕ) ≤ 2 * n - 1 := by
      have := p.isLt
      have := q.isLt
      omega
    have him := hmom _ hk
    simp only [hHr, Matrix.of_apply, Matrix.map_apply]
    exact (Complex.ext (by simp) (by simpa using him))
  have hdet : Delta γ m n r = (Hr.det : ℂ) := by
    unfold Delta
    rw [hmap]
    exact (RingHom.map_det (algebraMap ℝ ℂ) Hr).symm
  rw [hdet]
  exact Complex.ofReal_im _

lemma Hn_eq_map_real (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hmom : ∀ k ≤ 2 * n - 1, (newton γ m n k).im = 0) :
    ∃ Hr : Matrix (Fin n) (Fin n) ℝ, Hr.IsSymm ∧
      Hn γ m n = Hr.map (algebraMap ℝ ℂ) := by
  refine ⟨Matrix.of fun p q => (newton γ m n ((p : ℕ) + (q : ℕ))).re, ?_, ?_⟩
  · ext p q
    simp [Matrix.transpose_apply, Nat.add_comm]
  · ext p q
    have hk : (p : ℕ) + (q : ℕ) ≤ 2 * n - 1 := by
      have := p.isLt
      have := q.isLt
      omega
    simp only [Hn, Matrix.of_apply, Matrix.map_apply]
    apply Complex.ext
    · simp
    · simpa using hmom _ hk

lemma Hn_shift_eq_map_real (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hmom : ∀ k ≤ 2 * n - 1, (newton γ m n k).im = 0) :
    ∃ Hs : Matrix (Fin n) (Fin n) ℝ, Hs.IsSymm ∧
      Hn_shift γ m n = Hs.map (algebraMap ℝ ℂ) := by
  refine ⟨Matrix.of fun p q => (newton γ m n ((p : ℕ) + (q : ℕ) + 1)).re, ?_, ?_⟩
  · ext p q
    simp [Matrix.transpose_apply, Nat.add_comm]
  · ext p q
    have hk : (p : ℕ) + (q : ℕ) + 1 ≤ 2 * n - 1 := by
      have := p.isLt
      have := q.isLt
      omega
    simp only [Hn_shift, Matrix.of_apply, Matrix.map_apply]
    apply Complex.ext
    · simp
    · simpa using hmom _ hk

lemma Delta_eq_minor (γ : ℕ → ℂ) (m : ℕ → ℕ) (n r : ℕ) (hr : r ≤ n)
    (Hr : Matrix (Fin n) (Fin n) ℝ)
    (hH : Hn γ m n = Hr.map (algebraMap ℝ ℂ)) :
    Delta γ m n r =
      ((Hr.submatrix (Fin.castLE hr) (Fin.castLE hr)).det : ℝ) := by
  have h1 : (Matrix.of fun (p q : Fin r) => newton γ m n ((p : ℕ) + (q : ℕ)))
      = (Hr.map (algebraMap ℝ ℂ)).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
    ext p q
    have := congrFun (congrFun hH (Fin.castLE hr p)) (Fin.castLE hr q)
    simpa [Hn, Matrix.submatrix_apply] using this
  unfold Delta
  rw [h1]
  have h2 : (Hr.map (algebraMap ℝ ℂ)).submatrix (Fin.castLE hr) (Fin.castLE hr)
      = (Hr.submatrix (Fin.castLE hr) (Fin.castLE hr)).map (algebraMap ℝ ℂ) := by
    ext p q; simp
  rw [h2]
  exact (RingHom.map_det (algebraMap ℝ ℂ) _).symm

lemma quadForm_im_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm)
    (u : Fin n → ℂ) :
    (star u ⬝ᵥ ((M.map (algebraMap ℝ ℂ)) *ᵥ u)).im = 0 := by
  have hconj : (starRingEnd ℂ) (star u ⬝ᵥ ((M.map (algebraMap ℝ ℂ)) *ᵥ u))
      = star u ⬝ᵥ ((M.map (algebraMap ℝ ℂ)) *ᵥ u) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      map_sum, map_mul, Complex.conj_ofReal, Complex.star_def,
      Complex.conj_conj, Complex.coe_algebraMap, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    have hij : M j i = M i j := by
      have := congrFun (congrFun hM i) j
      simpa [Matrix.transpose_apply] using this
    rw [hij]
    ring
  exact Complex.conj_eq_iff_im.mp hconj


lemma quadForm_re_pos {n : ℕ} (Hr : Matrix (Fin n) (Fin n) ℝ) (hRpos : Hr.PosDef)
    (u : Fin n → ℂ) (hu : u ≠ 0) :
    0 < (star u ⬝ᵥ ((Hr.map (algebraMap ℝ ℂ)) *ᵥ u)).re := by
  have hre_c : ∀ i j, ((algebraMap ℝ ℂ) (Hr i j)).re = Hr i j := by
    intro i j; simp
  have him_c : ∀ i j, ((algebraMap ℝ ℂ) (Hr i j)).im = 0 := by
    intro i j; simp
  have hre : (star u ⬝ᵥ ((Hr.map (algebraMap ℝ ℂ)) *ᵥ u)).re
      = ∑ i, ∑ j, Hr i j * ((u i).re * (u j).re + (u i).im * (u j).im) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Complex.re_sum, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im, Complex.mul_im, Complex.im_sum, hre_c, him_c]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hsplit : (star u ⬝ᵥ ((Hr.map (algebraMap ℝ ℂ)) *ᵥ u)).re
      = (fun i => (u i).re) ⬝ᵥ (Hr *ᵥ (fun i => (u i).re))
        + (fun i => (u i).im) ⬝ᵥ (Hr *ᵥ (fun i => (u i).im)) := by
    rw [hre]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hpd := (Matrix.posDef_iff_dotProduct_mulVec.mp hRpos).2
  have hnn : ∀ v : Fin n → ℝ, 0 ≤ v ⬝ᵥ (Hr *ᵥ v) := by
    intro v
    by_cases hv : v = 0
    · subst hv; simp
    · exact le_of_lt (by simpa using hpd hv)
  rw [hsplit]
  by_cases ha : (fun i => (u i).re) = 0
  · have hb : (fun i => (u i).im) ≠ 0 := by
      intro hb
      apply hu
      funext i
      apply Complex.ext
      · simpa using congrFun ha i
      · simpa using congrFun hb i
    have := hpd hb
    have h2 : 0 < (fun i => (u i).im) ⬝ᵥ (Hr *ᵥ (fun i => (u i).im)) := by simpa using this
    exact add_pos_of_nonneg_of_pos (hnn _) h2
  · have h1 : 0 < (fun i => (u i).re) ⬝ᵥ (Hr *ᵥ (fun i => (u i).re)) := by
      simpa using hpd ha
    exact add_pos_of_pos_of_nonneg h1 (hnn _)

lemma eigenvalue_real_of_posDef {n : ℕ}
    (Hr Hs : Matrix (Fin n) (Fin n) ℝ)
    (hRpos : Hr.PosDef) (hssymm : Hs.IsSymm)
    (z : ℂ) (u : Fin n → ℂ) (hu : u ≠ 0)
    (heig : (Hs.map (algebraMap ℝ ℂ)) *ᵥ u
        = z • ((Hr.map (algebraMap ℝ ℂ)) *ᵥ u)) :
    z.im = 0 := by
  have hRsymm : Hr.IsSymm := by
    have h1 : Hr.IsHermitian := hRpos.1
    ext i j
    have h := congrFun (congrFun h1 j) i
    simp only [Matrix.conjTranspose_apply, star_trivial] at h
    simp only [Matrix.transpose_apply]
    exact h.symm
  have hqr_re := quadForm_re_pos Hr hRpos u hu
  have hqr_im := quadForm_im_zero Hr hRsymm u
  have hqs_im := quadForm_im_zero Hs hssymm u
  have hrel : star u ⬝ᵥ ((Hs.map (algebraMap ℝ ℂ)) *ᵥ u)
      = z * (star u ⬝ᵥ ((Hr.map (algebraMap ℝ ℂ)) *ᵥ u)) := by
    rw [heig, dotProduct_smul, smul_eq_mul]
  have him := congrArg Complex.im hrel
  rw [Complex.mul_im, hqr_im, hqs_im] at him
  have hprod : z.im * (star u ⬝ᵥ ((Hr.map (algebraMap ℝ ℂ)) *ᵥ u)).re = 0 := by
    linarith
  exact (mul_eq_zero.mp hprod).resolve_right hqr_re.ne'

lemma Cn_eigenvector (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hV : IsUnit (Vn γ n).det) (hM : IsUnit (Mn m n).det) :
    ∃ u : Fin n → ℂ, u ≠ 0 ∧ (Cn γ m n) *ᵥ u = γ n • u := by
  have hnpos : 0 < n := hn
  set i0 : Fin n := ⟨n - 1, by omega⟩ with hi0
  set e : Fin n → ℂ := Pi.single i0 1 with he
  have he_ne : e ≠ 0 := by
    intro h
    have := congrFun h i0
    simp [he] at this
  have hDe : (Dn' γ n) *ᵥ e = γ n • e := by
    have hidx : ((i0 : ℕ) + 1) = n := by simp [hi0]; omega
    ext i
    simp only [Dn', he, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases h : i = i0
    · subst h
      simp [hidx]
    · simp [h]
  have hVinv : (Vn γ n)⁻¹ * (Vn γ n) = 1 := Matrix.nonsing_inv_mul _ hV
  have hVinv' : (Vn γ n) * (Vn γ n)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hV
  refine ⟨(Vn γ n)⁻¹ *ᵥ e, ?_, ?_⟩
  · intro h
    apply he_ne
    have : (Vn γ n) *ᵥ ((Vn γ n)⁻¹ *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, hVinv', Matrix.one_mulVec]
    rw [← this, h, Matrix.mulVec_zero]
  · rw [Cn_eq γ m n hV hM]
    have hVe : (Vn γ n) *ᵥ ((Vn γ n)⁻¹ *ᵥ e) = e := by
      rw [Matrix.mulVec_mulVec, hVinv', Matrix.one_mulVec]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        hVe, hDe, Matrix.mulVec_smul]

lemma gamma_n_real_of_data (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hV : IsUnit (Vn γ n).det) (hM : IsUnit (Mn m n).det)
    (Hr Hs : Matrix (Fin n) (Fin n) ℝ)
    (hRpos : Hr.PosDef) (hssymm : Hs.IsSymm)
    (hH : Hn γ m n = Hr.map (algebraMap ℝ ℂ))
    (hHs : Hn_shift γ m n = Hs.map (algebraMap ℝ ℂ))
    (hshift : Hn_shift γ m n = Hn γ m n * Cn γ m n) :
    (γ n).im = 0 := by
  obtain ⟨u, hu, hCu⟩ := Cn_eigenvector γ m n hn hV hM
  refine eigenvalue_real_of_posDef Hr Hs hRpos hssymm (γ n) u hu ?_
  rw [← hHs, hshift, ← Matrix.mulVec_mulVec, hCu, Matrix.mulVec_smul, hH]


open SylvesterCrit in
theorem step3_equiv (Xi : ℂ → ℂ) (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (h : ZeroEnumeration Xi γ m) (n : ℕ) (hn : 3 ≤ n)
    (hreal : ∀ j, 1 ≤ j → j ≤ n - 1 → (γ j).im = 0) :
    (γ n).im = 0 ↔
      ((∀ k, k ≤ 2 * n - 1 → (newton γ m n k).im = 0) ∧
       (∀ r, 1 ≤ r → r ≤ n - 1 → 0 < (Delta γ m n r).re ∧ (Delta γ m n r).im = 0) ∧
       0 < (Delta γ m n n / Delta γ m n (n - 1)).re) := by
  have hm : ∀ j ∈ Finset.Icc 1 n, 1 ≤ m j := by
    intro j hj
    exact h.mult_pos j (Finset.mem_Icc.mp hj).1
  have hinj : Set.InjOn γ (Finset.Icc 1 n : Set ℕ) := by
    intro a ha b hb hab
    have ha' : a ∈ Finset.Icc 1 n := by exact_mod_cast ha
    have hb' : b ∈ Finset.Icc 1 n := by exact_mod_cast hb
    exact h.injective a b (Finset.mem_Icc.mp ha').1 (Finset.mem_Icc.mp hb').1 hab
  constructor
  · intro hγn
    have hreal_n : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0 := by
      intro j hj1 hjn
      rcases Nat.lt_or_ge j n with hlt | hge
      · exact hreal j hj1 (by omega)
      · have : j = n := by omega
        subst this
        exact hγn
    refine ⟨?_, ?_, ?_⟩
    · intro k _
      exact newton_im_zero γ m n k hreal_n
    · intro r hr1 hrn
      exact Delta_pos_of_real γ m n r hr1 (by omega) hm hreal_n hinj
    · obtain ⟨hnum_pos, hnum_im⟩ :=
        Delta_pos_of_real γ m n n (by omega) le_rfl hm hreal_n hinj
      obtain ⟨hden_pos, hden_im⟩ :=
        Delta_pos_of_real γ m n (n - 1) (by omega) (by omega) hm hreal_n hinj
      have hden_ne : Delta γ m n (n - 1) ≠ 0 := by
        intro h0
        rw [h0] at hden_pos
        simp at hden_pos
      rw [Complex.div_re]
      simp only [hnum_im, hden_im, mul_zero, add_zero, zero_div]
      have hnsq : 0 < Complex.normSq (Delta γ m n (n - 1)) :=
        Complex.normSq_pos.mpr hden_ne
      rw [show (Delta γ m n n).re * (Delta γ m n (n - 1)).re
            / Complex.normSq (Delta γ m n (n - 1))
          = (Delta γ m n n).re * (Delta γ m n (n - 1)).re
            / Complex.normSq (Delta γ m n (n - 1)) from rfl]
      positivity
  · rintro ⟨hmom, hpos, hS⟩
    obtain ⟨hden_pos, hden_im⟩ := hpos (n - 1) (by omega) le_rfl
    have hnum_im : (Delta γ m n n).im = 0 :=
      Delta_im_zero_of_moments_real γ m n n le_rfl hmom
    have hden_ne : Delta γ m n (n - 1) ≠ 0 := by
      intro h0
      rw [h0] at hden_pos
      simp at hden_pos
    have hnum_pos : 0 < (Delta γ m n n).re := by
      have hnsq : 0 < Complex.normSq (Delta γ m n (n - 1)) :=
        Complex.normSq_pos.mpr hden_ne
      rw [Complex.div_re] at hS
      simp only [hnum_im, hden_im, mul_zero, add_zero, zero_div] at hS
      have h1 : 0 < (Delta γ m n n).re * (Delta γ m n (n - 1)).re :=
        (div_pos_iff_of_pos_right hnsq).mp hS
      exact (pos_iff_pos_of_mul_pos h1).mpr hden_pos
    obtain ⟨Hr, hsymm, hH⟩ := Hn_eq_map_real γ m n hmom
    have hRpos : Hr.PosDef := by
      apply posDef_of_leading_minors Hr hsymm
      intro r hr
      rcases Nat.eq_zero_or_pos r with h0 | hr1
      · subst h0
        simp
      · have hcast := Delta_eq_minor γ m n r hr Hr hH
        rcases Nat.lt_or_ge r n with hlt | hge
        · have h1 := (hpos r hr1 (by omega)).1
          rw [hcast] at h1
          simpa using h1
        · have hrn : r = n := by omega
          subst hrn
          have h1 := hnum_pos
          rw [hcast] at h1
          simpa using h1
    have hdetH : (Hn γ m n).det ≠ 0 :=
      Hn_det_ne_zero γ m n
        (fun i j hi1 hin hj1 hjn hij =>
          hinj (by simpa using And.intro hi1 hin) (by simpa using And.intro hj1 hjn) hij)
        (fun j hj1 hjn => hm j (by simpa using And.intro hj1 hjn))
    have hshift : Hn_shift γ m n = Hn γ m n * Cn γ m n := by
      unfold Cn
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdetH)]
      simp
    obtain ⟨Hs, hssymm, hHs⟩ := Hn_shift_eq_map_real γ m n hmom
    have hV : IsUnit (Vn γ n).det :=
      isUnit_iff_ne_zero.mpr
        (Vn_det_ne_zero γ n
          (fun i j hi1 hin hj1 hjn hij =>
            hinj (by simpa using And.intro hi1 hin)
                 (by simpa using And.intro hj1 hjn) hij))
    have hM : IsUnit (Mn m n).det :=
      isUnit_iff_ne_zero.mpr
        (Mn_det_ne_zero m n
          (fun j hj1 hjn => hm j (by simpa using And.intro hj1 hjn)))
    exact gamma_n_real_of_data γ m n (by omega) hV hM Hr Hs hRpos hssymm hH hHs hshift

lemma trace_Cn_eq_sum (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hV : IsUnit (Vn γ n).det) (hM : IsUnit (Mn m n).det) :
    (Cn γ m n).trace = ∑ j ∈ Finset.Icc 1 n, γ j := by
  rw [Cn_eq γ m n hV hM]
  have hVu : Invertible (Vn γ n) := Matrix.invertibleOfIsUnitDet _ hV
  have h1 : ((Vn γ n)⁻¹ * Dn' γ n * Vn γ n).trace = (Dn' γ n).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hV]
    simp
  rw [h1]
  unfold Dn'
  rw [Matrix.trace_diagonal]
  rw [Finset.sum_bij (fun (j : Fin n) _ => (j : ℕ) + 1)]
  · intro j _; simp [Finset.mem_Icc]
  · intro a _ b _ h; ext; omega
  · intro b hb
    simp only [Finset.mem_Icc] at hb
    exact ⟨⟨b - 1, by omega⟩, Finset.mem_univ _, by simp; omega⟩
  · intro j _; rfl

lemma gamma_n_eq_trace (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hV : IsUnit (Vn γ n).det) (hM : IsUnit (Mn m n).det) :
    γ n = (Cn γ m n).trace - ∑ j ∈ Finset.Icc 1 (n - 1), γ j := by
  rw [trace_Cn_eq_sum γ m n hV hM]
  have hsplit : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : n ∉ Finset.Icc 1 (n - 1) := by simp [Finset.mem_Icc]; omega
  rw [hsplit, Finset.sum_insert hnot]
  ring

lemma gamma_n_eq_moments (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hmn : 1 ≤ m n) :
    γ n = (newton γ m n 1 - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ) * γ j) /
          (newton γ m n 0 - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ)) := by
  have hsplit : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : n ∉ Finset.Icc 1 (n - 1) := by simp [Finset.mem_Icc]; omega
  have h0 : newton γ m n 0 = (m n : ℂ) + ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ) := by
    unfold newton; rw [hsplit, Finset.sum_insert hnot]; simp
  have h1 : newton γ m n 1 =
      (m n : ℂ) * γ n + ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ) * γ j := by
    unfold newton; rw [hsplit, Finset.sum_insert hnot]; simp
  have hmne : (m n : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : m n ≠ 0)
  rw [h0, h1]
  rw [show (m n : ℂ) + ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ)
        - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ) = (m n : ℂ) by ring,
      show (m n : ℂ) * γ n + ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ) * γ j
        - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ) * γ j = (m n : ℂ) * γ n by ring]
  field_simp

open Polynomial

lemma momentForm_X_pow (γ : ℕ → ℂ) (m : ℕ → ℕ) (n k : ℕ) :
    momentForm γ m n ((X : ℂ[X]) ^ k) = newton γ m n k := by
  unfold momentForm newton
  simp [Polynomial.eval_pow, Polynomial.eval_X]

lemma momentForm_nodal (γ : ℕ → ℂ) (m : ℕ → ℕ) (n q : ℕ) :
    momentForm γ m n ((X : ℂ[X]) ^ q * nodalPoly γ n) = 0 := by
  unfold momentForm
  apply Finset.sum_eq_zero
  intro j hj
  have : (nodalPoly γ n).eval (γ j) = 0 := by
    unfold nodalPoly
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero hj (by simp)
  simp [Polynomial.eval_mul, this]

lemma momentForm_add (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (P Q : ℂ[X]) :
    momentForm γ m n (P + Q) = momentForm γ m n P + momentForm γ m n Q := by
  unfold momentForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp [Polynomial.eval_add, mul_add]

lemma momentForm_smul (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (c : ℂ) (P : ℂ[X]) :
    momentForm γ m n (Polynomial.C c * P) = c * momentForm γ m n P := by
  unfold momentForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Polynomial.eval_mul, Polynomial.eval_C]
  ring

lemma momentForm_sum (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → ℂ[X]) :
    momentForm γ m n (∑ i ∈ s, f i) = ∑ i ∈ s, momentForm γ m n (f i) := by
  unfold momentForm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp [Polynomial.eval_finsetSum, Finset.mul_sum]

lemma PiPoly_eq_det (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    PiPoly γ m n =
      C ((Delta γ m n n)⁻¹) *
        (borderMat (C : ℂ →+* ℂ[X]) γ m n (fun q => (X : ℂ[X]) ^ (q : ℕ))).det := by
  unfold PiPoly borderMat
  rfl

lemma momentForm_C_mul (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (c : ℂ) (P : ℂ[X]) :
    momentForm γ m n (C c * P) = c * momentForm γ m n P := by
  unfold momentForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  ring


lemma det_borderMat_cofac {R : Type*} [CommRing R] (f : ℂ →+* R)
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (r : Fin (n + 1) → R) :
    (borderMat f γ m n r).det = ∑ p, r p * f (cofac γ m n p) := by
  rw [Matrix.det_succ_row (borderMat f γ m n r) (Fin.last n)]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : borderMat f γ m n r (Fin.last n) j = r j := by
    simp [borderMat]
  have h2 : (borderMat f γ m n r).submatrix (Fin.last n).succAbove j.succAbove =
      (borderMat f γ m n 0).submatrix (Fin.last n).succAbove j.succAbove := by
    ext a b
    simp [borderMat, Fin.succAbove_last]
  have h3 : ((borderMat f γ m n 0).submatrix (Fin.last n).succAbove j.succAbove).det =
      f (((borderMat (RingHom.id ℂ) γ m n 0).submatrix
        (Fin.last n).succAbove j.succAbove).det) := by
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp [borderMat, Fin.succAbove_last]
  rw [h1, h2, h3]
  simp [cofac]
  ring

lemma PiPoly_eq_sum (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    PiPoly γ m n =
      C ((Delta γ m n n)⁻¹) *
        ∑ p : Fin (n + 1), C (cofac γ m n p) * (X : ℂ[X]) ^ (p : ℕ) := by
  rw [PiPoly_eq_det, det_borderMat_cofac (C : ℂ →+* ℂ[X])]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

lemma momentForm_PiPoly (γ : ℕ → ℂ) (m : ℕ → ℕ) (n q : ℕ) (hq : q < n)
    (_ : Delta γ m n n ≠ 0) :
    momentForm γ m n ((X : ℂ[X]) ^ q * PiPoly γ m n) = 0 := by
  have hzero : ∑ p : Fin (n + 1), newton γ m n (q + (p : ℕ)) * cofac γ m n p = 0 := by
    have h := det_borderMat_cofac (RingHom.id ℂ) γ m n
      (fun p => newton γ m n (q + (p : ℕ)))
    have hdet : (borderMat (RingHom.id ℂ) γ m n
        (fun p => newton γ m n (q + (p : ℕ)))).det = 0 := by
      refine Matrix.det_zero_of_row_eq
        (i := (⟨q, by omega⟩ : Fin (n + 1))) (j := Fin.last n) ?_ ?_
      · intro h'
        have := congrArg Fin.val h'
        simp at this
        omega
      · ext x
        simp [borderMat, hq]
    simpa [hdet] using h.symm
  rw [PiPoly_eq_sum, mul_left_comm, momentForm_C_mul, Finset.mul_sum]
  have hterm : ∀ p : Fin (n + 1),
      (X : ℂ[X]) ^ q * (C (cofac γ m n p) * (X : ℂ[X]) ^ (p : ℕ)) =
        C (cofac γ m n p) * (X : ℂ[X]) ^ (q + (p : ℕ)) := by
    intro p
    rw [pow_add]
    ring
  simp_rw [hterm]
  rw [momentForm_sum]
  simp_rw [momentForm_C_mul, momentForm_X_pow]
  have : ∑ p : Fin (n + 1), cofac γ m n p * newton γ m n (q + (p : ℕ)) = 0 := by
    simpa [mul_comm] using hzero
  rw [this, mul_zero]

lemma cofac_last (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    cofac γ m n (Fin.last n) = Delta γ m n n := by
  unfold cofac Delta borderMat
  simp only [Fin.val_last, Even.add_self, Even.neg_pow, one_pow, RingHom.id_apply,
    Pi.zero_apply, Fin.succAbove_last, one_mul]
  congr 1
  ext p q
  simp [Matrix.submatrix_apply]


lemma momentForm_sub (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (P Q : ℂ[X]) :
    momentForm γ m n (P - Q) = momentForm γ m n P - momentForm γ m n Q := by
  unfold momentForm
  simp only [Polynomial.eval_sub, mul_sub, Finset.sum_sub_distrib]

lemma degree_sub_lt_of_monic {P Q : ℂ[X]} {n : ℕ}
    (hP : P.Monic) (hQ : Q.Monic) (hPd : P.natDegree = n) (hQd : Q.natDegree = n)
    (_ : 0 < n) : (P - Q).degree < n := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hdeg : P.degree = Q.degree := by
    rw [Polynomial.degree_eq_natDegree hP0, Polynomial.degree_eq_natDegree hQ.ne_zero,
      hPd, hQd]
  have hlc : P.leadingCoeff = Q.leadingCoeff := by
    rw [hP, hQ]
  have h := Polynomial.degree_sub_lt_left hdeg hP0 hlc
  rw [Polynomial.degree_eq_natDegree hP0, hPd] at h
  exact h

lemma PiPoly_monic_natDegree (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hΔ : Delta γ m n n ≠ 0) :
    (PiPoly γ m n).Monic ∧ (PiPoly γ m n).natDegree = n := by
  rw [PiPoly_eq_sum]
  set S : ℂ[X] := ∑ p : Fin (n + 1), C (cofac γ m n p) * (X : ℂ[X]) ^ (p : ℕ) with hS
  have hSdeg : S.natDegree ≤ n := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun p _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    exact Nat.lt_succ_iff.mp p.isLt
  have hScoeff : S.coeff n = Delta γ m n n := by
    rw [hS, Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, cofac_last]
    · intro p _ hp
      have : (p : ℕ) ≠ n := fun h => hp (Fin.ext (by simpa using h))
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, this.symm]
    · simp
  have hcoeff : (C ((Delta γ m n n)⁻¹) * S).coeff n = 1 := by
    rw [Polynomial.coeff_C_mul, hScoeff, inv_mul_cancel₀ hΔ]
  have hne : C ((Delta γ m n n)⁻¹) ≠ (0 : ℂ[X]) := by
    simpa using hΔ
  have hdeg : (C ((Delta γ m n n)⁻¹) * S).natDegree ≤ n := by
    rw [Polynomial.natDegree_C_mul (by simpa using hΔ)]
    exact hSdeg
  have hnat : (C ((Delta γ m n n)⁻¹) * S).natDegree = n :=
    le_antisymm hdeg (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact one_ne_zero))
  refine ⟨?_, hnat⟩
  unfold Polynomial.Monic Polynomial.leadingCoeff
  rw [hnat, hcoeff]

lemma poly_zero_of_orth (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hH : (Hn γ m n).det ≠ 0) (R : ℂ[X]) (hR : R.degree < n)
    (horth : ∀ q < n, momentForm γ m n ((X : ℂ[X]) ^ q * R) = 0) :
    R = 0 := by
  set a : Fin n → ℂ := fun p => R.coeff p with ha
  have hR' : R = ∑ p : Fin n, C (a p) * (X : ℂ[X]) ^ (p : ℕ) := by
    by_cases hR0 : R = 0
    · subst hR0
      simp [a]
    · have hnd : R.natDegree < n :=
        (Polynomial.natDegree_lt_iff_degree_lt hR0).mpr hR
      rw [Polynomial.as_sum_range' R n hnd, ← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Polynomial.C_mul_X_pow_eq_monomial]
  have hmul : (Hn γ m n).mulVec a = 0 := by
    ext q
    have h := horth q q.isLt
    rw [hR', Finset.mul_sum] at h
    simp only [Matrix.mulVec, dotProduct, Hn, Matrix.of_apply, Pi.zero_apply]
    simp_rw [← mul_assoc, mul_comm ((X : ℂ[X]) ^ (q : ℕ)), mul_assoc,
      ← pow_add] at h
    rw [momentForm_sum] at h
    simp_rw [momentForm_C_mul, momentForm_X_pow] at h
    simpa [mul_comm] using h
  have ha0 : a = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero hH hmul
  rw [hR']
  simp [ha0]

-- Heine-Szegő ---
lemma PiPoly_eq_nodal (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hH : (Hn γ m n).det ≠ 0) (hΔ : Delta γ m n n ≠ 0) :
    PiPoly γ m n = nodalPoly γ n := by
  obtain ⟨hmonic, hdeg⟩ := PiPoly_monic_natDegree γ m n hΔ
  have hmonicW : (nodalPoly γ n).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _
  have hdegW : (nodalPoly γ n).natDegree = n := by
    unfold nodalPoly
    rw [Polynomial.natDegree_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _]
    simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : PiPoly γ m 0 = 1 := by
      have hc : (PiPoly γ m 0).coeff 0 = 1 := by
        have := hmonic.coeff_natDegree
        rwa [hdeg] at this
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg, hc, map_one]
    have h2 : nodalPoly γ 0 = 1 := by
      have hc : (nodalPoly γ 0).coeff 0 = 1 := by
        have := hmonicW.coeff_natDegree
        rwa [hdegW] at this
      rw [Polynomial.eq_C_of_natDegree_eq_zero hdegW, hc, map_one]
    rw [h1, h2]
  · have hRdeg : (PiPoly γ m n - nodalPoly γ n).degree < n :=
      degree_sub_lt_of_monic hmonic hmonicW hdeg hdegW hn
    have horth : ∀ q < n,
        momentForm γ m n ((X : ℂ[X]) ^ q * (PiPoly γ m n - nodalPoly γ n)) = 0 := by
      intro q hq
      rw [mul_sub, momentForm_sub,
        momentForm_PiPoly γ m n q hq hΔ, momentForm_nodal, sub_zero]
    have hR0 := poly_zero_of_orth γ m n hH _ hRdeg horth
    exact sub_eq_zero.mp hR0

lemma I_mul_gamma (γ : ℕ → ℂ) (j : ℕ) :
    Complex.I * γ j = sZero γ j - 1 / 2 := by
  unfold sZero; ring

lemma re_sZero (γ : ℕ → ℂ) (j : ℕ) : (sZero γ j).re = 1 / 2 - (γ j).im := by
  rw [sZero]
  simp
  ring

lemma im_sZero (γ : ℕ → ℂ) (j : ℕ) : (sZero γ j).im = (γ j).re := by
  unfold sZero; simp

lemma re_sZero_eq_half_iff (γ : ℕ → ℂ) (n : ℕ) :
    (sZero γ n).re = 1 / 2 ↔ (γ n).im = 0 := by
  rw [re_sZero]; constructor <;> intro h <;> linarith

lemma re_sZero_step (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hV : IsUnit (Vn γ n).det) (hM : IsUnit (Mn m n).det)
    (Hr Hs : Matrix (Fin n) (Fin n) ℝ)
    (hRpos : Hr.PosDef) (hssymm : Hs.IsSymm)
    (hH : Hn γ m n = Hr.map (algebraMap ℝ ℂ))
    (hHs : Hn_shift γ m n = Hs.map (algebraMap ℝ ℂ))
    (hshift : Hn_shift γ m n = Hn γ m n * Cn γ m n) :
    (sZero γ n).re = 1 / 2 := by
  rw [re_sZero_eq_half_iff]
  exact gamma_n_real_of_data
    γ m n hn hV hM Hr Hs hRpos hssymm hH hHs hshift


theorem re_sZero_all (Xi : ℂ → ℂ) (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration Xi γ m)
    (hpos : HankelPositive γ m)
    (htrans : ∀ n, 3 ≤ n → (∀ j, 1 ≤ j → j ≤ n - 1 → (γ j).im = 0) →
      ((γ n).im = 0 ↔
        ((∀ k, k ≤ 2 * n - 1 → (newton γ m n k).im = 0) ∧
          0 < (Schur γ m n).re ∧ (Schur γ m n).im = 0 ∧
          Schur γ m n = Delta γ m n n / Delta γ m n (n - 1) ∧
          (∀ r, 1 ≤ r → r ≤ n - 1 →
            0 < (Delta γ m n r).re ∧ (Delta γ m n r).im = 0)))) :
    ∀ n, 1 ≤ n → (sZero γ n).re = 1 / 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rw [re_sZero_eq_half_iff]
    by_cases h1 : n = 1
    · subst h1; exact henum.real_one
    by_cases h2 : n = 2
    · subst h2; exact henum.real_two
    have h3 : 3 ≤ n := by omega
    have hreal : ∀ j, 1 ≤ j → j ≤ n - 1 → (γ j).im = 0 := by
      intro j hj1 hjn
      have := ih j (by omega) hj1
      exact (re_sZero_eq_half_iff γ j).mp this
    refine (htrans n h3 hreal).mpr ?_
    obtain ⟨hmom, hrk⟩ := hpos n (by omega)
    obtain ⟨hmom, hrk⟩ := hpos n (by omega)
    have hn1 : 1 ≤ n - 1 := by omega
    obtain ⟨hDn_re, hDn_im⟩ := hrk n hn (le_refl n)
    obtain ⟨hDm_re, hDm_im⟩ := hrk (n - 1) hn1 (by omega)
    have hS : Schur γ m n = Delta γ m n n / Delta γ m n (n - 1) := by
      have hne : Delta γ m n (n - 1) ≠ 0 := by
        intro h
        rw [h] at hDm_re
        simp at hDm_re
      have hdet : Delta γ m n (n - 1) = (Hsub γ m n).det := rfl
      have hA : IsUnit (Hsub γ m n).det := by
        rw [← hdet]
        exact isUnit_iff_ne_zero.mpr hne
      have hJ := Delta_eq_jacobi γ m n hn hA
      rw [hJ]
      field_simp
    have hquot_im : (Delta γ m n n / Delta γ m n (n - 1)).im = 0 := by
      rw [Complex.div_im, hDn_im, hDm_im]
      simp
    have hquot_re : 0 < (Delta γ m n n / Delta γ m n (n - 1)).re := by
      rw [Complex.div_re, hDn_im, hDm_im]
      simp only [mul_zero, zero_div, add_zero]
      have hnorm : 0 < Complex.normSq (Delta γ m n (n - 1)) :=
        Complex.normSq_pos.mpr (fun h => by simp [h] at hDm_re)
      exact div_pos (mul_pos hDn_re hDm_re) hnorm
    refine ⟨hmom, ?_, ?_, hS, fun r hr1 hrn => hrk r hr1 (by omega)⟩
    · rw [hS]; exact hquot_re
    · rw [hS]; exact hquot_im


theorem etape4_synthese
    (Xi : ℂ → ℂ) (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration Xi γ m)
    (hV : ∀ n, 2 ≤ n → IsUnit (Vn γ n).det)
    (hM : ∀ n, 2 ≤ n → IsUnit (Mn m n).det)
    (hH : ∀ n, 2 ≤ n → (Hn γ m n).det ≠ 0)
    (hΔ : ∀ n, 2 ≤ n → Delta γ m n n ≠ 0) :
    ∀ n, 2 ≤ n →
      γ n = (Cn γ m n).trace - ∑ j ∈ Finset.Icc 1 (n - 1), γ j ∧
      γ n = (newton γ m n 1 - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ) * γ j) /
            (newton γ m n 0 - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ)) ∧
      PiPoly γ m n = (X - C (γ n)) * ∏ j ∈ Finset.Icc 1 (n - 1), (X - C (γ j)) := by
  intro n hn
  refine ⟨gamma_n_eq_trace γ m n (by omega) (hV n hn) (hM n hn),
          gamma_n_eq_moments γ m n (by omega) (henum.mult_pos n (by omega)), ?_⟩
  rw [PiPoly_eq_nodal γ m n (hH n hn) (hΔ n hn)]
  unfold nodalPoly
  have hsplit : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : n ∉ Finset.Icc 1 (n - 1) := by simp [Finset.mem_Icc]; omega
  rw [hsplit, Finset.prod_insert hnot]

lemma prod_fin_succ_eq_Icc (f : ℕ → ℂ) (n : ℕ) :
    ∏ j : Fin n, f ((j : ℕ) + 1) = ∏ j ∈ Finset.Icc 1 n, f j := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]

lemma det_Vn_sq (γ : ℕ → ℂ) (n : ℕ) :
    (Vn γ n).det ^ 2 =
      ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 n,
        (if i < j then (γ j - γ i) ^ 2 else 1) := by
  induction n with
  | zero => simp [Vn, Matrix.det_isEmpty]
  | succ k ih =>
    rw [det_Vn_succ, mul_pow, ih]
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
    simp only [Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
    have hG : (∏ j : Fin k, (γ (k + 1) - γ ((j : ℕ) + 1)))^2
        = ∏ x ∈ Finset.Icc 1 k, (if x < k + 1 then (γ (k + 1) - γ x) ^ 2 else 1) := by
      rw [← Finset.prod_pow]
      rw [prod_fin_succ_eq_Icc (fun x => (γ (k + 1) - γ x) ^ 2) k]
      refine Finset.prod_congr rfl fun j hj => ?_
      have : j < k + 1 := by
        have := (Finset.mem_Icc.mp hj).2
        omega
      simp [this]
    have hlast : (if k + 1 < k + 1 then (γ (k + 1) - γ (k + 1)) ^ 2 else 1) = 1 := by
      simp
    have hH : (∏ j ∈ Finset.Icc 1 k, if k + 1 < j then (γ j - γ (k + 1)) ^ 2 else 1) = 1 := by
      refine Finset.prod_eq_one fun j hj => ?_
      have : j ≤ k := (Finset.mem_Icc.mp hj).2
      simp [show ¬ (k + 1 < j) by omega]
    rw [hlast, hH, mul_one, Finset.prod_mul_distrib, hG]
    ring

lemma sum_Icc_eq_sum_fin (f : ℕ → ℂ) (n : ℕ) :
    ∑ j ∈ Finset.Icc 1 n, f j = ∑ i : Fin n, f ((i : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Fin.sum_univ_castSucc]
    simp

lemma Hn_eq_VMV (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    Hn γ m n = (Vn γ n)ᵀ * Mn m n * Vn γ n := by
  ext p q
  simp only [Hn, Vn, Mn, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal_apply]
  have hinner : ∀ j : Fin n,
      (∑ j_1 : Fin n, γ (↑j_1 + 1) ^ (p : ℕ) *
        if j_1 = j then ((m (↑j_1 + 1) : ℕ) : ℂ) else 0)
      = γ (↑j + 1) ^ (p : ℕ) * ((m (↑j + 1) : ℕ) : ℂ) := by
    intro j
    simp [mul_ite, Finset.sum_ite_eq']
  simp only [hinner]
  unfold newton
  rw [sum_Icc_eq_sum_fin (fun j => ((m j : ℕ) : ℂ) * γ j ^ ((p : ℕ) + (q : ℕ))) n]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_add]
  ring

lemma Hn_shift_eq_VMDV (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    Hn_shift γ m n = (Vn γ n)ᵀ * Mn m n * Dn' γ n * Vn γ n := by
  ext p q
  simp only [Hn_shift, Vn, Mn, Dn', Matrix.of_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.diagonal_apply]
  have hin : ∀ j_1 : Fin n,
      (∑ j : Fin n, γ (↑j + 1) ^ (p : ℕ) *
        if j = j_1 then ((m (↑j + 1) : ℕ) : ℂ) else 0)
      = γ (↑j_1 + 1) ^ (p : ℕ) * ((m (↑j_1 + 1) : ℕ) : ℂ) := by
    intro j_1
    simp [mul_ite]
  simp only [hin]
  have hout : ∀ j : Fin n,
      (∑ j_1 : Fin n, γ (↑j_1 + 1) ^ (p : ℕ) * ((m (↑j_1 + 1) : ℕ) : ℂ) *
        if j_1 = j then γ (↑j_1 + 1) else 0)
      = γ (↑j + 1) ^ (p : ℕ) * ((m (↑j + 1) : ℕ) : ℂ) * γ (↑j + 1) := by
    intro j
    simp [mul_ite, Finset.sum_ite_eq']
  simp only [hout]
  unfold newton
  rw [sum_Icc_eq_sum_fin
    (fun j => ((m j : ℕ) : ℂ) * γ j ^ ((p : ℕ) + (q : ℕ) + 1)) n]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_succ, pow_add]
  ring

lemma prod_sq_fin_eq_Icc (γ : ℕ → ℂ) (k : ℕ) :
    ∏ j : Fin k, (γ (k + 1) - γ ((j : ℕ) + 1)) ^ 2
      = ∏ j ∈ Finset.Icc 1 k, (γ (k + 1) - γ j) ^ 2 :=
  prod_fin_succ_eq_Icc (fun x => (γ (k + 1) - γ x) ^ 2) k

lemma Schur_eq_div (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (hD : Delta γ m n (n - 1) ≠ 0) :
    Schur γ m n = Delta γ m n n / Delta γ m n (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : k + 1 - 1 = k := by omega
  rw [hk] at hD ⊢
  have key : Delta γ m (k + 1) (k + 1) =
      Delta γ m (k + 1) k * Schur γ m (k + 1) := by
    have hdet : Delta γ m (k + 1) k = (Hsub γ m (k + 1)).det := rfl
    have hA : IsUnit (Hsub γ m (k + 1)).det := by
      rw [← hdet]
      exact isUnit_iff_ne_zero.mpr hD
    have := Delta_eq_jacobi γ m (k + 1) hn hA
    simpa only [Nat.add_sub_cancel] using this
  rw [key]
  field_simp

lemma Delta_self_eq_det_Hn (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    Delta γ m n n = (Hn γ m n).det := by
  rw [Delta_self_eq, det_Hn_eq]

lemma div_im_eq_zero_of_im_zero {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0) :
    (a / b).im = 0 := by
  have ha' : a = (a.re : ℂ) := Complex.ext (by simp) (by simp [ha])
  have hb' : b = (b.re : ℂ) := Complex.ext (by simp) (by simp [hb])
  rw [ha', hb', ← Complex.ofReal_div]
  exact Complex.ofReal_im _

lemma Delta_self_im_zero (Xi : ℂ → ℂ) (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (_ : ZeroEnumeration Xi γ m) (k : ℕ)
    (hreal : ∀ j, 1 ≤ j → j ≤ k → (γ j).im = 0)
    (hk1 : (γ (k + 1)).im = 0) :
    (Delta γ m (k + 1) (k + 1)).im = 0 := by
  rw [Delta_self_eq]
  have hall : ∀ j, 1 ≤ j → j ≤ k + 1 → (γ j).im = 0 := by
    intro j hj1 hj2
    rcases Nat.lt_or_ge j (k + 1) with hlt | hge
    · exact hreal j hj1 (by omega)
    · have : j = k + 1 := by omega
      rw [this]
      exact hk1
  have hV : ((Vn γ (k + 1)).det).im = 0 := by
    set R : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
      Matrix.of fun i j => ((γ ((i : ℕ) + 1)).re) ^ (j : ℕ) with hR
    have hmap : Vn γ (k + 1) = R.map (algebraMap ℝ ℂ) := by
      ext i j
      simp only [Vn, hR, Matrix.of_apply, Matrix.map_apply]
      have hγ : γ ((i : ℕ) + 1) = (((γ ((i : ℕ) + 1)).re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp [hall ((i : ℕ) + 1) (by omega) (by have := i.isLt; omega)]
      rw [hγ]
      simp
    rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact Complex.ofReal_im _
  have hV' : (Vn γ (k + 1)).det = (((Vn γ (k + 1)).det.re : ℝ) : ℂ) :=
    Complex.ext (by simp) (by simp [hV])
  rw [hV']
  have : (∏ j : Fin (k + 1), (m ((j : ℕ) + 1) : ℂ)) =
      ((∏ j : Fin (k + 1), (m ((j : ℕ) + 1) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [this, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  exact Complex.ofReal_im _

lemma det_im_zero_of_entries_real {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, (A i j).im = 0) : A.det.im = 0 := by
  have hAeq : A = (Matrix.of fun i j => (A i j).re).map (algebraMap ℝ ℂ) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply]
    apply Complex.ext
    · simp
    · simp [hA i j]
  rw [hAeq]
  have := (algebraMap ℝ ℂ).map_det (Matrix.of fun i j => (A i j).re)
  simp only [RingHom.mapMatrix_apply] at this
  rw [← this]
  simp

lemma step3_equiv_succ (Xi : ℂ → ℂ) (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (h : ZeroEnumeration Xi γ m) (k : ℕ) (hn : 3 ≤ k + 1)
    (hreal : ∀ j, 1 ≤ j → j ≤ k + 1 - 1 → (γ j).im = 0) :
    (γ (k + 1)).im = 0 ↔
      ((∀ i, i ≤ 2 * (k + 1) - 1 → (newton γ m (k + 1) i).im = 0) ∧
        0 < (Schur γ m (k + 1)).re ∧ (Schur γ m (k + 1)).im = 0 ∧
        Schur γ m (k + 1) = Delta γ m (k + 1) (k + 1) / Delta γ m (k + 1) (k + 1 - 1) ∧
        (∀ r, 1 ≤ r → r ≤ k + 1 - 1 →
          0 < (Delta γ m (k + 1) r).re ∧ (Delta γ m (k + 1) r).im = 0)) := by
  have H := step3_equiv Xi γ m h (k + 1) hn hreal
  rw [H]
  constructor
  · rintro ⟨hmom, hmin, hS⟩
    have hDne : Delta γ m (k + 1) (k + 1 - 1) ≠ 0 := by
      intro h0
      have hpos := (hmin (k + 1 - 1) (by omega) le_rfl).1
      rw [h0] at hpos
      simp at hpos
    have hSeq : Schur γ m (k + 1) =
        Delta γ m (k + 1) (k + 1) / Delta γ m (k + 1) (k + 1 - 1) :=
      Schur_eq_div γ m (k + 1) (by omega) hDne
    rw [← hSeq] at hS
    have hDn : (Delta γ m (k + 1) (k + 1)).im = 0 := by
      have hdet : Delta γ m (k + 1) (k + 1) = (Hn γ m (k + 1)).det :=
        Delta_self_eq_det_Hn γ m (k + 1)
      rw [hdet]
      apply det_im_zero_of_entries_real
      intro p q
      simp only [Hn, Matrix.of_apply]
      apply hmom
      have hp := p.isLt
      have hq := q.isLt
      omega
    have hDk : (Delta γ m (k + 1) (k + 1 - 1)).im = 0 :=
      (hmin (k + 1 - 1) (by omega) le_rfl).2
    have hSim : (Schur γ m (k + 1)).im = 0 := by
      rw [hSeq, Complex.div_im, hDn, hDk]
      simp
    exact ⟨hmom, hS, hSim, hSeq, hmin⟩
  · rintro ⟨hmom, hSre, hSim, hSeq, hmin⟩
    refine ⟨hmom, hmin, ?_⟩
    rw [← hSeq]
    exact hSre

lemma Vn_Cn_Vn_inv (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hV : (Vn γ n).det ≠ 0) (hM : (Mn m n).det ≠ 0) :
    Vn γ n * Cn γ m n * (Vn γ n)⁻¹ = Dn' γ n := by
  have hVu : IsUnit (Vn γ n).det := isUnit_iff_ne_zero.mpr hV
  have hMu : IsUnit (Mn m n).det := isUnit_iff_ne_zero.mpr hM
  have hVTu : IsUnit (Vn γ n)ᵀ.det := by
    rw [Matrix.det_transpose]; exact hVu
  have hHu : IsUnit (Hn γ m n).det := by
    rw [Hn_eq_VMV, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact (hVu.mul hMu).mul hVu
  have hinv : (Hn γ m n)⁻¹ * Hn γ m n = 1 := Matrix.nonsing_inv_mul _ hHu
  have key : Vn γ n * Cn γ m n = Dn' γ n * Vn γ n := by
    unfold Cn
    have h1 : Hn γ m n * ((Vn γ n)⁻¹ * Dn' γ n * Vn γ n) = Hn_shift γ m n := by
      rw [Hn_eq_VMV, Hn_shift_eq_VMDV]
      calc (Vn γ n)ᵀ * Mn m n * Vn γ n * ((Vn γ n)⁻¹ * Dn' γ n * Vn γ n)
          = (Vn γ n)ᵀ * Mn m n * (Vn γ n * (Vn γ n)⁻¹) * Dn' γ n * Vn γ n := by
            simp only [Matrix.mul_assoc]
        _ = (Vn γ n)ᵀ * Mn m n * Dn' γ n * Vn γ n := by
            rw [Matrix.mul_nonsing_inv _ hVu, Matrix.mul_one]
    have h2 : (Hn γ m n)⁻¹ * Hn_shift γ m n = (Vn γ n)⁻¹ * Dn' γ n * Vn γ n := by
      rw [← h1, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    rw [h2]
    calc Vn γ n * ((Vn γ n)⁻¹ * Dn' γ n * Vn γ n)
        = (Vn γ n * (Vn γ n)⁻¹) * Dn' γ n * Vn γ n := by
          simp only [Matrix.mul_assoc]
      _ = Dn' γ n * Vn γ n := by
          rw [Matrix.mul_nonsing_inv _ hVu, Matrix.one_mul]
  calc Vn γ n * Cn γ m n * (Vn γ n)⁻¹
      = (Dn' γ n * Vn γ n) * (Vn γ n)⁻¹ := by rw [key]
    _ = Dn' γ n := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hVu, Matrix.mul_one]

theorem recurrence_zeros_hankel_riemann
    (Xi : ℂ → ℂ) (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration Xi γ m) :
    -- (1) inversibility and diagonalisation
    (∀ n, 2 ≤ n →
      IsUnit (Hn γ m n).det ∧
      Delta γ m n n =
        (∏ j ∈ Finset.Icc 1 n, (m j : ℂ)) *
          ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 n,
            (if i < j then (γ j - γ i) ^ 2 else 1) ∧
      Delta γ m n n ≠ 0 ∧
      IsUnit (Vn γ n).det ∧
      Vn γ n * Cn γ m n * (Vn γ n)⁻¹ = Dn' γ n) ∧
    -- (2) initialisation on the second rank
    ((∀ k, (newton γ m 2 k).im = 0) ∧
      0 < (Delta γ m 2 1).re ∧ (Delta γ m 2 1).im = 0 ∧
      Delta γ m 2 1 = (m 1 : ℂ) + (m 2 : ℂ) ∧
      Delta γ m 2 2 = (m 1 : ℂ) * (m 2 : ℂ) * (γ 2 - γ 1) ^ 2 ∧
      0 < (Delta γ m 2 2).re ∧ (Delta γ m 2 2).im = 0 ∧
      (Hn γ m 2).IsHermitian) ∧
    -- (3) transition and DefPos
    (∀ n, 3 ≤ n → (∀ j, 1 ≤ j → j ≤ n - 1 → (γ j).im = 0) →
      (∀ r, 1 ≤ r → r ≤ n - 1 → 0 < (Delta γ m (n - 1) r).re ∧
        (Delta γ m (n - 1) r).im = 0) ∧
      Delta γ m n n =
        (m n : ℂ) * Delta γ m (n - 1) (n - 1) *
          ∏ j ∈ Finset.Icc 1 (n - 1), (γ n - γ j) ^ 2 ∧
      ((γ n).im = 0 ↔
        ((∀ k, k ≤ 2 * n - 1 → (newton γ m n k).im = 0) ∧
          0 < (Schur γ m n).re ∧ (Schur γ m n).im = 0 ∧
          Schur γ m n = Delta γ m n n / Delta γ m n (n - 1) ∧
          (∀ r, 1 ≤ r → r ≤ n - 1 → 0 < (Delta γ m n r).re ∧ (Delta γ m n r).im = 0)))) ∧
    -- (4) explicite caracterisation of γ_n and conclusion of Re(s_n)
    (∀ n, 2 ≤ n →
      γ n = (Cn γ m n).trace - ∑ j ∈ Finset.Icc 1 (n - 1), γ j ∧
      γ n = (newton γ m n 1 - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ) * γ j) /
            (newton γ m n 0 - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ)) ∧
      PiPoly γ m n = (X - C (γ n)) * ∏ j ∈ Finset.Icc 1 (n - 1), (X - C (γ j)) ∧
      (∀ z : ℂ, (PiPoly γ m n).eval z = 0 → z ≠ γ n →
        ∃ j, 1 ≤ j ∧ j ≤ n - 1 ∧ z = γ j)) ∧
    (HankelPositive γ m →
      ∀ n, 1 ≤ n → ((1 : ℂ) / 2 + Complex.I * γ n).re = 1 / 2) := by
  have hdist : ∀ n, ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → γ i = γ j → i = j :=
    fun n i j hi _ hj _ h => henum.injective i j hi hj h
  have h1 : ∀ n, 2 ≤ n →
      IsUnit (Hn γ m n).det ∧
      Delta γ m n n =
        (∏ j ∈ Finset.Icc 1 n, (m j : ℂ)) *
          ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 n,
            (if i < j then (γ j - γ i) ^ 2 else 1) ∧
      Delta γ m n n ≠ 0 ∧
      IsUnit (Vn γ n).det ∧
      Vn γ n * Cn γ m n * (Vn γ n)⁻¹ = Dn' γ n := by
    intro n hn
    have hV : (Vn γ n).det ≠ 0 := Vn_det_ne_zero γ n (hdist n)
    have hprodm : (∏ j : Fin n, (m ((j : ℕ) + 1) : ℂ)) =
        ∏ j ∈ Finset.Icc 1 n, (m j : ℂ) :=
      prod_fin_succ_eq_Icc (fun j => (m j : ℂ)) n
    have hDelta : Delta γ m n n =
        (∏ j ∈ Finset.Icc 1 n, (m j : ℂ)) *
          ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 n,
            (if i < j then (γ j - γ i) ^ 2 else 1) := by
      rw [Delta_self_eq, hprodm]
      congr 1
      exact det_Vn_sq γ n
    have hD : Delta γ m n n ≠ 0 := by
      rw [Delta_self_eq]
      refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr ?_) (pow_ne_zero 2 hV)
      intro j _
      have : 1 ≤ m ((j : ℕ) + 1) := henum.mult_pos _ (by omega)
      exact_mod_cast (by omega : m ((j : ℕ) + 1) ≠ 0)
    have hHdet : (Hn γ m n).det = Delta γ m n n := rfl
    refine ⟨?_, hDelta, hD, ?_, ?_⟩
    · rw [hHdet]; exact isUnit_iff_ne_zero.mpr hD
    · exact isUnit_iff_ne_zero.mpr hV
    · have hM0 : (Mn m n).det ≠ 0 := by
        unfold Mn
        rw [Matrix.det_diagonal]
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro j _
        have hpos : 1 ≤ m ((j : ℕ) + 1) := henum.mult_pos _ (by omega)
        exact_mod_cast (by omega : m ((j : ℕ) + 1) ≠ 0)
      exact Vn_Cn_Vn_inv γ m n hV hM0
  have h2 := init_rank_two Xi γ m henum
  have h2' : (∀ k, (newton γ m 2 k).im = 0) ∧
      0 < (Delta γ m 2 1).re ∧ (Delta γ m 2 1).im = 0 ∧
      Delta γ m 2 1 = (m 1 : ℂ) + (m 2 : ℂ) ∧
      Delta γ m 2 2 = (m 1 : ℂ) * (m 2 : ℂ) * (γ 2 - γ 1) ^ 2 ∧
      0 < (Delta γ m 2 2).re ∧ (Delta γ m 2 2).im = 0 ∧
      (Hn γ m 2).IsHermitian := by
    obtain ⟨hk, ⟨hD1r, hD1i⟩, ⟨hD2r, hD2i⟩, g₁, g₂, hne, hg1, hg2, hpd, hH⟩ := h2
    refine ⟨hk, hD1r, hD1i, ?_, ?_, hD2r, hD2i, ?_⟩
    · simp [Delta, newton, Finset.sum_Icc_succ_top]
    · simp [Delta, newton, Matrix.det_fin_two, Finset.sum_Icc_succ_top]
      ring
    · rw [hH]
      have hs : (H2R (m 1) (m 2) g₁ g₂).IsHermitian := hpd.isHermitian
      ext i j
      simpa [Matrix.IsHermitian, Matrix.conjTranspose_apply] using
        (congrArg (fun A => (algebraMap ℝ ℂ) (A j i)) hs.eq).symm
  have h3 : ∀ n, 3 ≤ n → (∀ j, 1 ≤ j → j ≤ n - 1 → (γ j).im = 0) →
      (∀ r, 1 ≤ r → r ≤ n - 1 → 0 < (Delta γ m (n - 1) r).re ∧
        (Delta γ m (n - 1) r).im = 0) ∧
      Delta γ m n n =
        (m n : ℂ) * Delta γ m (n - 1) (n - 1) *
          ∏ j ∈ Finset.Icc 1 (n - 1), (γ n - γ j) ^ 2 ∧
      ((γ n).im = 0 ↔
        ((∀ k, k ≤ 2 * n - 1 → (newton γ m n k).im = 0) ∧
          0 < (Schur γ m n).re ∧ (Schur γ m n).im = 0 ∧
          Schur γ m n = Delta γ m n n / Delta γ m n (n - 1) ∧
          (∀ r, 1 ≤ r → r ≤ n - 1 → 0 < (Delta γ m n r).re ∧
            (Delta γ m n r).im = 0))) := by
    intro n hn hreal
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have hk : k + 1 - 1 = k := by omega
    refine ⟨?_, ?_, ?_⟩
    · intro r hr1 hrk
      rw [hk] at hrk ⊢
      refine Delta_pos_of_real γ m k r hr1 hrk
        (fun j hj => henum.mult_pos j (Finset.mem_Icc.mp hj).1)
        (fun j hj1 hjk => hreal j hj1 (by omega)) ?_
      intro i hi j hj hij
      have hi' := Finset.mem_Icc.mp (Finset.mem_coe.mp hi)
      have hj' := Finset.mem_Icc.mp (Finset.mem_coe.mp hj)
      exact henum.injective i j hi'.1 hj'.1 hij
    · rw [hk]
      rw [delta_succ]
      congr 1
      exact prod_sq_fin_eq_Icc γ k
    · exact step3_equiv_succ Xi γ m henum k hn hreal
  have hM : ∀ n, 2 ≤ n → IsUnit (Mn m n).det := by
    intro n hn
    unfold Mn
    rw [Matrix.det_diagonal]
    rw [isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro j _
    have hpos : 1 ≤ m ((j : ℕ) + 1) := henum.mult_pos _ (by omega)
    exact_mod_cast (by omega : m ((j : ℕ) + 1) ≠ 0)
  have h4 := etape4_synthese Xi γ m henum
    (fun n hn => (h1 n hn).2.2.2.1) hM
    (fun n hn => (isUnit_iff_ne_zero.mp (h1 n hn).1))
    (fun n hn => (h1 n hn).2.2.1)
  have h4roots : ∀ n, 2 ≤ n → ∀ z : ℂ, (PiPoly γ m n).eval z = 0 → z ≠ γ n →
      ∃ j, 1 ≤ j ∧ j ≤ n - 1 ∧ z = γ j := by
    intro n hn z hz hne
    rw [(h4 n hn).2.2] at hz
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_prod, mul_eq_zero] at hz
    rcases hz with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp h
      rw [Finset.mem_Icc] at hj
      exact ⟨j, hj.1, hj.2, sub_eq_zero.mp hj0⟩
  have h4b : HankelPositive γ m → ∀ n, 1 ≤ n →
    ((1 : ℂ) / 2 + Complex.I * γ n).re = 1 / 2 := by
    intro hpos n hn
    have hs := re_sZero_all Xi γ m henum hpos
      (fun n hn hr => (h3 n hn hr).2.2) n hn
    have him := (re_sZero_eq_half_iff γ n).mp hs
    simp [Complex.add_re, Complex.mul_re, him]
  exact ⟨h1, h2', h3, fun n hn =>
    ⟨(h4 n hn).1, (h4 n hn).2.1, (h4 n hn).2.2, h4roots n hn⟩, h4b⟩








end InducRiemannZero
