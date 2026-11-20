import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.SchurDiagonalisation
import ThEqRiemann.EqTheorem.Vandermonde
import ThEqRiemann.RiemannProof.MatrixPassageTranslate

/-! -/
namespace SchurPassage

open Set Complex
open RiemannDef

lemma Mseq_succ (lam : ℕ → ℂ) (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) (n : ℕ) :
    Mseq lam u (n + 1) = versFin (bordee (Mseq lam u n) (u n) (lam (n + 1))) := rfl

lemma Pseq_succ (lam : ℕ → ℂ) (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) (n : ℕ) :
    Pseq lam u (n + 1) =
      versFin (passage (Pseq lam u n)
        (bVec lam (Pseq lam u n) (u n) (lam (n + 1))) 0 1) := rfl

lemma versFin_eq {n : ℕ} (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    versFin A = A.submatrix (eqFin n).symm (eqFin n).symm := rfl

lemma versFin_mul {n : ℕ} (A B : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    versFin (A * B) = versFin A * versFin B := by
  simp only [versFin_eq]
  rw [Matrix.submatrix_mul_equiv]

lemma versFin_inv {n : ℕ} (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    (versFin A)⁻¹ = versFin A⁻¹ := by
  simp only [versFin_eq]
  rw [Matrix.inv_submatrix_equiv]

lemma versFin_one {n : ℕ} :
    versFin (1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) = 1 := by
  simp only [versFin_eq]
  exact Matrix.submatrix_one_equiv _

lemma det_versFin {n : ℕ} (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    (versFin A).det = A.det := by
  simp only [versFin_eq]
  exact Matrix.det_submatrix_equiv_self _ _

lemma eqFin_symm_castSucc {n : ℕ} (i : Fin n) :
    (eqFin n).symm (Fin.castSucc i) = Sum.inl i := by
  rw [Equiv.symm_apply_eq]
  rfl

lemma eqFin_symm_last {n : ℕ} :
    (eqFin n).symm (Fin.last n) = Sum.inr (0 : Fin 1) := by
  rw [Equiv.symm_apply_eq]
  ext
  simp [eqFin, finSumFinEquiv]

lemma versFin_fromBlocks_11 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin n) ℂ) (D : Matrix (Fin 1) (Fin 1) ℂ)
    (k i : Fin n) :
    versFin (Matrix.fromBlocks A B C D) (Fin.castSucc k) (Fin.castSucc i) = A k i := by
  simp [versFin_eq, eqFin_symm_castSucc]

lemma versFin_fromBlocks_12 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin n) ℂ) (D : Matrix (Fin 1) (Fin 1) ℂ)
    (k : Fin n) :
    versFin (Matrix.fromBlocks A B C D) (Fin.castSucc k) (Fin.last n) = B k 0 := by
  simp [versFin_eq, eqFin_symm_castSucc, eqFin_symm_last]

lemma versFin_fromBlocks_21 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin n) ℂ) (D : Matrix (Fin 1) (Fin 1) ℂ)
    (i : Fin n) :
    versFin (Matrix.fromBlocks A B C D) (Fin.last n) (Fin.castSucc i) = C 0 i := by
  simp [versFin_eq, eqFin_symm_castSucc, eqFin_symm_last]

lemma versFin_fromBlocks_22 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n) (Fin 1) ℂ) (C : Matrix (Fin 1) (Fin n) ℂ) (D : Matrix (Fin 1) (Fin 1) ℂ) :
    versFin (Matrix.fromBlocks A B C D) (Fin.last n) (Fin.last n) = D 0 0 := by
  simp [versFin_eq, eqFin_symm_last]

lemma inv_diagonal_of_ne {n : ℕ} (v : Fin n → ℂ) (hv : ∀ i, v i ≠ 0) :
    (Matrix.diagonal v)⁻¹ = Matrix.diagonal (fun i => (v i)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hv i)

lemma smul_one_sub_diagonal {n : ℕ} (lam : ℂ) (l : Fin n → ℂ) :
    (lam • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal l) =
      Matrix.diagonal (fun i => lam - l i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

lemma inv_smul_one_sub_diagonal {n : ℕ} (lam : ℂ) (l : Fin n → ℂ) (hl : ∀ i, l i ≠ lam) :
    (lam • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal l)⁻¹ =
      Matrix.diagonal (fun i => (lam - l i)⁻¹) := by
  rw [smul_one_sub_diagonal]
  apply inv_diagonal_of_ne
  intro i h
  exact hl i (by linear_combination -h)

lemma Mseq_zero (lam : ℕ → ℂ) (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) :
    Mseq lam u 0 = Dn lam 0 := by
  ext i j
  have hi : i = 0 := Fin.ext (by omega)
  have hj : j = 0 := Fin.ext (by omega)
  subst hi; subst hj
  simp [Mseq, Dn]

lemma Dn_succ (lam : ℕ → ℂ) (n : ℕ) :
    Dn lam (n + 1) = versFin (diagBordee
      (fun i : Fin (n + 1) => lam i.val) (lam (n + 1))) := by
  ext i j
  refine Fin.lastCases ?_ (fun k => ?_) i <;>
  refine Fin.lastCases ?_ (fun l => ?_) j
  · simp [Dn, versFin_eq, diagBordee, eqFin_symm_last, scal]
  · have h : (Fin.last (n + 1)) ≠ Fin.castSucc l := (Fin.castSucc_lt_last l).ne'
    simp [Dn, versFin_eq, diagBordee, eqFin_symm_last, eqFin_symm_castSucc, scal,
      Matrix.diagonal_apply_ne _ h]
  · have h : (Fin.castSucc k) ≠ Fin.last (n + 1) := (Fin.castSucc_lt_last k).ne
    simp [Dn, versFin_eq, diagBordee, eqFin_symm_last, eqFin_symm_castSucc, scal]
  · by_cases h : k = l
    · subst h; simp [Dn, versFin_eq, diagBordee, eqFin_symm_castSucc]
    · have h' : (Fin.castSucc k) ≠ Fin.castSucc l :=
        fun e => h (Fin.castSucc_injective _ e)
      simp [Dn, versFin_eq, diagBordee, eqFin_symm_castSucc,
        Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h']

lemma hyp_of_prev (N : ℕ) (lam : ℕ → ℂ)
    (hlam : ∀ i j, i < N → j < N → i ≠ j → lam i ≠ lam j)
    (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) (n : ℕ) (hn : n + 2 ≤ N)
    (hP : IsUnit (Pseq lam u n).det)
    (hD : (Pseq lam u n)⁻¹ * Mseq lam u n * Pseq lam u n = Dn lam n) :
    HypProlong (Mseq lam u n) (Pseq lam u n) (fun i : Fin (n + 1) => lam i.val) (lam (n + 1)) where
  hP := hP
  hdiag := hD
  hlam := fun i => hlam i.val (n + 1) (by omega) (by omega) (by omega)


open SchurDiag in
lemma etapeA (N : ℕ) (lam : ℕ → ℂ)
    (hlam : ∀ i j, i < N → j < N → i ≠ j → lam i ≠ lam j)
    (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) :
    ∀ n, n + 1 ≤ N →
      IsUnit (Pseq lam u n).det ∧
      (Pseq lam u n)⁻¹ * Mseq lam u n * Pseq lam u n = Dn lam n := by
  intro n
  induction n with
  | zero =>
      intro _
      refine ⟨by simp [Pseq], ?_⟩
      simp [Pseq, Mseq_zero]
  | succ n ih =>
      intro hn
      obtain ⟨hP, hD⟩ := ih (by omega)
      have H := hyp_of_prev N lam hlam u n hn hP hD
      set b := bVec lam (Pseq lam u n) (u n) (lam (n + 1)) with hb
      have key := (prolongement_diag_iff (Mseq lam u n) (u n) (lam (n + 1))
        (Pseq lam u n) (fun i : Fin (n + 1) => lam i.val) H b 0 1).2 ⟨rfl, one_ne_zero, ?_⟩
      · obtain ⟨hdet, hconj⟩ := key
        refine ⟨?_, ?_⟩
        · rw [Pseq_succ, det_versFin]; exact hdet
        · rw [Pseq_succ, Mseq_succ, Dn_succ, versFin_inv, ← versFin_mul, ← versFin_mul]
          rw [hconj]
      · rw [one_smul, inv_smul_one_sub_diagonal _ _ H.hlam]
        rfl

lemma passage_inv_explicite {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (hP : IsUnit P.det)
    (b : Matrix (Fin p) (Fin 1) ℂ) :
    (passage P b 0 1) * Matrix.fromBlocks P⁻¹ (-(P⁻¹ * b)) 0 (scal 1) = 1 := by
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hP
  have hb1 : b * scal 1 = b := by
    ext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp [scal, Matrix.mul_apply]
  have h22 : scal 1 * scal 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi; subst hj
    simp [scal, Matrix.mul_apply]
  have h12 : P * (-(P⁻¹ * b)) + b * scal 1 = 0 := by
    rw [hb1, Matrix.mul_neg, ← Matrix.mul_assoc, hPP, Matrix.one_mul]
    exact neg_add_cancel b
  unfold passage
  rw [Matrix.fromBlocks_multiply]
  rw [Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_mul, Matrix.mul_zero, hPP, h12, h22]
  simp only [add_zero, zero_add]
  exact Matrix.fromBlocks_one

lemma etapeB (N : ℕ) (lam : ℕ → ℂ)
    (hlam : ∀ i j, i < N → j < N → i ≠ j → lam i ≠ lam j)
    (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) :
    ∀ n, n + 2 ≤ N →
      (Pseq lam u (n + 1))⁻¹ =
        versFin (Matrix.fromBlocks (Pseq lam u n)⁻¹
          (-(Matrix.diagonal (fun i : Fin (n + 1) => (lam (n + 1) - lam i.val)⁻¹)
              * (Pseq lam u n)⁻¹ * u n)) 0 (scal 1)) := by
  intro n hn
  obtain ⟨hP, _⟩ := etapeA N lam hlam u n (by omega)
  have hb : (Pseq lam u n)⁻¹ * bVec lam (Pseq lam u n) (u n) (lam (n + 1)) =
      Matrix.diagonal (fun i : Fin (n + 1) => (lam (n + 1) - lam i.val)⁻¹)
        * (Pseq lam u n)⁻¹ * u n := by
    have hPP' : (Pseq lam u n)⁻¹ * Pseq lam u n = 1 := Matrix.nonsing_inv_mul _ hP
    unfold bVec
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
  rw [Pseq_succ]
  apply Matrix.inv_eq_right_inv
  rw [← hb, ← versFin_mul]
  rw [passage_inv_explicite _ hP, versFin_one]

lemma etapeC (N : ℕ) (lam : ℕ → ℂ)
    (hlam : ∀ i j, i < N → j < N → i ≠ j → lam i ≠ lam j)
    (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) :
    ∀ n, n + 2 ≤ N →
        (∀ i : Fin (n + 1), ∀ k : Fin (n + 1),
          Pseq lam u (n + 1) (Fin.castSucc k) (Fin.castSucc i) = Pseq lam u n k i) ∧
        (∀ i : Fin (n + 1), Pseq lam u (n + 1) (Fin.last (n + 1)) (Fin.castSucc i) = 0) ∧
        (∀ k : Fin (n + 1),
          Pseq lam u (n + 1) (Fin.castSucc k) (Fin.last (n + 1)) =
            ∑ i : Fin (n + 1),
              (Matrix.diagonal (fun j : Fin (n + 1) => (lam (n + 1) - lam j.val)⁻¹)
                * (Pseq lam u n)⁻¹ * u n) i 0 * Pseq lam u n k i) ∧
        Pseq lam u (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1)) = 1 := by
  intro n hn
  obtain ⟨hP, _⟩ := etapeA N lam hlam u n (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i k
    rw [Pseq_succ, passage, versFin_fromBlocks_11]
  · intro i
    rw [Pseq_succ, passage, versFin_fromBlocks_21]
    simp
  · intro k
    rw [Pseq_succ, passage, versFin_fromBlocks_12]
    have hb : bVec lam (Pseq lam u n) (u n) (lam (n + 1)) =
        Pseq lam u n * (Matrix.diagonal (fun j : Fin (n + 1) => (lam (n + 1) - lam j.val)⁻¹)
          * (Pseq lam u n)⁻¹ * u n) := by
      unfold bVec
      simp only [Matrix.mul_assoc]
    rw [hb, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · rw [Pseq_succ, passage, versFin_fromBlocks_22]
    simp [scal]

lemma versFin_injective {n : ℕ} :
    Function.Injective (versFin : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ → _) := by
  intro A B h
  ext i j
  have := congrFun (congrFun h ((eqFin n) i)) ((eqFin n) j)
  simpa [versFin_eq] using this

open SchurDiag in
lemma etapeD (N : ℕ) (lam : ℕ → ℂ)
    (hlam : ∀ i j, i < N → j < N → i ≠ j → lam i ≠ lam j)
    (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ)
    (Q : (n : ℕ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (hQ0 : Q 0 = 1)
    (hQs : ∀ n, n + 2 ≤ N → ∃ (b' : Matrix (Fin (n + 1)) (Fin 1) ℂ)
            (c' : Matrix (Fin 1) (Fin (n + 1)) ℂ),
            Q (n + 1) = versFin (passage (Q n) b' c' 1))
    (hQd : ∀ n, n + 1 ≤ N → IsUnit (Q n).det ∧ (Q n)⁻¹ * Mseq lam u n * Q n = Dn lam n) :
    ∀ n, n + 1 ≤ N → Q n = Pseq lam u n := by
  intro n
  induction n with
  | zero => intro _; simp [hQ0, Pseq]
  | succ n ih =>
      intro hn
      have hQn : Q n = Pseq lam u n := ih (by omega)
      obtain ⟨b', c', hQ⟩ := hQs n hn
      obtain ⟨hP, hD⟩ := etapeA N lam hlam u n (by omega)
      have H := hyp_of_prev N lam hlam u n hn hP hD
      obtain ⟨hdet, hconj⟩ := hQd (n + 1) hn
      rw [hQ, hQn] at hdet hconj
      rw [det_versFin] at hdet
      rw [Mseq_succ, Dn_succ, versFin_inv, ← versFin_mul, ← versFin_mul] at hconj
      have hconj' := versFin_injective hconj
      obtain ⟨hc, _, hb⟩ := (prolongement_diag_iff (Mseq lam u n) (u n) (lam (n + 1))
        (Pseq lam u n) (fun i : Fin (n + 1) => lam i.val) H b' c' 1).1 ⟨hdet, hconj'⟩
      rw [hQ, hQn, Pseq_succ, hc, hb, one_smul, inv_smul_one_sub_diagonal _ _ H.hlam]
      rfl

theorem construction_recurrente_passage
    (N : ℕ) (_ : 2 ≤ N) (lam : ℕ → ℂ)
    (hlam : ∀ i j, i < N → j < N → i ≠ j → lam i ≠ lam j)
    (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) :
    (∀ n, n + 1 ≤ N →
        IsUnit (Pseq lam u n).det ∧
        (Pseq lam u n)⁻¹ * Mseq lam u n * Pseq lam u n = Dn lam n) ∧
    (∀ n, n + 2 ≤ N →
        (Pseq lam u (n + 1))⁻¹ =
          versFin (Matrix.fromBlocks (Pseq lam u n)⁻¹
            (-(Matrix.diagonal (fun i : Fin (n + 1) => (lam (n + 1) - lam i.val)⁻¹)
                * (Pseq lam u n)⁻¹ * u n)) 0 (scal 1))) ∧
    (∀ n, n + 2 ≤ N →
        (∀ i : Fin (n + 1), ∀ k : Fin (n + 1),
          Pseq lam u (n + 1) (Fin.castSucc k) (Fin.castSucc i) = Pseq lam u n k i) ∧
        (∀ i : Fin (n + 1), Pseq lam u (n + 1) (Fin.last (n + 1)) (Fin.castSucc i) = 0) ∧
        (∀ k : Fin (n + 1),
          Pseq lam u (n + 1) (Fin.castSucc k) (Fin.last (n + 1)) =
            ∑ i : Fin (n + 1),
              (Matrix.diagonal (fun j : Fin (n + 1) => (lam (n + 1) - lam j.val)⁻¹)
                * (Pseq lam u n)⁻¹ * u n) i 0 * Pseq lam u n k i) ∧
        Pseq lam u (n + 1) (Fin.last (n + 1)) (Fin.last (n + 1)) = 1) ∧
    (∀ Q : (n : ℕ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
        Q 0 = 1 →
        (∀ n, n + 2 ≤ N → ∃ (b' : Matrix (Fin (n + 1)) (Fin 1) ℂ)
            (c' : Matrix (Fin 1) (Fin (n + 1)) ℂ),
            Q (n + 1) = versFin (passage (Q n) b' c' 1)) →
        (∀ n, n + 1 ≤ N → IsUnit (Q n).det ∧ (Q n)⁻¹ *
          Mseq lam u n * Q n = Dn lam n) →
        ∀ n, n + 1 ≤ N → Q n = Pseq lam u n) :=
  ⟨etapeA N lam hlam u,
   etapeB N lam hlam u,
   etapeC N lam hlam u,
   fun Q hQ0 hQs hQd => etapeD N lam hlam u Q hQ0 hQs hQd⟩


----------------------------------------------------------------------

open VandermondeThEq

lemma det_hn1_valeur_signe (k : ℕ) (τ : Fin (k + 2) → ℝ) (hτ : Function.Injective τ)
    (τn σn : ℝ) (hσ : σn ≠ 0) :
    let γn : ℂ := (τn : ℂ) - (σn : ℂ) * Complex.I
    let Δ : ℝ := ∏ i : Fin (k + 2), ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2
    let Hn1 : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ :=
      Matrix.of fun i j =>
        ∑ l : Fin (k + 2), τ l ^ ((i : ℕ) + j) +
          ((γn ^ ((i : ℕ) + j) + (starRingEnd ℂ γn) ^ ((i : ℕ) + j) : ℂ)).re
    Hn1.det = -4 * σn ^ 2 * Δ * ∏ l : Fin (k + 2), ((τn - τ l) ^ 2 + σn ^ 2) ^ 2 ∧
      Hn1.det < 0 := by
  intro γn Δ Hn1
  have hval : Hn1.det = -4 * σn ^ 2 * Δ *
      ∏ l : Fin (k + 2), ((τn - τ l) ^ 2 + σn ^ 2) ^ 2 := by
    apply Complex.ofReal_injective
    rw [det_hn1_eq_vandermonde_carre k τ τn σn, vandermonde_conjugue_carre (k + 2) τ τn σn]
    have hΔc : (Matrix.vandermonde (fun k => (τ k : ℂ))).det ^ 2 = (Δ : ℂ) :=
      vandermonde_carre_eq_delta (k + 2) τ
    rw [hΔc]
    simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
      Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_add,
      Complex.ofReal_sub]
    ring
  refine ⟨hval, ?_⟩
  rw [hval]
  have hΔ : 0 < Δ := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hne : τ j - τ i ≠ 0 := sub_ne_zero.mpr (fun h => (ne_of_gt hij) (hτ h))
    positivity
  have hP : 0 < ∏ l : Fin (k + 2), ((τn - τ l) ^ 2 + σn ^ 2) ^ 2 := by
    apply Finset.prod_pos
    intro l _
    have : 0 < (τn - τ l) ^ 2 + σn ^ 2 := by positivity
    positivity
  have hσ2 : 0 < σn ^ 2 := by positivity
  nlinarith [mul_pos (mul_pos hσ2 hΔ) hP]

open MatTranslate in
theorem obstruction_schur_partie_reelle
    (k : ℕ) (τ : Fin (k + 2) → ℝ) (hτ : Function.Injective τ) (τn σn : ℝ) :
    let m : ℕ → ℂ := fun r => ∑ j : Fin (k + 2), (τ j : ℂ) ^ r
    let γn : ℂ := (τn : ℂ) - (σn : ℂ) * Complex.I
    let Hn : Matrix (Fin (k + 3)) (Fin (k + 3)) ℂ :=
      Matrix.of fun i j => m (i + j) + γn ^ ((i : ℕ) + j)
    (Hn.transpose = Hn ∧ (Hn.IsHermitian ↔ σn = 0)) ∧
    (∀ j : Fin (k + 2), (τn - τ j) ^ 2 + σn ^ 2 ≠ 0 →
      ((1 / (γn - (τ j : ℂ))).im = 0 ↔ σn = 0)) ∧
    (σn ≠ 0 →
      let Δ : ℝ := ∏ i : Fin (k + 2), ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2
      let Hn1 : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ :=
        Matrix.of fun i j =>
          ∑ l : Fin (k + 2), τ l ^ ((i : ℕ) + j) +
            ((γn ^ ((i : ℕ) + j) + (starRingEnd ℂ γn) ^ ((i : ℕ) + j) : ℂ)).re
      (Hn1.det = -4 * σn ^ 2 * Δ *
          ∏ l : Fin (k + 2), ((τn - τ l) ^ 2 + σn ^ 2) ^ 2 ∧
        Hn1.det < 0) ∧
      ¬ Hn1.PosDef) := by
  intro m γn Hn
  refine ⟨?_, ?_, ?_⟩
  · have hsym : Hn.transpose = Hn := by
      ext i j
      simp only [Matrix.transpose_apply, Hn, Matrix.of_apply]
      rw [add_comm (i : ℕ) (j : ℕ)]
    refine ⟨hsym, ?_⟩
    constructor
    · intro h
      have h01 : star (Hn (1 : Fin (k + 3)) 0) = Hn 0 1 := by
        have := congrFun (congrFun h.eq 0) 1
        simpa [Matrix.conjTranspose_apply] using this
      simp only [Hn, Matrix.of_apply, m] at h01
      have him := congrArg Complex.im h01
      simp [γn, Complex.sub_im, Complex.mul_im] at him
      linarith
    · intro hσ0
      refine Matrix.IsHermitian.ext (fun i j => ?_)
      simp only [Hn, Matrix.of_apply, m, γn, hσ0]
      simp only [Complex.ofReal_zero, zero_mul, sub_zero, star_add, star_sum,
        star_pow, RCLike.star_def, Complex.conj_ofReal]
      rw [add_comm (j : ℕ) (i : ℕ)]
  · intro j hj
    exact resolvante_reelle_iff (τ j) τn σn hj
  · intro hσ Δ Hn1
    have hdet : Hn1.det = -4 * σn ^ 2 * Δ *
        ∏ l : Fin (k + 2), ((τn - τ l) ^ 2 + σn ^ 2) ^ 2 ∧ Hn1.det < 0 :=
      det_hn1_valeur_signe k τ hτ τn σn hσ
    exact ⟨hdet, not_posDef_of_det_neg Hn1 hdet.2⟩

open Matrix in
theorem schur_det_bloc {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) [Invertible A]
    (b : Fin m → ℝ) (d : ℝ) :
    (Matrix.fromBlocks A (Matrix.replicateCol (Fin 1) b)
        (Matrix.replicateRow (Fin 1) b)
        (Matrix.of fun _ _ => d)).det =
      A.det * (d - b ⬝ᵥ (A⁻¹ *ᵥ b)) := by
  rw [Matrix.det_fromBlocks₁₁]
  simp only [invOf_eq_nonsing_inv, Matrix.det_unique, Fin.default_eq_zero, Fin.isValue,
    Matrix.sub_apply, Matrix.of_apply, mul_eq_mul_left_iff, sub_right_inj]
  left
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring



end SchurPassage
