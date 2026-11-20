import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
/-! -/
namespace SchurDiag

open Set Complex
open RiemannDef

lemma scal_mul (a b : ℂ) : scal a * scal b = scal (a * b) := by
  ext i j
  simp [scal, Matrix.mul_apply]

lemma scal_one : (1 : Matrix (Fin 1) (Fin 1) ℂ) = scal 1 := by
  ext i j
  fin_cases i; fin_cases j
  simp [scal]

lemma scal_det (d : ℂ) : (scal d).det = d := by
  simp [scal, Matrix.det_unique]

lemma passage_det {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (hP : IsUnit P.det)
    (b : Matrix (Fin p) (Fin 1) ℂ) (c : Matrix (Fin 1) (Fin p) ℂ) (d : ℂ) :
    (passage P b c d).det = P.det * schurScal P b c d := by
  have _ : Invertible P := Matrix.invertibleOfIsUnitDet P hP
  unfold passage
  rw [Matrix.det_fromBlocks₁₁]
  congr 1
  have : scal d - c * ⅟P * b = scal (schurScal P b c d) := by
    ext i j
    fin_cases i; fin_cases j
    simp [scal, schurScal, Matrix.invOf_eq_nonsing_inv]
  rw [this, scal_det]

lemma bordee_mul_passage {p : ℕ} (M : Matrix (Fin p) (Fin p) ℂ)
    (u : Matrix (Fin p) (Fin 1) ℂ) (m : ℂ) (P : Matrix (Fin p) (Fin p) ℂ)
    (b : Matrix (Fin p) (Fin 1) ℂ) (c : Matrix (Fin 1) (Fin p) ℂ) (d : ℂ) :
    bordee M u m * passage P b c d =
      Matrix.fromBlocks (M * P + u * c) (M * b + u * scal d)
        (scal m * c) (scal m * scal d) := by
  unfold bordee passage
  rw [Matrix.fromBlocks_multiply]
  simp

lemma passage_mul_diag {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin p) (Fin 1) ℂ)
    (c : Matrix (Fin 1) (Fin p) ℂ) (d : ℂ) (l : Fin p → ℂ) (lam : ℂ) :
    passage P b c d * diagBordee l lam =
      Matrix.fromBlocks (P * Matrix.diagonal l) (b * scal lam)
        (c * Matrix.diagonal l) (scal d * scal lam) := by
  unfold passage diagBordee
  rw [Matrix.fromBlocks_multiply]
  simp

lemma lam_sub_diag_unit {p : ℕ} (l : Fin p → ℂ) (lam : ℂ) (h : ∀ i, l i ≠ lam) :
    IsUnit ((lam • (1 : Matrix (Fin p) (Fin p) ℂ) - Matrix.diagonal l).det) := by
  have : lam • (1 : Matrix (Fin p) (Fin p) ℂ) - Matrix.diagonal l
      = Matrix.diagonal (fun i => lam - l i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Matrix.one_apply_ne hij]
  rw [this, Matrix.det_diagonal]
  apply IsUnit.mk0
  rw [Finset.prod_ne_zero_iff]
  intro i _
  exact sub_ne_zero.mpr (h i).symm

lemma MP_eq_PD {p : ℕ} {M P : Matrix (Fin p) (Fin p) ℂ} {l : Fin p → ℂ} {m : ℂ}
    (H : HypProlong M P l m) : M * P = P * Matrix.diagonal l := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P H.hP
  calc M * P = (P * P⁻¹) * M * P := by rw [h1, Matrix.one_mul]
    _ = P * (P⁻¹ * M * P) := by simp only [Matrix.mul_assoc]
    _ = P * Matrix.diagonal l := by rw [H.hdiag]

lemma conj_iff_mul {n : Type*} [Fintype n] [DecidableEq n]
    {Pn Mn Dn : Matrix n n ℂ} (hPn : IsUnit Pn.det) :
    Pn⁻¹ * Mn * Pn = Dn ↔ Mn * Pn = Pn * Dn := by
  have h1 : Pn * Pn⁻¹ = 1 := Matrix.mul_nonsing_inv Pn hPn
  have h2 : Pn⁻¹ * Pn = 1 := Matrix.nonsing_inv_mul Pn hPn
  constructor
  · intro h
    calc Mn * Pn = (Pn * Pn⁻¹) * Mn * Pn := by rw [h1, Matrix.one_mul]
      _ = Pn * (Pn⁻¹ * Mn * Pn) := by simp only [Matrix.mul_assoc]
      _ = Pn * Dn := by rw [h]
  · intro h
    calc Pn⁻¹ * Mn * Pn = Pn⁻¹ * (Mn * Pn) := by rw [Matrix.mul_assoc]
      _ = Pn⁻¹ * (Pn * Dn) := by rw [h]
      _ = (Pn⁻¹ * Pn) * Dn := by rw [Matrix.mul_assoc]
      _ = Dn := by rw [h2, Matrix.one_mul]


lemma bloc_system {p : ℕ} {M P : Matrix (Fin p) (Fin p) ℂ} {l : Fin p → ℂ} {m : ℂ}
    (H : HypProlong M P l m) (u : Matrix (Fin p) (Fin 1) ℂ)
    (b : Matrix (Fin p) (Fin 1) ℂ) (c : Matrix (Fin 1) (Fin p) ℂ) (d : ℂ) :
    bordee M u m * passage P b c d = passage P b c d * diagBordee l m ↔
      (u * c = 0 ∧
       M * b + u * scal d = b * scal m ∧
       scal m * c = c * Matrix.diagonal l) := by
  have hMP := MP_eq_PD H
  rw [bordee_mul_passage, passage_mul_diag, Matrix.fromBlocks_inj]
  have hsc : scal m * scal d = scal d * scal m := by
    rw [scal_mul, scal_mul, mul_comm]
  constructor
  · rintro ⟨h11, h12, h21, -⟩
    refine ⟨?_, h12, h21⟩
    rw [hMP] at h11
    simpa using h11
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, h2, h3, hsc⟩
    rw [hMP, h1]
    simp

lemma c_eq_zero_iff {p : ℕ} {l : Fin p → ℂ} {m : ℂ} (hlam : ∀ i, l i ≠ m)
    (c : Matrix (Fin 1) (Fin p) ℂ) :
    scal m * c = c * Matrix.diagonal l ↔ c = 0 := by
  constructor
  · intro h
    ext i j
    fin_cases i
    have h' := congr_fun (congr_fun h 0) j
    rw [Matrix.mul_diagonal] at h'
    have hL : (scal m * c) 0 j = m * c 0 j := by
      simp [scal, Matrix.mul_apply]
    rw [hL] at h'
    have h2 : (m - l j) * c 0 j = 0 := by linear_combination h'
    rcases mul_eq_zero.mp h2 with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm (hlam j)
    · simpa using h0
  · rintro rfl
    simp

lemma b_formula_iff {p : ℕ} {M P : Matrix (Fin p) (Fin p) ℂ} {l : Fin p → ℂ} {m : ℂ}
    (H : HypProlong M P l m) (u b : Matrix (Fin p) (Fin 1) ℂ) (d : ℂ) :
    M * b + u * scal d = b * scal m ↔
      b = d • (P * (m • (1 : Matrix (Fin p) (Fin p) ℂ) - Matrix.diagonal l)⁻¹ * P⁻¹ * u) := by
  set E : Matrix (Fin p) (Fin p) ℂ := m • (1 : Matrix (Fin p) (Fin p) ℂ) - Matrix.diagonal l
    with hE
  have hEu : IsUnit E.det := lam_sub_diag_unit l m H.hlam
  have hEE : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hEu
  have hEE' : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hEu
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P H.hP
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P H.hP
  have hMP := MP_eq_PD H
  have hMdef : M = P * Matrix.diagonal l * P⁻¹ := by
    calc M = M * (P * P⁻¹) := by rw [hPP, Matrix.mul_one]
      _ = (M * P) * P⁻¹ := by rw [Matrix.mul_assoc]
      _ = P * Matrix.diagonal l * P⁻¹ := by rw [hMP]
  have hlhs : (m • (1 : Matrix (Fin p) (Fin p) ℂ) - M) = P * E * P⁻¹ := by
    rw [hMdef, hE]
    calc m • (1 : Matrix (Fin p) (Fin p) ℂ) - P * Matrix.diagonal l * P⁻¹
        = P * (m • (1 : Matrix (Fin p) (Fin p) ℂ)) * P⁻¹
            - P * Matrix.diagonal l * P⁻¹ := by
          congr 1
          rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
      _ = P * (m • (1 : Matrix (Fin p) (Fin p) ℂ) - Matrix.diagonal l) * P⁻¹ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
  have hE2 : M * b + u * scal d = b * scal m ↔
    (m • (1 : Matrix (Fin p) (Fin p) ℂ) - M) * b = d • u := by
    have e1 : b * scal m = m • b := by
      ext i j; fin_cases j; simp [scal, Matrix.mul_apply, mul_comm]
    have e2 : u * scal d = d • u := by
      ext i j; fin_cases j; simp [scal, Matrix.mul_apply, mul_comm]
    rw [e1, e2, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul]
    constructor
    · intro h
      rw [← h]; abel
    · intro h
      have := h
      rw [sub_eq_iff_eq_add] at this
      rw [this]; abel
  rw [hE2, hlhs]
  constructor
  · intro h
    have h1 : P⁻¹ * (P * E * P⁻¹ * b) = P⁻¹ * (d • u) := by rw [h]
    have h2 : E * (P⁻¹ * b) = d • (P⁻¹ * u) := by
      calc E * (P⁻¹ * b) = P⁻¹ * (P * E * P⁻¹ * b) := by
            simp only [← Matrix.mul_assoc, hPP', Matrix.one_mul]
        _ = P⁻¹ * (d • u) := h1
        _ = d • (P⁻¹ * u) := by rw [Matrix.mul_smul]
    have h3 : P⁻¹ * b = d • (E⁻¹ * (P⁻¹ * u)) := by
      calc P⁻¹ * b = (E⁻¹ * E) * (P⁻¹ * b) := by rw [hEE', Matrix.one_mul]
        _ = E⁻¹ * (E * (P⁻¹ * b)) := by rw [Matrix.mul_assoc]
        _ = E⁻¹ * (d • (P⁻¹ * u)) := by rw [h2]
        _ = d • (E⁻¹ * (P⁻¹ * u)) := by rw [Matrix.mul_smul]
    calc b = (P * P⁻¹) * b := by rw [hPP, Matrix.one_mul]
      _ = P * (P⁻¹ * b) := by rw [Matrix.mul_assoc]
      _ = P * (d • (E⁻¹ * (P⁻¹ * u))) := by rw [h3]
      _ = d • (P * E⁻¹ * P⁻¹ * u) := by
          rw [Matrix.mul_smul]; simp only [Matrix.mul_assoc]
  · intro h
    rw [h]
    calc P * E * P⁻¹ * (d • (P * E⁻¹ * P⁻¹ * u))
        = d • (P * E * P⁻¹ * (P * E⁻¹ * P⁻¹ * u)) := by rw [Matrix.mul_smul]
      _ = d • u := by
          congr 1
          calc P * E * P⁻¹ * (P * E⁻¹ * P⁻¹ * u)
              = P * E * (P⁻¹ * P) * E⁻¹ * P⁻¹ * u := by
                simp only [Matrix.mul_assoc]
            _ = P * (E * E⁻¹) * P⁻¹ * u := by
                rw [hPP']; simp only [Matrix.mul_one, Matrix.mul_assoc]
            _ = u := by
                rw [hEE, Matrix.mul_one, hPP, Matrix.one_mul]

lemma passage_unit_iff {p : ℕ} {P : Matrix (Fin p) (Fin p) ℂ} (hP : IsUnit P.det)
    (b : Matrix (Fin p) (Fin 1) ℂ) (d : ℂ) :
    IsUnit (passage P b 0 d).det ↔ d ≠ 0 := by
  rw [passage_det P hP b 0 d]
  have hs : schurScal P b 0 d = d := by simp [schurScal]
  rw [hs]
  constructor
  · intro h hd
    rw [hd, mul_zero] at h
    exact not_isUnit_zero h
  · intro hd
    exact hP.mul (IsUnit.mk0 d hd)

theorem prolongement_diag_iff {p : ℕ}
    (M : Matrix (Fin p) (Fin p) ℂ) (u : Matrix (Fin p) (Fin 1) ℂ) (m : ℂ)
    (P : Matrix (Fin p) (Fin p) ℂ) (l : Fin p → ℂ)
    (H : HypProlong M P l m)
    (b : Matrix (Fin p) (Fin 1) ℂ) (c : Matrix (Fin 1) (Fin p) ℂ) (d : ℂ) :
    (IsUnit (passage P b c d).det ∧
      (passage P b c d)⁻¹ * bordee M u m * passage P b c d = diagBordee l m) ↔
    (c = 0 ∧ d ≠ 0 ∧
      b = d • (P * (m • (1 : Matrix (Fin p) (Fin p) ℂ) - Matrix.diagonal l)⁻¹ * P⁻¹ * u)) := by
  constructor
  · rintro ⟨hPn, hconj⟩
    have hcomm := (conj_iff_mul hPn).mp hconj
    obtain ⟨-, h2, h3⟩ := (bloc_system H u b c d).mp hcomm
    have hc : c = 0 := (c_eq_zero_iff H.hlam c).mp h3
    subst hc
    have hd : d ≠ 0 := (passage_unit_iff H.hP b d).mp hPn
    exact ⟨rfl, hd, (b_formula_iff H u b d).mp h2⟩
  · rintro ⟨hc, hd, hb⟩
    subst hc
    have hPn : IsUnit (passage P b 0 d).det := (passage_unit_iff H.hP b d).mpr hd
    refine ⟨hPn, ?_⟩
    rw [conj_iff_mul hPn, bloc_system H u b 0 d]
    refine ⟨by simp, (b_formula_iff H u b d).mpr hb, by simp⟩


end SchurDiag
