import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.SchurDiagonalisation

/-! -/
namespace SchurTrigo

open Set Complex
open RiemannDef

lemma inv_bord_inf {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℂ) (hQ : IsUnit Q.det)
    (c : Matrix (Fin 1) (Fin p) ℂ) :
    (Matrix.fromBlocks Q 0 c (scal 1))⁻¹ =
      Matrix.fromBlocks Q⁻¹ 0 (-(c * Q⁻¹)) (scal 1) := by
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
  have h22 : scal 1 * scal 1 = (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    have hi : i = 0 := Subsingleton.elim _ _
    have hj : j = 0 := Subsingleton.elim _ _
    subst hi; subst hj
    simp [scal, Matrix.mul_apply]
  apply Matrix.inv_eq_right_inv
  rw [Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, hQQ, h22]
  have h21 : c * Q⁻¹ + scal 1 * (-(c * Q⁻¹)) = 0 := by
    have : scal 1 * (-(c * Q⁻¹)) = -(c * Q⁻¹) := by
      ext i j
      have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp [scal, Matrix.mul_apply]
    rw [this]
    exact add_neg_cancel _
  rw [h21]
  exact Matrix.fromBlocks_one

lemma mul_scal_one {p : ℕ} (A : Matrix (Fin p) (Fin 1) ℂ) : A * scal 1 = A := by
  ext i j
  have hj : j = 0 := Fin.ext (by omega)
  subst hj
  simp [scal, Matrix.mul_apply]

lemma scal_one_mul {p : ℕ} (A : Matrix (Fin 1) (Fin p) ℂ) : scal 1 * A = A := by
  ext i j
  have hi : i = 0 := Fin.ext (by omega)
  subst hi
  simp [scal, Matrix.mul_apply]

lemma scal_mul_eq_smul {p : ℕ} (m : ℂ) (A : Matrix (Fin 1) (Fin p) ℂ) :
    scal m * A = m • A := by
  ext i j
  have hi : i = 0 := Fin.ext (by omega)
  subst hi
  simp [scal, Matrix.mul_apply]

lemma scal_mul_scal_one (m : ℂ) : scal m * scal 1 = scal m := by
  ext i j
  have hi : i = 0 := Fin.ext (by omega)
  have hj : j = 0 := Fin.ext (by omega)
  subst hi; subst hj
  simp [scal, Matrix.mul_apply]

lemma scal_one_mul_scal (m : ℂ) : scal 1 * scal m = scal m := by
  ext i j
  have hi : i = 0 := Fin.ext (by omega)
  have hj : j = 0 := Fin.ext (by omega)
  subst hi; subst hj
  simp [scal, Matrix.mul_apply]

lemma scal_eq_smul_one (m : ℂ) : scal m = m • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  have hi : i = 0 := Fin.ext (by omega)
  have hj : j = 0 := Fin.ext (by omega)
  subst hi; subst hj
  simp [scal]

lemma mat11_mul {p : ℕ} (S : Matrix (Fin 1) (Fin 1) ℂ) (c : Matrix (Fin 1) (Fin p) ℂ) :
    S * c = S 0 0 • c := by
  ext i j
  have hi : i = 0 := Fin.ext (by omega)
  subst hi
  simp [Matrix.mul_apply, Matrix.smul_apply]

lemma bloc22_iff (m lam : ℂ) (S : Matrix (Fin 1) (Fin 1) ℂ) :
    scal m - S = scal lam ↔ lam = m - S 0 0 := by
  constructor
  · intro h
    have h0 := congrFun (congrFun h 0) 0
    simp [scal] at h0
    linear_combination -h0
  · intro h
    ext i j
    have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 0 := Fin.ext (by omega)
    subst hi; subst hj
    simp [scal]
    linear_combination -h

lemma bloc21_iff {p : ℕ} (w c : Matrix (Fin 1) (Fin p) ℂ)
    (T : Matrix (Fin p) (Fin p) ℂ) (s m lam : ℂ) (hl : lam = m - s) :
    -(c * T) - s • c + w + m • c = 0 ↔ w = c * (T - lam • 1) := by
  have hc : c * (T - lam • 1) = c * T - lam • c := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  rw [hc, hl, sub_smul]
  constructor
  · intro h
    have : w = c * T + s • c - m • c := by
      rw [← sub_eq_zero]
      rw [← h]
      abel
    rw [this]
    abel
  · intro h
    rw [h]
    abel

lemma mul_col_scalaire {p : ℕ} (c : Matrix (Fin 1) (Fin p) ℂ)
    (w : Matrix (Fin p) (Fin 1) ℂ) :
    c * w * c = (c * w) 0 0 • c := mat11_mul (c * w) c

theorem trigon_bordure_iff {p : ℕ}
    (M : Matrix (Fin p) (Fin p) ℂ) (u : Matrix (Fin p) (Fin 1) ℂ)
    (v : Matrix (Fin 1) (Fin p) ℂ) (m : ℂ)
    (Q : Matrix (Fin p) (Fin p) ℂ) (hQ : IsUnit Q.det)
    (c : Matrix (Fin 1) (Fin p) ℂ) (lam : ℂ) :
    (Matrix.fromBlocks Q 0 c (scal 1))⁻¹ * Matrix.fromBlocks M u v (scal m)
        * Matrix.fromBlocks Q 0 c (scal 1)
      = Matrix.fromBlocks (Q⁻¹ * M * Q + Q⁻¹ * u * c) (Q⁻¹ * u) 0 (scal lam) ↔
    v * Q = c * (Q⁻¹ * M * Q - lam • 1) ∧ lam = m - (c * (Q⁻¹ * u)) 0 0 := by
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ hQ
  have hQQ' : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul _ hQ
  rw [inv_bord_inf Q hQ c]
  have hprod :
      Matrix.fromBlocks Q⁻¹ 0 (-(c * Q⁻¹)) (scal 1) * Matrix.fromBlocks M u v (scal m)
          * Matrix.fromBlocks Q 0 c (scal 1) =
        Matrix.fromBlocks (Q⁻¹ * M * Q + Q⁻¹ * u * c) (Q⁻¹ * u)
          (-(c * Q⁻¹ * M * Q) - c * Q⁻¹ * u * c + v * Q + m • c)
          (scal m - c * Q⁻¹ * u) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      mul_scal_one, scal_mul_eq_smul, Matrix.add_mul, Matrix.neg_mul,
      Matrix.mul_assoc]
    congr 1
    · simp only [one_smul, scal_mul_eq_smul]
      abel
    · simp only [one_smul]
      abel
  rw [hprod, Matrix.fromBlocks_inj]
  simp only [true_and]
  have hS : (c * Q⁻¹ * u) = c * (Q⁻¹ * u) := Matrix.mul_assoc _ _ _
  have h22 : scal m - c * Q⁻¹ * u = scal lam ↔ lam = m - (c * (Q⁻¹ * u)) 0 0 := by
    rw [hS]
    exact bloc22_iff m lam (c * (Q⁻¹ * u))
  have hs : c * Q⁻¹ * u * c = (c * (Q⁻¹ * u)) 0 0 • c := by
    rw [hS]
    exact mul_col_scalaire c (Q⁻¹ * u)
  have hT : c * (Q⁻¹ * M * Q - lam • 1) = c * (Q⁻¹ * M * Q) - lam • c := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one]
  have hcQ : c * Q⁻¹ * M * Q = c * (Q⁻¹ * M * Q) := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [h22, hs, hcQ]
  constructor
  · rintro ⟨h21, hl⟩
    refine ⟨?_, hl⟩
    exact (bloc21_iff (v * Q) c (Q⁻¹ * M * Q) _ m lam hl).mp h21
  · rintro ⟨h21, hl⟩
    refine ⟨?_, hl⟩
    exact (bloc21_iff (v * Q) c (Q⁻¹ * M * Q) _ m lam hl).mpr h21


open SchurDiag in
theorem trigon_bordure_diag_iff {p : ℕ}
    (M : Matrix (Fin p) (Fin p) ℂ) (u : Matrix (Fin p) (Fin 1) ℂ) (m : ℂ)
    (P : Matrix (Fin p) (Fin p) ℂ) (l : Fin p → ℂ)
    (H : HypProlong M P l m) (b : Matrix (Fin p) (Fin 1) ℂ)
    (c : Matrix (Fin 1) (Fin p) ℂ) :
    (IsUnit (passage P b c 1).det ∧
      (passage P b c 1)⁻¹ * bordee M u m * passage P b c 1 = diagBordee l m) ↔
    c = 0 ∧ b = P * (m • 1 - Matrix.diagonal l)⁻¹ * P⁻¹ * u := by
  have h := prolongement_diag_iff M u m P l H b c 1
  simpa [one_smul, one_ne_zero] using h






end SchurTrigo
