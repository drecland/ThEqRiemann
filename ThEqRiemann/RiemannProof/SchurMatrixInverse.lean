import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition


/-! -/
namespace SchurInverse

open Set Complex
open RiemannDef


lemma schurComplementA_eq_invOf {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    [Invertible A] :
    schurComplementA A B C D = D - C * ⅟A * B := by
  simp [schurComplementA, Matrix.invOf_eq_nonsing_inv]

lemma schurL_mul_schurDelta {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) :
    schurL A C * schurDelta A B C D =
      Matrix.fromBlocks A 0 C (schurComplementA A B C D) := by
  unfold schurL schurDelta
  rw [Matrix.fromBlocks_multiply]
  have h : C * A⁻¹ * A = C := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul A hA, Matrix.mul_one]
  simp [h]

lemma schurLDelta_mul_schurU {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) :
    Matrix.fromBlocks A 0 C (schurComplementA A B C D) * schurU A B =
      blockMatrix A B C D := by
  unfold schurU blockMatrix
  rw [Matrix.fromBlocks_multiply]
  have h1 : A * (A⁻¹ * B) = B := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A hA, Matrix.one_mul]
  have h2 : C * (A⁻¹ * B) + schurComplementA A B C D = D := by
    unfold schurComplementA
    rw [Matrix.mul_assoc]
    abel
  simp [h1, h2]

theorem schur_factorisation {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) :
    blockMatrix A B C D = schurL A C * schurDelta A B C D * schurU A B := by
  rw [schurL_mul_schurDelta A B C D hA, schurLDelta_mul_schurU A B C D hA]

lemma det_schurL {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    (schurL A C).det = 1 := by
  unfold schurL
  rw [Matrix.det_fromBlocks_zero₁₂]
  simp

lemma det_schurU {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ) :
    (schurU A B).det = 1 := by
  unfold schurU
  rw [Matrix.det_fromBlocks_zero₂₁]
  simp

lemma det_schurDelta {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    (schurDelta A B C D).det = A.det * (schurComplementA A B C D).det := by
  unfold schurDelta
  rw [Matrix.det_fromBlocks_zero₂₁]

theorem det_blockMatrix_eq {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) :
    (blockMatrix A B C D).det = A.det * (D - C * A⁻¹ * B).det := by
  rw [schur_factorisation A B C D hA, Matrix.det_mul, Matrix.det_mul,
    det_schurL, det_schurDelta, det_schurU]
  simp [schurComplementA]

theorem isUnit_blockMatrix_iff {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) :
    IsUnit (blockMatrix A B C D) ↔ IsUnit (schurComplementA A B C D) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det,
    det_blockMatrix_eq A B C D hA]
  unfold schurComplementA
  constructor
  · intro h
    exact (IsUnit.mul_iff.mp h).2
  · intro h
    exact hA.mul h

theorem schur_factorisation_complete {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) :
    blockMatrix A B C D = schurL A C * schurDelta A B C D * schurU A B ∧
    (IsUnit (blockMatrix A B C D) ↔ IsUnit (schurComplementA A B C D)) ∧
    (blockMatrix A B C D).det = A.det * (D - C * A⁻¹ * B).det :=
  ⟨schur_factorisation A B C D hA,
   isUnit_blockMatrix_iff A B C D hA,
   det_blockMatrix_eq A B C D hA⟩


--------------------------------------------------------------------

lemma schurL_mul_inv {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    schurL A C * Matrix.fromBlocks 1 0 (-(C * A⁻¹)) 1 = 1 := by
  unfold schurL
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

lemma schurU_mul_inv {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ) :
    schurU A B * Matrix.fromBlocks 1 (-(A⁻¹ * B)) 0 1 = 1 := by
  unfold schurU
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

lemma schurDelta_mul_inv {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) (hS : IsUnit (schurComplementA A B C D).det) :
    schurDelta A B C D *
      Matrix.fromBlocks A⁻¹ 0 0 (schurComplementA A B C D)⁻¹ = 1 := by
  unfold schurDelta
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hS,
    Matrix.fromBlocks_one]

lemma inv_blockMatrix_eq_prod {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) (hS : IsUnit (schurComplementA A B C D).det) :
    (blockMatrix A B C D)⁻¹ =
      Matrix.fromBlocks 1 (-(A⁻¹ * B)) 0 1 *
      Matrix.fromBlocks A⁻¹ 0 0 (schurComplementA A B C D)⁻¹ *
      Matrix.fromBlocks 1 0 (-(C * A⁻¹)) 1 := by
  apply Matrix.inv_eq_right_inv
  rw [schur_factorisation A B C D hA]
  calc schurL A C * schurDelta A B C D * schurU A B *
        (Matrix.fromBlocks 1 (-(A⁻¹ * B)) 0 1 *
          Matrix.fromBlocks A⁻¹ 0 0 (schurComplementA A B C D)⁻¹ *
          Matrix.fromBlocks 1 0 (-(C * A⁻¹)) 1)
      = schurL A C * (schurDelta A B C D *
          (schurU A B * Matrix.fromBlocks 1 (-(A⁻¹ * B)) 0 1) *
          Matrix.fromBlocks A⁻¹ 0 0 (schurComplementA A B C D)⁻¹) *
          Matrix.fromBlocks 1 0 (-(C * A⁻¹)) 1 := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [schurU_mul_inv, Matrix.mul_one, schurDelta_mul_inv A B C D hA hS,
          Matrix.mul_one, schurL_mul_inv]

lemma banachiewicz_prod {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (S : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromBlocks 1 (-(A⁻¹ * B)) 0 1 *
      Matrix.fromBlocks A⁻¹ 0 0 S⁻¹ *
      Matrix.fromBlocks 1 0 (-(C * A⁻¹)) 1 =
    Matrix.fromBlocks (A⁻¹ + A⁻¹ * B * S⁻¹ * C * A⁻¹) (-(A⁻¹ * B * S⁻¹))
      (-(S⁻¹ * C * A⁻¹)) S⁻¹ := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc]

theorem banachiewicz {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) (hS : IsUnit (schurComplementA A B C D).det) :
    IsUnit (blockMatrix A B C D).det ∧
    (blockMatrix A B C D)⁻¹ =
      Matrix.fromBlocks
        (A⁻¹ + A⁻¹ * B * (schurComplementA A B C D)⁻¹ * C * A⁻¹)
        (-(A⁻¹ * B * (schurComplementA A B C D)⁻¹))
        (-((schurComplementA A B C D)⁻¹ * C * A⁻¹))
        (schurComplementA A B C D)⁻¹ := by
  refine ⟨?_, ?_⟩
  · rw [det_blockMatrix_eq A B C D hA]
    exact hA.mul hS
  · rw [inv_blockMatrix_eq_prod A B C D hA hS, banachiewicz_prod]

theorem schur_factorisation_D {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hD : IsUnit D.det) :
    blockMatrix A B C D =
      Matrix.fromBlocks 1 (B * D⁻¹) 0 1 *
      Matrix.fromBlocks (schurComplementD A B C D) 0 0 D *
      Matrix.fromBlocks 1 0 (D⁻¹ * C) 1 := by
  unfold blockMatrix schurComplementD
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  have h1 : B * D⁻¹ * D = B := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul D hD, Matrix.mul_one]
  have h2 : D * (D⁻¹ * C) = C := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv D hD, Matrix.one_mul]
  simp [h1, h2, Matrix.mul_assoc]

lemma schurU'_mul_inv {p q : ℕ}
    (B : Matrix (Fin p) (Fin q) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) (B * D⁻¹) 0
        (1 : Matrix (Fin q) (Fin q) ℂ) *
      Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) (-(B * D⁻¹)) 0
        (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

lemma schurL'_mul_inv {p q : ℕ}
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 (D⁻¹ * C)
        (1 : Matrix (Fin q) (Fin q) ℂ) *
      Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 (-(D⁻¹ * C))
        (1 : Matrix (Fin q) (Fin q) ℂ) = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.fromBlocks_one]

lemma deltaD_mul_inv {p q : ℕ}
    (T : Matrix (Fin p) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hT : IsUnit T.det) (hD : IsUnit D.det) :
    Matrix.fromBlocks T 0 0 D * Matrix.fromBlocks T⁻¹ 0 0 D⁻¹ = 1 := by
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ hT, Matrix.mul_nonsing_inv _ hD,
    Matrix.fromBlocks_one]

lemma banachiewicz_D_prod {p q : ℕ}
    (B : Matrix (Fin p) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p) ℂ)
    (D : Matrix (Fin q) (Fin q) ℂ) (T : Matrix (Fin p) (Fin p) ℂ) :
    Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 (-(D⁻¹ * C))
        (1 : Matrix (Fin q) (Fin q) ℂ) *
      Matrix.fromBlocks T⁻¹ 0 0 D⁻¹ *
      Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) (-(B * D⁻¹)) 0
        (1 : Matrix (Fin q) (Fin q) ℂ) =
    Matrix.fromBlocks T⁻¹ (-(T⁻¹ * B * D⁻¹))
      (-(D⁻¹ * C * T⁻¹)) (D⁻¹ + D⁻¹ * C * T⁻¹ * B * D⁻¹) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_assoc, add_comm]

theorem banachiewicz_D {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hD : IsUnit D.det) (hT : IsUnit (schurComplementD A B C D).det) :
    (blockMatrix A B C D)⁻¹ =
      Matrix.fromBlocks
        (schurComplementD A B C D)⁻¹
        (-((schurComplementD A B C D)⁻¹ * B * D⁻¹))
        (-(D⁻¹ * C * (schurComplementD A B C D)⁻¹))
        (D⁻¹ + D⁻¹ * C * (schurComplementD A B C D)⁻¹ * B * D⁻¹) := by
  rw [← banachiewicz_D_prod B C D (schurComplementD A B C D)]
  apply Matrix.inv_eq_right_inv
  rw [schur_factorisation_D A B C D hD]
  generalize hU : Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) (B * D⁻¹) 0
      (1 : Matrix (Fin q) (Fin q) ℂ) = U'
  generalize hDl : Matrix.fromBlocks (schurComplementD A B C D) 0 0 D = Dl
  generalize hL : Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 (D⁻¹ * C)
      (1 : Matrix (Fin q) (Fin q) ℂ) = L'
  generalize hL1 : Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) 0 (-(D⁻¹ * C))
      (1 : Matrix (Fin q) (Fin q) ℂ) = L1
  generalize hD1 : Matrix.fromBlocks (schurComplementD A B C D)⁻¹ 0 0 D⁻¹ = D1
  generalize hU1 : Matrix.fromBlocks (1 : Matrix (Fin p) (Fin p) ℂ) (-(B * D⁻¹)) 0
      (1 : Matrix (Fin q) (Fin q) ℂ) = U1
  have h1 : L' * L1 = 1 := by rw [← hL, ← hL1]; exact schurL'_mul_inv C D
  have h2 : U' * U1 = 1 := by rw [← hU, ← hU1]; exact schurU'_mul_inv B D
  have h3 : Dl * D1 = 1 := by
    rw [← hDl, ← hD1]; exact deltaD_mul_inv _ D hT hD
  calc U' * Dl * L' * (L1 * D1 * U1)
      = U' * (Dl * ((L' * L1) * D1) * U1) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, Matrix.one_mul, h3, Matrix.one_mul, h2]

theorem blocs_inverse_egaux {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) (hD : IsUnit D.det)
    (hS : IsUnit (schurComplementA A B C D).det)
    (hT : IsUnit (schurComplementD A B C D).det) :
    (schurComplementD A B C D)⁻¹ =
      A⁻¹ + A⁻¹ * B * (schurComplementA A B C D)⁻¹ * C * A⁻¹ ∧
    -((schurComplementD A B C D)⁻¹ * B * D⁻¹) =
      -(A⁻¹ * B * (schurComplementA A B C D)⁻¹) ∧
    -(D⁻¹ * C * (schurComplementD A B C D)⁻¹) =
      -((schurComplementA A B C D)⁻¹ * C * A⁻¹) ∧
    D⁻¹ + D⁻¹ * C * (schurComplementD A B C D)⁻¹ * B * D⁻¹ =
      (schurComplementA A B C D)⁻¹ := by
  have h := (banachiewicz_D A B C D hD hT).symm.trans
    (banachiewicz A B C D hA hS).2
  exact Matrix.fromBlocks_inj.mp h

theorem woodbury {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) (hD : IsUnit D.det)
    (hS : IsUnit (schurComplementA A B C D).det)
    (hT : IsUnit (schurComplementD A B C D).det) :
    (A - B * D⁻¹ * C)⁻¹ =
      A⁻¹ + A⁻¹ * B * (D - C * A⁻¹ * B)⁻¹ * C * A⁻¹ :=
  (blocs_inverse_egaux A B C D hA hD hS hT).1

theorem inversion_blocs {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ)
    (hA : IsUnit A.det) (hS : IsUnit (schurComplementA A B C D).det) :
    IsUnit (blockMatrix A B C D).det ∧
    (blockMatrix A B C D)⁻¹ =
      Matrix.fromBlocks
        (A⁻¹ + A⁻¹ * B * (schurComplementA A B C D)⁻¹ * C * A⁻¹)
        (-(A⁻¹ * B * (schurComplementA A B C D)⁻¹))
        (-((schurComplementA A B C D)⁻¹ * C * A⁻¹))
        (schurComplementA A B C D)⁻¹ :=
  banachiewicz A B C D hA hS

------------------------------------------------------------------------
open Matrix in
lemma jacobi_schur {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ) (b : Fin k → ℂ) (d : ℂ)
    (hA : IsUnit A.det) :
    (Matrix.fromBlocks A (Matrix.replicateCol Unit b) (Matrix.replicateRow Unit b)
        (Matrix.of fun (_ _ : Unit) => d)).det
      = A.det * (d - b ⬝ᵥ (A⁻¹ *ᵥ b)) := by
  have _ : Invertible A.det := hA.nonempty_invertible.some
  have _ : Invertible A := Matrix.invertibleOfDetInvertible A
  rw [Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.replicateRow_apply,
    Matrix.replicateCol_apply, Matrix.sub_apply, Matrix.of_apply,
    Matrix.invOf_eq_nonsing_inv]
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
  congr 1
  rw [Finset.sum_comm]






end SchurInverse
