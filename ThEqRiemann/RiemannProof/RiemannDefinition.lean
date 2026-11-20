import mathlib

/-! -/
namespace RiemannDef

open Set Complex



noncomputable def xi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s

noncomputable def xiEntiere (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2

lemma xi_eq_xiEntiere (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = xiEntiere s := by
  have h1' : (s - 1) ≠ 0 := sub_ne_zero.mpr h1
  have h1'' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold xi xiEntiere
  rw [completedRiemannZeta_eq]
  field_simp
  ring

lemma xi_eq_of_re_pos (s : ℂ) (hs : 0 < s.re) :
    xi s = (1 / 2 : ℂ) * s * (s - 1) * (Gammaℝ s * riemannZeta s) := by
  have h0 : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs
  have hz : riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero h0
  have hc : completedRiemannZeta s = Gammaℝ s * riemannZeta s := by
    rw [hz]; field_simp
  unfold xi
  rw [hc]

lemma xiEntiere_differentiable : Differentiable ℂ xiEntiere := by
  unfold xiEntiere
  have hΛ : Differentiable ℂ completedRiemannZeta₀ :=
    differentiable_completedZeta₀
  fun_prop

lemma xiEntiere_one_sub (s : ℂ) : xiEntiere (1 - s) = xiEntiere s := by
  unfold xiEntiere
  rw [completedRiemannZeta₀_one_sub]
  ring

lemma xi_eq_poly (s : ℂ) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    xi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta₀ s + 1 / 2 := by
  have h1' : (s - 1) ≠ 0 := sub_ne_zero.mpr h1
  have h1'' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold xi
  rw [completedRiemannZeta_eq]
  field_simp
  ring

lemma xi_eq_of_ne (s : ℂ) (_ : s ≠ 0) (h1 : s ≠ 1) :
    xi s = (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  have h1' : (s - 1) ≠ 0 := sub_ne_zero.mpr h1
  have h1'' : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold xi
  rw [completedRiemannZeta_eq]

lemma xi_one_sub (s : ℂ) : xi (1 - s) = xi s := by
  unfold xi
  rw [completedRiemannZeta_one_sub]
  ring

def RiemannHypothesisXi : Prop :=
  ∀ s : ℂ, xiEntiere s = 0 → s.re = 1 / 2

---------------------------------------------------------------------

noncomputable def xiDecale (z : ℂ) : ℂ := xiEntiere (1 / 2 + z)

noncomputable def integrandeMoment (k : ℕ) (z : ℂ) : ℂ :=
  (-Complex.I * z) ^ k * deriv xiDecale z / xiDecale z

noncomputable def nuMoment (γ : ℝ → ℂ) (k : ℕ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I)) *
    ∫ t in (0:ℝ)..1, deriv γ t * integrandeMoment k (γ t)

---------------------------------------------------------------------

def LambdaZeros : Set ℂ := {γ | xiEntiere (1 / 2 + Complex.I * γ) = 0}

noncomputable def momentTronque
  (E : Finset ℂ) (k : ℕ) : ℂ := ∑ γ ∈ E, γ ^ k

def RiemannHypothesisLambda : Prop := ∀ γ ∈ LambdaZeros, γ.im = 0

lemma riemannXi_iff_lambda : RiemannHypothesisXi ↔ RiemannHypothesisLambda := by
  constructor
  · intro h γ hγ
    have := h _ hγ
    simp [Complex.add_re, Complex.mul_re] at this
    linarith
  · intro h s hs
    have hγ : (-Complex.I * (s - 1 / 2)) ∈ LambdaZeros := by
      unfold LambdaZeros
      simp only [Set.mem_ofPred_eq]
      have : (1 / 2 : ℂ) + Complex.I * (-Complex.I * (s - 1 / 2)) = s := by
        ring_nf; simp [Complex.I_sq]
      rw [this]; exact hs
    have := h _ hγ
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im] at this
    linarith

noncomputable def GLambda (γ : ℂ) : ℂ :=
  xiEntiere (1 / 2 + Complex.I * γ)



-----------------------------------------------------------------------------------------------

open Finset Matrix Polynomial BigOperators ComplexConjugate

noncomputable def momentFusion (E : Finset ℂ) (m : ℂ → ℕ) (k : ℕ) : ℂ :=
  ∑ γ ∈ E, (m γ : ℂ) * γ ^ k

noncomputable def hankelFusion (E : Finset ℂ) (m : ℂ → ℕ) (D : ℕ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun i j => momentFusion E m (i + j)

noncomputable def hankelFusion' (E : Finset ℂ) (m : ℂ → ℕ) (D : ℕ) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.of fun i j => momentFusion E m ((i : ℕ) + (j : ℕ))

def MultSymm (m : ℂ → ℕ) : Prop := ∀ γ : ℂ, m (conj γ) = m γ

def ConjStable (E : Finset ℂ) : Prop := ∀ γ ∈ E, conj γ ∈ E

abbrev Idx (E : Finset ℂ) (m : ℂ → ℕ) := Σ γ : E, Fin (m γ)

noncomputable def Tdiag (E : Finset ℂ) (m : ℂ → ℕ) : Matrix (Idx E m) (Idx E m) ℂ :=
  Matrix.diagonal fun p => (p.1 : ℂ)

noncomputable def Tjordan (E : Finset ℂ) (m : ℂ → ℕ) : Matrix (Idx E m) (Idx E m) ℂ :=
  Matrix.of fun p q =>
    if p = q then (p.1 : ℂ)
    else if p.1 = q.1 ∧ (q.2 : ℕ) = (p.2 : ℕ) + 1 then 1 else 0

noncomputable def Nil (E : Finset ℂ) (m : ℂ → ℕ) : Matrix (Idx E m) (Idx E m) ℂ :=
  Tjordan E m - Tdiag E m

noncomputable def polyOf {D : ℕ} (c : Fin D → ℂ) : ℂ[X] :=
  ∑ j : Fin D, C (c j) * X ^ (j : ℕ)

noncomputable def polyTilde {D : ℕ} (c : Fin D → ℂ) : ℂ[X] :=
  ∑ k : Fin D, C (conj (c k)) * X ^ (k : ℕ)

def HankelFusionPosDef (E : Finset ℂ) (m : ℂ → ℕ) (D : ℕ) : Prop :=
  ∀ c : Fin D → ℂ, c ≠ 0 → 0 < (star c ⬝ᵥ
  (hankelFusion' E m D).mulVec c).re

def HankelFusionPosDefReal (E : Finset ℂ) (m : ℂ → ℕ) (D : ℕ) : Prop :=
  ∀ c : Fin D → ℝ, c ≠ 0 →
    0 < (star (fun i => (c i : ℂ)) ⬝ᵥ
    (hankelFusion' E m D).mulVec (fun i => (c i : ℂ))).re

-----------------------------------------------------------------------


structure Exhaustion where
  Λ : Set ℂ
  E : ℕ → Finset ℂ
  D : ℕ → ℕ
  m : ℂ → ℕ
  hD : ∀ N, (E N).card = D N
  hE : ∀ N, ConjStable (E N)
  hm : MultSymm m
  hm_pos : ∀ γ ∈ Λ, 0 < m γ
  hsub : ∀ N, (E N : Set ℂ) ⊆ Λ
  hcov : ∀ γ ∈ Λ, ∃ N, γ ∈ E N

----------------------------------------------------------------------

noncomputable abbrev blockMatrix {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks A B C D

noncomputable def schurComplementA {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin q) (Fin q) ℂ :=
  D - C * A⁻¹ * B

noncomputable def schurComplementD {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin p) (Fin p) ℂ :=
  A - B * D⁻¹ * C

noncomputable def schurL {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (C : Matrix (Fin q) (Fin p) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 1 0 (C * A⁻¹) 1

noncomputable def schurDelta {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ)
    (C : Matrix (Fin q) (Fin p) ℂ) (D : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks A 0 0 (schurComplementA A B C D)

noncomputable def schurU {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  Matrix.fromBlocks 1 (A⁻¹ * B) 0 1

---------------------------------------------------------------------

def scal (d : ℂ) : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => d

def bordee {p : ℕ} (M : Matrix (Fin p) (Fin p) ℂ) (u : Matrix (Fin p) (Fin 1) ℂ) (m : ℂ) :
    Matrix (Fin p ⊕ Fin 1) (Fin p ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks M u 0 (scal m)

def diagBordee {p : ℕ} (l : Fin p → ℂ) (lam : ℂ) :
    Matrix (Fin p ⊕ Fin 1) (Fin p ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks (Matrix.diagonal l) 0 0 (scal lam)

def passage {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin p) (Fin 1) ℂ)
    (c : Matrix (Fin 1) (Fin p) ℂ) (d : ℂ) :
    Matrix (Fin p ⊕ Fin 1) (Fin p ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks P b c (scal d)

noncomputable def schurScal {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (b : Matrix (Fin p) (Fin 1) ℂ)
    (c : Matrix (Fin 1) (Fin p) ℂ) (d : ℂ) : ℂ :=
  d - (c * P⁻¹ * b) 0 0

structure HypProlong {p : ℕ} (M : Matrix (Fin p) (Fin p) ℂ) (P : Matrix (Fin p) (Fin p) ℂ)
    (l : Fin p → ℂ) (lam : ℂ) : Prop where
  hP : IsUnit P.det
  hdiag : P⁻¹ * M * P = Matrix.diagonal l
  hlam : ∀ i, l i ≠ lam

---------------------------------------------------------------------

def eqFin (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n + 1) :=
  finSumFinEquiv


def versFin {n : ℕ} (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.reindex (eqFin n) (eqFin n) A

noncomputable def Dn (lam : ℕ → ℂ) (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Matrix.diagonal (fun i : Fin (n + 1) => lam i.val)

noncomputable def Mseq (lam : ℕ → ℂ) (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) :
    (n : ℕ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  | 0 => Matrix.of fun _ _ => lam 0
  | n + 1 => versFin (bordee (Mseq lam u n) (u n) (lam (n + 1)))

noncomputable def bVec (lam : ℕ → ℂ) {n : ℕ} (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (un : Matrix (Fin (n + 1)) (Fin 1) ℂ) (lamNew : ℂ) : Matrix (Fin (n + 1)) (Fin 1) ℂ :=
  P * Matrix.diagonal
    (fun i : Fin (n + 1) => (lamNew - lam i.val)⁻¹) * P⁻¹ * un

noncomputable def Pseq (lam : ℕ → ℂ) (u : (n : ℕ) → Matrix (Fin (n + 1)) (Fin 1) ℂ) :
    (n : ℕ) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  | 0 => 1
  | n + 1 =>
      versFin (passage (Pseq lam u n) (bVec lam (Pseq lam u n) (u n) (lam (n + 1))) 0 1)

---------------------------------------------------------------------

def EstUnitriSup {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ i j : Fin n, j < i → R i j = 0) ∧ (∀ i : Fin n, R i i = 1)

noncomputable def mom {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (n : ℕ) (hn : n ≤ D) (k : ℕ) : ℂ :=
  ∑ i : Fin n, (mult (Fin.castLE hn i) : ℂ) * γ (Fin.castLE hn i) ^ k

noncomputable def hankelN {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (n : ℕ) (hn : n ≤ D) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => mom γ mult n hn (i.val + j.val)

noncomputable def hVec {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) : Matrix (Fin p) (Fin 1) ℂ :=
  Matrix.of fun i _ => mom γ mult (p + 1) hp (p + i.val)

noncomputable def coinHankel {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) : Matrix (Fin p) (Fin p) ℂ :=
  Matrix.of fun i j => mom γ mult (p + 1) hp (i.val + j.val)

noncomputable def schurN {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) : ℂ :=
  mom γ mult (p + 1) hp (2 * p)
    - ((hVec γ mult p hp)ᵀ * (coinHankel γ mult p hp)⁻¹ *
      hVec γ mult p hp) 0 0

---------------------------------------------------------------------


noncomputable def diagZeros {D : ℕ} (γ : Fin D → ℂ) (n : ℕ) (hnD : n ≤ D) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i : Fin n => γ (Fin.castLE hnD i))

noncomputable abbrev bordure {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) : Matrix (Fin p) (Fin 1) ℂ :=
  hVec γ mult p hp

noncomputable abbrev blocHankel {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) : Matrix (Fin p) (Fin p) ℂ :=
  coinHankel γ mult p hp

noncomputable abbrev sN {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) : ℂ :=
  schurN γ mult p hp

noncomputable def blocPrincipal {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (n : ℕ) (hnD : n ≤ D) (k : ℕ) (_ : k ≤ n) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => mom γ mult n hnD (i.val + j.val)

noncomputable def pivotsN {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (n : ℕ) (hnD : n ≤ D) (k : Fin n) : ℂ :=
  (blocPrincipal γ mult n hnD (k.val + 1) (by omega)).det
    / (blocPrincipal γ mult n hnD k.val (by omega)).det

def blocPrinc {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) (hk : k ≤ n) :
    Matrix (Fin k) (Fin k) ℂ :=
  A.submatrix (Fin.castLE hk) (Fin.castLE hk)

------------------------------------------------------------------------

noncomputable def momentZ (γ : ℕ → ℂ) (n r : ℕ) : ℂ :=
  ∑ k : Fin n, (γ k) ^ r

noncomputable def hankelZ (γ : ℕ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => momentZ γ n ((i : ℕ) + j)

noncomputable def hankelR (τ : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∑ k : Fin n, (τ k) ^ ((i : ℕ) + j)

def HR (γ : ℕ → ℂ) (n : ℕ) : Prop :=
  ∃ τ : ℕ → ℝ, (∀ k < n, γ k = (τ k : ℂ)) ∧
    (∀ i < n, ∀ j < n, i ≠ j → τ i ≠ τ j)

lemma hankelZ_eq_map_hankelR (γ : ℕ → ℂ) (τ : ℕ → ℝ) (n : ℕ)
    (h : ∀ k < n, γ k = (τ k : ℂ)) :
    hankelZ γ n = (hankelR τ n).map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  simp only [hankelZ, hankelR, momentZ, Matrix.of_apply, Matrix.map_apply]
  push_cast
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [h (k : ℕ) k.isLt]

------------------------------------------------------------------------

def newton (γ : ℕ → ℂ) (m : ℕ → ℕ) (n k : ℕ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 n, (m j : ℂ) * γ j ^ k

def Hn (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun p q => newton γ m n (p + q)

def Hn_shift (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun p q => newton γ m n (p + q + 1)

def Delta (γ : ℕ → ℂ) (m : ℕ → ℕ) (n r : ℕ) : ℂ :=
  (Matrix.of fun (p q : Fin r) => newton γ m n (p + q)).det

def Vn (γ : ℕ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun (j : Fin n) (p : Fin n) => γ (j + 1) ^ (p : ℕ)

lemma Vn_eq_vandermonde (γ : ℕ → ℂ) (n : ℕ) :
    Vn γ n = Matrix.vandermonde (fun j : Fin n => γ ((j : ℕ) + 1)) := by
  ext j p
  simp [Vn, Matrix.vandermonde_apply]

def Mn (m : ℕ → ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j : Fin n => (m ((j : ℕ) + 1) : ℂ)

noncomputable def Cn (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  (Hn γ m n)⁻¹ * Hn_shift γ m n

noncomputable def Dn' (γ : ℕ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun j : Fin n => γ (j + 1)

def bn (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) : Fin (n - 1) → ℂ :=
  fun p => newton γ m n (n - 1 + p)

def Hsub (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℂ :=
  Matrix.of fun p q => newton γ m n (p + q)

noncomputable def Schur (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) : ℂ :=
  newton γ m n (2 * n - 2) - (bn γ m n) ⬝ᵥ
  ((Hsub γ m n)⁻¹ *ᵥ (bn γ m n))

noncomputable def PiPoly (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) : ℂ[X] :=
  C ((Delta γ m n n)⁻¹) *
    (Matrix.of fun (p : Fin (n + 1)) (q : Fin (n + 1)) =>
      if (p : ℕ) < n then C
      (newton γ m n (p + q)) else (X : ℂ[X]) ^ (q : ℕ)).det


variable (Xi : ℂ → ℂ)

structure ZeroEnumeration (Xi : ℂ → ℂ) (γ : ℕ → ℂ) (m : ℕ → ℕ) : Prop where
  zero_mem   : ∀ n, 1 ≤ n → Xi (γ n) = 0
  injective  : ∀ m n, 1 ≤ m → 1 ≤ n → γ m = γ n → m = n
  exhaustive : ∀ z, Xi z = 0 → ∃ n, 1 ≤ n ∧ γ n = z
  mono_norm  : ∀ m n, 1 ≤ m → m ≤ n → ‖γ m‖ ≤ ‖γ n‖
  palier_strict : ∀ n, 1 ≤ n → ‖γ (n+1)‖ = ‖γ n‖ →
      (γ (n+1) = starRingEnd ℂ (γ n)) ∧ ‖γ (n+2)‖ ≠ ‖γ n‖
  mult_pos   : ∀ n, 1 ≤ n → 1 ≤ m n
  real_one   : (γ 1).im = 0
  real_two   : (γ 2).im = 0
  conj_mult  : ∀ i j, 1 ≤ i → 1 ≤ j → γ j =
    starRingEnd ℂ (γ i) → m j = m i



def HankelPositive (γ : ℕ → ℂ) (m : ℕ → ℕ) : Prop :=
  ∀ n, 2 ≤ n →
    (∀ k, k ≤ 2 * n - 1 → (newton γ m n k).im = 0) ∧
    (∀ r, 1 ≤ r → r ≤ n → 0 <
    (Delta γ m n r).re ∧ (Delta γ m n r).im = 0)

def H2R (m₁ m₂ : ℕ) (g₁ g₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun p q => (m₁ : ℝ) *
  g₁ ^ ((p : ℕ) + q) + (m₂ : ℝ) * g₂ ^ ((p : ℕ) + q)


noncomputable def momentForm (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (P : ℂ[X]) : ℂ :=
  ∑ j ∈ Finset.Icc 1 n, (m j : ℂ) * P.eval (γ j)

noncomputable def nodalPoly (γ : ℕ → ℂ) (n : ℕ) : ℂ[X] :=
  ∏ j ∈ Finset.Icc 1 n, (X - C (γ j))

noncomputable def borderMat {R : Type*} [CommRing R] (f : ℂ →+* R)
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (r : Fin (n + 1) → R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
  Matrix.of fun p q => if (p : ℕ) < n then f
  (newton γ m n (p + q)) else r q

noncomputable def cofac (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) (j : Fin (n + 1)) : ℂ :=
  (-1) ^ ((Fin.last n : ℕ) + (j : ℕ)) *
    ((borderMat (RingHom.id ℂ) γ m n 0).submatrix
      (Fin.last n).succAbove j.succAbove).det

noncomputable def sZero (γ : ℕ → ℂ) (j : ℕ) : ℂ :=
(1 : ℂ) / 2 + Complex.I * γ j


-------------------------------------------------------------------

structure PalierCritique (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ) : Prop where
  n0_ge       : 3 ≤ n₀
  reels_avant : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0
  non_reel    : (γ n₀).im ≠ 0
  conj_zero   : γ (n₀ + 1) = conj (γ n₀)
  mult_pos    : ∀ j, 1 ≤ j → j ≤ n₀ + 1 → 1 ≤ m j
  mult_conj   : m (n₀ + 1) = m n₀
  injectif    : ∀ i j, 1 ≤ i → i ≤ n₀ + 1 → 1 ≤ j → j ≤ n₀ + 1 → γ i = γ j → i = j



--------------------------------------------------------------------

def zerosCritiques : Set ℂ :=
  {s : ℂ | riemannZeta s = 0 ∧ s.re = 1 / 2}

-- the proof of the Hardy-theorem is not in mathlib ---
-- so HardyTheorem is the placeholder
-- to the theorem here.
def HardyTheorem : Prop :=
  Set.Infinite zerosCritiques


--------------------------------------------------------------------

def zerosNonTriviaux : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ riemannZeta s = 0}

def Omega (γ : ℕ → ℂ) : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ (sZero γ n).re ≠ 1 / 2}

def zCritEnum (γ : ℕ → ℂ) : Set ℂ :=
  {s : ℂ | ∃ n, 1 ≤ n ∧ (γ n).im = 0 ∧ s = sZero γ n}

def ConjugueSuit (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ) : Prop :=
  γ (n₀ + 1) = conj (γ n₀) ∧ m (n₀ + 1) = m n₀

def PropagationDefaut (γ : ℕ → ℂ) (n₀ : ℕ) : Prop :=
  ∀ N, n₀ ≤ N → (γ N).im ≠ 0

noncomputable def XiRiemann (z : ℂ) : ℂ := xiDecale (Complex.I * z)

lemma XiRiemann_eq (z : ℂ) :
  XiRiemann z = xiEntiere (1 / 2 + Complex.I * z) := rfl

--------------------------------------------------------------------

def DeuxPremiersZerosReels : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ XiRiemann a = 0 ∧ XiRiemann b = 0 ∧
    a.im = 0 ∧ b.im = 0 ∧ ‖a‖ ≤ ‖b‖ ∧
    ∀ z : ℂ, XiRiemann z = 0 → z ≠ a → z ≠ b → ‖b‖ ≤ ‖z‖

lemma deux_premiers_zeros_reels (hDeux : DeuxPremiersZerosReels) :
    ∃ a b : ℂ, a ≠ b ∧ XiRiemann a = 0 ∧ XiRiemann b = 0 ∧
      a.im = 0 ∧ b.im = 0 ∧ ‖a‖ ≤ ‖b‖ ∧
      ∀ z : ℂ, XiRiemann z = 0 → z ≠ a → z ≠ b → ‖b‖ ≤ ‖z‖ :=
  hDeux

noncomputable def cle (z : ℂ) : ℝ ×ₗ (ℝ ×ₗ ℝ) :=
  toLex (‖z‖, toLex (z.re, z.im))

lemma predecesseurs_finis (S : Set ℂ)
    (hfin : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite) (z : ℂ) :
    {w | w ∈ S ∧ cle w < cle z}.Finite := by
  refine (hfin ‖z‖).subset ?_
  intro w ⟨hwS, hlt⟩
  refine ⟨hwS, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  unfold cle at hlt
  rcases Prod.Lex.lt_iff.mp hlt with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

noncomputable def rang (S : Set ℂ)
    (hfin : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite) (z : ℂ) : ℕ :=
  (predecesseurs_finis S hfin z).toFinset.card

def prepend2 (a b : ℂ) (g : ℕ → ℂ) : ℕ → ℂ
  | 0 => a
  | 1 => b
  | n + 2 => g n

@[simp] lemma prepend2_zero (a b : ℂ) (g : ℕ → ℂ) : prepend2 a b g 0 = a := by
  simp [prepend2]

@[simp] lemma prepend2_one (a b : ℂ) (g : ℕ → ℂ) : prepend2 a b g 1 = b := by
  simp [prepend2]

@[simp] lemma prepend2_add_two (a b : ℂ) (g : ℕ → ℂ) (k : ℕ) :
    prepend2 a b g (k + 2) = g k := by
  simp [prepend2]

def ConjAdjacent (γ : ℕ → ℂ) : Prop :=
  ∀ n, 3 ≤ n → 0 < (γ n).im → γ (n + 1) = (starRingEnd ℂ) (γ n)

def ConjStable' (γ : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ) : Prop :=
  ∃ σ : ℕ → ℕ,
    (∀ j ∈ Finset.Icc 1 N, σ j ∈ Finset.Icc 1 N) ∧
    Set.InjOn σ (Finset.Icc 1 N) ∧
    (∀ j ∈ Finset.Icc 1 N, γ (σ j) = (starRingEnd ℂ) (γ j)) ∧
    (∀ j ∈ Finset.Icc 1 N, m (σ j) = m j)

structure ConjCompatible (γ : ℕ → ℂ) (m : ℕ → ℕ) : Prop where
  conj_next : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 → γ (n₀ + 1) = starRingEnd ℂ (γ n₀)
  mult_next : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 → m (n₀ + 1) = m n₀

structure ConjCompatible' (γ : ℕ → ℂ) (m : ℕ → ℕ) : Prop where
  conj_next : ∀ n, 3 ≤ n → (γ n).im ≠ 0 → γ (n - 1) ≠ starRingEnd ℂ (γ n) →
    γ (n + 1) = starRingEnd ℂ (γ n) ∧ m (n + 1) = m n

lemma conjCompatible_imp_conjCompatible' (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (h : ConjCompatible γ m) : ConjCompatible' γ m := by
  refine ⟨?_⟩
  intro n hn him _hprev
  constructor
  · exact h.conj_next n hn him
  · exact h.mult_next n hn him




structure ConfigurationDegenereePaire (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) : Prop where
  n_ge_three   : 3 ≤ n
  im_ne_zero   : (γ n).im ≠ 0
  prev_eq_conj : γ (n - 1) = (starRingEnd ℂ) (γ n)
  mult_eq      : m (n - 1) = m n
  mult_pos_n   : 1 ≤ m n
  det_prev_pos : 0 < (Delta γ m (n - 2) (n - 2)).re
  prev_reels   : ∀ k, 1 ≤ k → k ≤ n - 2 → (γ k).im = 0


def HconjFirst (γ : ℕ → ℂ) (m : ℕ → ℕ) : Prop :=
  ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
    (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
    γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n

def vecteurMomentLocal (γ : ℕ → ℂ) (j : ℕ) (N : ℕ) : Fin N → ℂ :=
  fun p => (γ j) ^ (p : ℕ)

structure OrdreSpectralIntraPalier (γ : ℕ → ℂ) (m : ℕ → ℕ) : Prop where
  paire_ouverte :
    ∀ n₀ n, 3 ≤ n₀ → n₀ ≤ n → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) →
      Even (n - n₀) → (γ n).im ≠ 0 →
      γ (n + 1) = (starRingEnd ℂ) (γ n) ∧
      m (n + 1) = m n ∧
      γ (n - 1) ≠ (starRingEnd ℂ) (γ n)
  paire_fermee :
    ∀ n₀ n, 3 ≤ n₀ → n₀ ≤ n → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) →
      Odd (n - n₀) → (γ n).im ≠ 0 →
      γ (n - 1) = (starRingEnd ℂ) (γ n)
  pas_reel_apres_paire :
    ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = (starRingEnd ℂ) (γ n) →
      (γ (n + 1)).im ≠ 0

def seuilSpectral (n₁ : ℕ) : ℕ := max n₁ 3

noncomputable def poleBlocSup (γ : ℕ → ℂ) (n₁ k : ℕ) : ℂ :=
  let z := γ (seuilSpectral n₁ + 2 * k)
  ⟨(k : ℝ), |z.im| + 1⟩

@[simp]
lemma poleBlocSup_im (γ : ℕ → ℂ) (n₁ k : ℕ) :
    (poleBlocSup γ n₁ k).im = |(γ (seuilSpectral n₁ + 2 * k)).im| + 1 := rfl

lemma poleBlocSup_im_pos (γ : ℕ → ℂ) (n₁ k : ℕ) :
    0 < (poleBlocSup γ n₁ k).im := by
  rw [poleBlocSup_im]
  positivity

@[simp]
lemma poleBlocSup_re (γ : ℕ → ℂ) (n₁ k : ℕ) :
    (poleBlocSup γ n₁ k).re = (k : ℝ) := rfl

lemma poleBlocSup_injective (γ : ℕ → ℂ) (n₁ : ℕ) :
    ∀ k₁ k₂, poleBlocSup γ n₁ k₁ = poleBlocSup γ n₁ k₂ → k₁ = k₂ := by
  intro k₁ k₂ h
  have h_re := congrArg Complex.re h
  simp only [poleBlocSup_re, Nat.cast_inj] at h_re
  exact h_re

lemma poleBlocSup_im_ne_zero (γ : ℕ → ℂ) (n₁ k : ℕ) :
    (poleBlocSup γ n₁ k).im ≠ 0 :=
  ne_of_gt (poleBlocSup_im_pos γ n₁ k)

noncomputable def gammaAlign (γ : ℕ → ℂ) (n₁ : ℕ) (n : ℕ) : ℂ :=
  if n < seuilSpectral n₁ then
    ((γ n).re : ℂ)
  else
    let k := (n - seuilSpectral n₁) / 2
    if (n - seuilSpectral n₁) % 2 = 0 then
      poleBlocSup γ n₁ k
    else
      (starRingEnd ℂ) (poleBlocSup γ n₁ k)

def mAlign (m : ℕ → ℕ) (n₁ : ℕ) (n : ℕ) : ℕ :=
  if n < seuilSpectral n₁ then
    m n
  else
    let k := (n - seuilSpectral n₁) / 2
    m (seuilSpectral n₁ + 2 * k)

def CanonicalZeroEnumerationExists : Prop :=
  ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
    ZeroEnumeration XiRiemann γ m ∧
    (∀ n, 3 ≤ n → (γ n).im ≠ 0 →
      ((∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n) ∧
      (γ (n + 1)).im ≠ 0)


def PaliersStrictsXiRiemann : Prop :=
  ∀ z w : ℂ, XiRiemann z = 0 → XiRiemann w = 0 → z ≠ w → ‖z‖ = ‖w‖ →
    w = starRingEnd ℂ z

structure HypotheseGeometrieSpectraleXi : Prop where
  paliers_stricts : PaliersStrictsXiRiemann
  align_perm : ∀ (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ),
    ZeroEnumeration XiRiemann γ₀ m₀ →
    ∃ σ : Equiv.Perm ℕ,
      (∀ n < 3, σ n = n) ∧
      (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
      (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
        (γ₀ ∘ σ) = gammaAlign (γ₀ ∘ σ) n ∧
        (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n)




----------------------------------------------------------------------
-- Complement Riemann

noncomputable def Tspan : ℂ →L[ℝ] (ℂ →L[ℂ] ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun c => ContinuousLinearMap.toSpanSingleton ℂ c
      map_add' := fun c d => by ext; simp
      map_smul' := fun r c => by ext; simp }

noncomputable def hFacteur (z : ℂ) : ℂ :=
  (2 : ℂ) ^ ((1/2 : ℂ) - z) *
  Complex.log 2 / (1 - (2 : ℂ) ^ ((1/2 : ℂ) - z))

noncomputable def etaPartial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ((-1 : ℂ) ^ (n - 1)) / ((n : ℂ) ^ s)

def zerosXiDecale : Set ℂ := {z | xiDecale z = 0}

def ZeroNonTrivial (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

noncomputable def momentLocal (f : ℂ → ℂ) (zm : ℂ) : ℂ :=
  ((analyticOrderAt f zm).toNat : ℂ) * zm

noncomputable def deviation (z : ℂ) : ℝ := Real.arcsin (z.re / ‖z‖)

noncomputable def moment1 (m : ℕ) (z : ℂ) : ℂ :=
  (m : ℂ) * ((-Complex.I) * z)

structure BijHolPresOrient (c₁ c₂ : ℂ) (ε : ℝ) (φ : ℂ → ℂ) : Prop where
  holo : DifferentiableOn ℂ φ (Metric.closedBall c₁ ε)
  bij : Set.BijOn φ (Metric.sphere c₁ ε) (Metric.sphere c₂ ε)
  chgt : ∀ G : ℂ → ℂ,
    (∮ w in C(c₂, ε), G w) = ∮ z in C(c₁, ε), G (φ z) * deriv φ z

noncomputable def mobiusDisque (c₁ c₂ : ℂ) (R₁ R₂ : ℝ) (a : ℂ) (θ : ℝ) : ℂ → ℂ :=
  fun z => c₂ + (R₂ : ℂ) * Complex.exp (θ * Complex.I) *
    ((z - c₁ - a * R₁) / ((R₁ : ℂ) - (starRingEnd ℂ) a * (z - c₁)))

noncomputable def mobiusUnite (a : ℂ) : ℂ → ℂ :=
  fun w => (w - a) / (1 - (starRingEnd ℂ) a * w)

structure BijHolPresOrientContinuity (c₁ c₂ : ℂ) (ε : ℝ) (φ : ℂ → ℂ) : Prop where
  holo : DifferentiableOn ℂ φ (Metric.closedBall c₁ ε)
  bij : Set.BijOn φ (Metric.sphere c₁ ε) (Metric.sphere c₂ ε)
  chgt : ∀ G : ℂ → ℂ, ContinuousOn G (Metric.sphere c₂ ε) →
    (∮ w in C(c₂, ε), G w) = ∮ z in C(c₁, ε), G (φ z) * deriv φ z

noncomputable def mobiusPsiDeriv (a : ℂ) (u : ℝ) : ℝ :=
  (1 - ‖a‖^2) / ‖(1 : ℂ) -
  (starRingEnd ℂ) a * Complex.exp (u * Complex.I)‖^2

noncomputable def mobiusPsi (a : ℂ) (ψ₀ : ℝ) (t : ℝ) : ℝ :=
  ψ₀ + ∫ u in (0 : ℝ)..t, mobiusPsiDeriv a u



-- Fourrier_Riemann, not in mathlib ---
axiom exists_riemann_kernel :
    ∃ Phi : ℝ → ℝ, (∀ u ≥ 0, 0 < Phi u) ∧
      (∀ σ : ℝ, MeasureTheory.IntegrableOn
        (fun u : ℝ => Phi u * Real.cosh (σ * u)) (Set.Ioi (0 : ℝ))) ∧
      ∀ z : ℂ, xiDecale z = 2 * ∫ u in Set.Ioi (0 : ℝ),
      (Phi u : ℂ) * Complex.cosh (z * (u : ℂ))


------------------------------------------------------------------------
-- RiemannEndProof ---









end RiemannDef
