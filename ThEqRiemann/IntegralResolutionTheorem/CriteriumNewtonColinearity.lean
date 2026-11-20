import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef

/-! -/
namespace CritColi

open Matrix Complex
open ResDef

lemma wNode_injective {d : ℕ} (z : Fin d → ℂ) (a : ℂ) (θ : ℝ)
    (hz : Function.Injective z) : Function.Injective (wNode z a θ) := by
  intro i j hij
  unfold wNode at hij
  have hne : Complex.exp (-(θ * Complex.I)) ≠ 0 := Complex.exp_ne_zero _
  have := mul_left_cancel₀ hne hij
  exact hz (sub_left_injective this)

lemma nuMoment_eq {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) (a : ℂ) (θ : ℝ) (k : ℕ) :
    nuMoment z m a θ k = ∑ j, (m j : ℂ) * (wNode z a θ j) ^ k := rfl

lemma quad_form_HankelR {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) (a : ℂ) (θ : ℝ)
    (r : ℕ) (c : Fin r → ℂ) :
    ∑ p, ∑ q, c p * c q * (HankelR z m a θ r) p q =
      ∑ j, (m j : ℂ) * (∑ p, c p * (wNode z a θ j) ^ (p : ℕ)) ^ 2 := by
  have h1 : ∀ p q : Fin r, c p * c q * (HankelR z m a θ r) p q =
      ∑ j, (m j : ℂ) * (c p * (wNode z a θ j) ^ (p : ℕ)) *
        (c q * (wNode z a θ j) ^ (q : ℕ)) := by
    intro p q
    simp only [HankelR, Matrix.of_apply, nuMoment_eq, pow_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [h1]
  have h2 : ∑ p : Fin r, ∑ q : Fin r, ∑ j : Fin d,
        (m j : ℂ) * (c p * (wNode z a θ j) ^ (p : ℕ)) * (c q * (wNode z a θ j) ^ (q : ℕ))
      = ∑ j : Fin d, ∑ p : Fin r, ∑ q : Fin r,
        (m j : ℂ) * (c p * (wNode z a θ j) ^ (p : ℕ)) * (c q * (wNode z a θ j) ^ (q : ℕ)) := by
    have hA : ∀ p : Fin r, ∑ q : Fin r, ∑ j : Fin d,
        (m j : ℂ) * (c p * (wNode z a θ j) ^ (p : ℕ)) * (c q * (wNode z a θ j) ^ (q : ℕ))
      = ∑ j : Fin d, ∑ q : Fin r,
        (m j : ℂ) * (c p * (wNode z a θ j) ^ (p : ℕ)) * (c q * (wNode z a θ j) ^ (q : ℕ)) :=
      fun p => Finset.sum_comm
    rw [Finset.sum_congr rfl (fun p _ => hA p)]
    exact Finset.sum_comm
  rw [h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

lemma wNode_real {d : ℕ} (z : Fin d → ℂ) (a : ℂ) (θ : ℝ) (j : Fin d) (x : ℝ)
    (h : z j = a + Complex.exp (θ * Complex.I) * x) :
    wNode z a θ j = (x : ℂ) := by
  unfold wNode
  rw [h]
  have : Complex.exp (-(θ * Complex.I)) * Complex.exp (θ * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  calc Complex.exp (-(θ * Complex.I)) * (a + Complex.exp (θ * Complex.I) * x - a)
      = (Complex.exp (-(θ * Complex.I)) * Complex.exp (θ * Complex.I)) * x := by ring
    _ = x := by rw [this, one_mul]

lemma quad_pos {d r : ℕ} (x : Fin d → ℝ) (m : Fin d → ℕ) (hm : ∀ j, 0 < m j)
    (hx : Function.Injective x) (hr : r ≤ d) (c : Fin r → ℝ) (hc : c ≠ 0) :
    0 < ∑ j, (m j : ℝ) * (∑ p, c p * (x j) ^ (p : ℕ)) ^ 2 := by
  classical
  set P : Polynomial ℝ :=
    ∑ p : Fin r, Polynomial.C (c p) * Polynomial.X ^ (p : ℕ) with hP
  have heval : ∀ t : ℝ, P.eval t = ∑ p : Fin r, c p * t ^ (p : ℕ) := by
    intro t
    simp [hP, Polynomial.eval_finsetSum]
  have hcoeff : ∀ p : Fin r, P.coeff (p : ℕ) = c p := by
    intro p
    simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hqp
      have : (p : ℕ) ≠ (q : ℕ) := fun h => hqp (Fin.ext h.symm)
      simp [this]
    · simp
  have hP0 : P ≠ 0 := by
    intro h
    apply hc
    funext p
    have := hcoeff p
    rw [h, Polynomial.coeff_zero] at this
    simpa using this.symm
  have hdeg : P.natDegree < r := by
    have hdeg' : P.degree < (r : WithBot ℕ) := by
      simpa [hP] using Polynomial.degree_sum_fin_lt c
    exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hdeg'
  have hex : ∃ j₀, P.eval (x j₀) ≠ 0 := by
    by_contra hall
    push Not at hall
    have hsub : Finset.univ.image x ⊆ P.roots.toFinset := by
      intro t ht
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
      simp [Polynomial.mem_roots hP0, hall j]
    have hcard : (Finset.univ.image x).card = d := by
      rw [Finset.card_image_of_injective _ hx]; simp
    have h1 : (Finset.univ.image x).card ≤ P.roots.toFinset.card :=
      Finset.card_le_card hsub
    have h2 : P.roots.toFinset.card ≤ P.natDegree :=
      (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
    omega
  obtain ⟨j₀, hj₀⟩ := hex
  apply Finset.sum_pos'
  · intro j _
    have : (0 : ℝ) ≤ (m j : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg this (sq_nonneg _)
  · refine ⟨j₀, Finset.mem_univ _, ?_⟩
    have hm' : (0 : ℝ) < (m j₀ : ℝ) := by exact_mod_cast hm j₀
    have hsq : 0 < (∑ p : Fin r, c p * (x j₀) ^ (p : ℕ)) ^ 2 := by
      rw [← heval]
      positivity
    exact mul_pos hm' hsq


lemma momentForm_eq_quad (ν : ℕ → ℝ) (r : ℕ) (P : Polynomial ℝ)
    (hP : P.natDegree < r) :
    momentForm ν P P =
      (fun p : Fin r => P.coeff p) ⬝ᵥ
        ((HankelSeq ν r) *ᵥ (fun p : Fin r => P.coeff p)) := by
  have hext : ∀ f : ℕ → ℝ,
      ∑ p ∈ Finset.range (P.natDegree + 1), P.coeff p * f p
        = ∑ p ∈ Finset.range r, P.coeff p * f p := by
    intro f
    apply Finset.sum_subset
    · intro p hp
      simp only [Finset.mem_range] at hp ⊢
      omega
    · intro p hp hpn
      simp only [Finset.mem_range, not_lt] at hp hpn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  unfold momentForm
  have h1 : ∀ p : ℕ,
      ∑ q ∈ Finset.range (P.natDegree + 1), P.coeff p * P.coeff q * ν (p + q)
        = P.coeff p * ∑ q ∈ Finset.range r, P.coeff q * ν (p + q) := by
    intro p
    rw [← hext (fun q => ν (p + q)), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [h1]
  rw [hext (fun p => ∑ q ∈ Finset.range r, P.coeff q * ν (p + q))]
  simp only [dotProduct, Matrix.mulVec, HankelSeq, Matrix.of_apply]
  rw [Finset.sum_range (fun p => P.coeff p * ∑ q ∈ Finset.range r, P.coeff q * ν (p + q))]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_range (fun q => P.coeff q * ν (↑p + q))]
  apply congrArg
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma HankelRR_posDef {d r : ℕ} (x : Fin d → ℝ) (m : Fin d → ℕ)
    (hm : ∀ j, 0 < m j) (hx : Function.Injective x) (hr : r ≤ d) :
    (HankelRR x m r).PosDef := by
  have hquad : ∀ c : Fin r → ℝ,
      c ⬝ᵥ ((HankelRR x m r) *ᵥ c)
        = ∑ j, (m j : ℝ) * (∑ p, c p * (x j) ^ (p : ℕ)) ^ 2 := by
    intro c
    have h : ∀ j : Fin d,
        (m j : ℝ) * (∑ p : Fin r, c p * (x j) ^ (p : ℕ)) ^ 2
          = ∑ p : Fin r, ∑ q : Fin r,
              c p * (↑(m j) * (x j ^ (p : ℕ) * x j ^ (q : ℕ))) * c q := by
      intro j
      rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      ring
    simp only [dotProduct, Matrix.mulVec, HankelRR, Matrix.of_apply, pow_add, h,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun y _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  refine ⟨?_, ?_⟩
  · refine Matrix.IsHermitian.ext fun p q => ?_
    simp only [star_trivial, HankelRR, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [add_comm (q : ℕ) (p : ℕ)]
  · intro c hc
    have hc' : (⇑c : Fin r → ℝ) ≠ 0 := by
      intro h
      apply hc
      exact DFunLike.coe_injective h
    have hsum : (c.sum fun i xi => c.sum fun j xj => xi * HankelRR x m r i j * xj)
        = (⇑c) ⬝ᵥ ((HankelRR x m r) *ᵥ (⇑c)) := by
      rw [Finsupp.sum_fintype _ _ (by intro i; simp [Finsupp.sum])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
      simp only [dotProduct, Matrix.mulVec]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp only [star_trivial]
    rw [hsum, hquad]
    exact quad_pos x m hm hx hr (⇑c) hc'

theorem posDef_of_forall_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (h : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (M *ᵥ x)) :
    M.PosDef := by
  refine ⟨?_, ?_⟩
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hM
  · intro x hx
    have hx' : (fun i => x i) ≠ 0 := by
      intro h0
      apply hx
      ext i
      simpa using congrFun h0 i
    have := h (fun i => x i) hx'
    simpa [Finsupp.sum_fintype, dotProduct, Matrix.mulVec, Finset.mul_sum,
      mul_assoc] using this

theorem schur_det_formula {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (α : ℝ)
    (hB : ∀ i j, B i j = A (Fin.castSucc i) (Fin.castSucc j))
    (hv : ∀ i, v i = A (Fin.castSucc i) (Fin.last n))
    (hα : α = A (Fin.last n) (Fin.last n)) (hsymm : A.IsSymm)
    (hdet : B.det ≠ 0) :
    A.det = B.det * (α - v ⬝ᵥ (B⁻¹ *ᵥ v)) := by
  have hBsymm : Bᵀ = B := by
    ext i j
    rw [Matrix.transpose_apply, hB, hB]
    exact congrFun (congrFun hsymm _) _
  have hBinvsymm : (B⁻¹)ᵀ = B⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, hBsymm]
  let _ : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hdet)
  have hdet' : A.det = (A.submatrix finSumFinEquiv finSumFinEquiv).det :=
    (Matrix.det_submatrix_equiv_self finSumFinEquiv A).symm
  have hblocks : A.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks B (Matrix.of fun i (_ : Fin 1) => v i)
        (Matrix.of fun (_ : Fin 1) j => v j) (Matrix.of fun _ _ => α) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁, hB]
      rfl
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂, Matrix.of_apply, hv]
      rfl
    · have hi : i = 0 := Subsingleton.elim _ _
      subst hi
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁, Matrix.of_apply, hv]
      exact congrFun (congrFun hsymm _) _
    · have hi : i = 0 := Subsingleton.elim _ _
      have hj : j = 0 := Subsingleton.elim _ _
      subst hi; subst hj
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, hα]
      rfl
  rw [hdet', hblocks, Matrix.det_fromBlocks₁₁]
  congr 1
  rw [Matrix.det_unique]
  simp only [Matrix.sub_apply, Matrix.of_apply, Matrix.mul_apply, invOf_eq_nonsing_inv]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
  ring


theorem posDef_of_schur_data {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) (α : ℝ)
    (hB : ∀ i j, B i j = A (Fin.castSucc i) (Fin.castSucc j))
    (hv : ∀ i, v i = A (Fin.castSucc i) (Fin.last n))
    (hα : α = A (Fin.last n) (Fin.last n))
    (hBpos : B.PosDef) (hschur : 0 < α - v ⬝ᵥ (B⁻¹ *ᵥ v))
    (hsymm : A.IsSymm) : A.PosDef := by
    have hBdet : IsUnit B.det := hBpos.det_pos.ne'.isUnit
    have hBinv : B *ᵥ (B⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hBdet, Matrix.one_mulVec]
    have hBpos' := (Matrix.posDef_iff_dotProduct_mulVec.mp hBpos).2
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hsymm, ?_⟩
    intro x hx
    set y : Fin n → ℝ := fun i => x (Fin.castSucc i) with hy
    set t : ℝ := x (Fin.last n) with ht
    set w : Fin n → ℝ := B⁻¹ *ᵥ v with hw
    have hdecomp : star x ⬝ᵥ (A *ᵥ x)
        = (y + t • w) ⬝ᵥ (B *ᵥ (y + t • w)) + t ^ 2 * (α - v ⬝ᵥ w) := by
      have hBsymm : Bᵀ = B := hBpos.isHermitian
      have h1 : w ⬝ᵥ (B *ᵥ y) = v ⬝ᵥ y := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hBsymm, hBinv]
      have hR : (y + t • w) ⬝ᵥ (B *ᵥ (y + t • w))
          = y ⬝ᵥ (B *ᵥ y) + 2 * t * (v ⬝ᵥ y) + t ^ 2 * (v ⬝ᵥ w) := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul, hBinv,
          add_dotProduct, dotProduct_add, dotProduct_add,
          smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct,
          smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
        have h2 : y ⬝ᵥ v = v ⬝ᵥ y := dotProduct_comm _ _
        have h3 : w ⬝ᵥ v = v ⬝ᵥ w := dotProduct_comm _ _
        rw [h1, h2, h3]
        ring
      have hL : star x ⬝ᵥ (A *ᵥ x)
          = y ⬝ᵥ (B *ᵥ y) + 2 * t * (v ⬝ᵥ y) + t ^ 2 * α := by
        have hsym : ∀ i : Fin n, A (Fin.last n) i.castSucc = v i := by
          intro i
          rw [hv i]
          exact Matrix.IsSymm.apply hsymm _ _
        have hBA : ∀ i j : Fin n, A i.castSucc j.castSucc = B i j := fun i j => (hB i j).symm
        have hvA : ∀ i : Fin n, A i.castSucc (Fin.last n) = v i := fun i => (hv i).symm
        simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc, star_trivial]
        simp only [hBA, hvA, hsym, ← hα]
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        have hcross : ∑ i, 2 * t * (v i * y i)
            = ∑ i, x i.castSucc * (v i * x (Fin.last n))
              + ∑ i, x (Fin.last n) * (v i * x i.castSucc) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hy, ht]
          ring
        rw [hcross]
        ring
      rw [hL, hR]
      ring
    by_cases ht0 : t = 0
    · have hy0 : y ≠ 0 := by
        intro h
        apply hx
        ext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa [ht] using ht0
        · simpa [hy] using congrFun h j
      have := hBpos' (show y + t • w ≠ 0 by simpa [ht0] using hy0)
      rw [hdecomp]
      simpa [ht0] using this
    · have h1 : 0 ≤ (y + t • w) ⬝ᵥ (B *ᵥ (y + t • w)) := by
        by_cases hz : y + t • w = 0
        · simp [hz]
        · exact (hBpos' hz).le
      have h2 : 0 < t ^ 2 * (α - v ⬝ᵥ w) := mul_pos (by positivity) hschur
      rw [hdecomp]
      linarith


theorem sylvester_posDef {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : A.IsSymm)
    (hminors : ∀ r (hr : r ≤ n), 0 < (A.submatrix (Fin.castLE hr) (Fin.castLE hr)).det) :
    A.PosDef := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · exact Matrix.IsHermitian.ext fun i => i.elim0
    · intro c hc
      exact absurd (Finsupp.ext fun i => i.elim0) hc
  | succ n ih =>
    set B : Matrix (Fin n) (Fin n) ℝ := A.submatrix Fin.castSucc Fin.castSucc with hB
    have hBsymm : B.IsSymm := by
      ext i j
      simpa [hB, Matrix.transpose_apply] using
        (congrFun (congrFun hsymm (Fin.castSucc j)) (Fin.castSucc i)).symm
    have hBminors : ∀ r (hr : r ≤ n),
        0 < (B.submatrix (Fin.castLE hr) (Fin.castLE hr)).det := by
      intro r hr
      have h := hminors r (hr.trans (Nat.le_succ n))
      convert h using 2
      ext i j
      simp [hB, Matrix.submatrix_apply]
    have hBpos : B.PosDef := ih B hBsymm hBminors
    set v : Fin n → ℝ := fun i => A (Fin.castSucc i) (Fin.last n) with hv
    set α : ℝ := A (Fin.last n) (Fin.last n) with hα
    have hBdet : B.det ≠ 0 := by
      have h := hBminors n le_rfl
      simpa using h.ne'
    have hdetA : A.det = B.det * (α - v ⬝ᵥ (B⁻¹ *ᵥ v)) := by
      apply schur_det_formula A B v α
      · intro i j; simp [hB, Matrix.submatrix_apply]
      · intro i; rfl
      · rfl
      · exact hsymm
      · exact hBdet
    have hschur : 0 < α - v ⬝ᵥ (B⁻¹ *ᵥ v) := by
      have hA : 0 < A.det := by simpa using hminors (n + 1) le_rfl
      have hBdet' : 0 < B.det := by simpa using hBminors n le_rfl
      rw [hdetA] at hA
      nlinarith
    exact posDef_of_schur_data A B v α (fun i j => rfl)
      (fun i => rfl) rfl hBpos hschur hsymm

lemma momentForm_eq_sum_range (ν : ℕ → ℝ) (P Q : Polynomial ℝ) (r s : ℕ)
    (hP : P.natDegree < r) (hQ : Q.natDegree < s) :
    momentForm ν P Q =
      ∑ p ∈ Finset.range r, ∑ q ∈ Finset.range s, P.coeff p * Q.coeff q * ν (p + q) := by
  have hinner : ∀ p : ℕ,
      ∑ q ∈ Finset.range (Q.natDegree + 1), P.coeff p * Q.coeff q * ν (p + q)
        = ∑ q ∈ Finset.range s, P.coeff p * Q.coeff q * ν (p + q) := by
    intro p
    apply Finset.sum_subset
    · intro q hq
      simp only [Finset.mem_range] at hq ⊢
      omega
    · intro q hq hqn
      simp only [Finset.mem_range, not_lt] at hq hqn
      have hq0 : Q.coeff q = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hq0]
      ring
  unfold momentForm
  simp_rw [hinner]
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_range] at hp ⊢
    omega
  · intro p hp hpn
    simp only [Finset.mem_range, not_lt] at hp hpn
    apply Finset.sum_eq_zero
    intro q _
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    ring

lemma momentForm_comm (ν : ℕ → ℝ) (P Q : Polynomial ℝ) :
    momentForm ν P Q = momentForm ν Q P := by
  set N : ℕ := max P.natDegree Q.natDegree + 1 with hN
  have hPN : P.natDegree < N := by
    rw [hN]; exact Nat.lt_succ_of_le (le_max_left _ _)
  have hQN : Q.natDegree < N := by
    rw [hN]; exact Nat.lt_succ_of_le (le_max_right _ _)
  rw [momentForm_eq_sum_range ν P Q N N hPN hQN,
      momentForm_eq_sum_range ν Q P N N hQN hPN]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [Nat.add_comm q p]
  ring

lemma momentForm_add_left (ν : ℕ → ℝ) (P P' Q : Polynomial ℝ) :
    momentForm ν (P + P') Q = momentForm ν P Q + momentForm ν P' Q := by
  have hPN : P.natDegree < max P.natDegree (max P'.natDegree Q.natDegree) + 1 := by
    omega
  have hP'N : P'.natDegree < max P.natDegree (max P'.natDegree Q.natDegree) + 1 := by
    omega
  have hQN : Q.natDegree < max P.natDegree (max P'.natDegree Q.natDegree) + 1 := by
    omega
  have hSN : (P + P').natDegree <
      max P.natDegree (max P'.natDegree Q.natDegree) + 1 := by
    have h := Polynomial.natDegree_add_le P P'
    omega
  rw [momentForm_eq_sum_range ν (P + P') Q _ _ hSN hQN,
      momentForm_eq_sum_range ν P Q _ _ hPN hQN,
      momentForm_eq_sum_range ν P' Q _ _ hP'N hQN]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [Polynomial.coeff_add]
  ring

lemma momentForm_smul_left (ν : ℕ → ℝ) (c : ℝ) (P Q : Polynomial ℝ) :
    momentForm ν (Polynomial.C c * P) Q = c * momentForm ν P Q := by
  have hPN : P.natDegree < max P.natDegree Q.natDegree + 1 := by
    omega
  have hQN : Q.natDegree < max P.natDegree Q.natDegree + 1 := by
    omega
  have hCN : (Polynomial.C c * P).natDegree < max P.natDegree Q.natDegree + 1 := by
    have h := Polynomial.natDegree_C_mul_le c P
    omega
  rw [momentForm_eq_sum_range ν (Polynomial.C c * P) Q _ _ hCN hQN,
      momentForm_eq_sum_range ν P Q _ _ hPN hQN]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [Polynomial.coeff_C_mul]
  ring

lemma momentForm_pos (ν : ℕ → ℝ) (r : ℕ) (hr : (HankelSeq ν r).PosDef)
    (P : Polynomial ℝ) (hP : P.natDegree < r) (hP0 : P ≠ 0) :
    0 < momentForm ν P P := by
  rw [momentForm_eq_quad ν r P hP]
  have hc : (fun p : Fin r => P.coeff p) ≠ 0 := by
    intro h
    apply hP0
    apply Polynomial.ext
    intro n
    rw [Polynomial.coeff_zero]
    by_cases hn : n < r
    · have := congrFun h ⟨n, hn⟩
      simpa using this
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have := (Matrix.posDef_iff_dotProduct_mulVec.mp hr).2 hc
  simpa using this

lemma momentForm_smul_right (ν : ℕ → ℝ) (c : ℝ) (P Q : Polynomial ℝ) :
    momentForm ν P (Polynomial.C c * Q) = c * momentForm ν P Q := by
  rw [momentForm_comm, momentForm_smul_left, momentForm_comm]

lemma momentForm_sum_left (ν : ℕ → ℝ) (s : Finset ℕ) (f : ℕ → ℝ)
    (g : ℕ → Polynomial ℝ) (Q : Polynomial ℝ) :
    momentForm ν (∑ j ∈ s, Polynomial.C (f j) * g j) Q
      = ∑ j ∈ s, f j * momentForm ν (g j) Q := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [momentForm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, momentForm_add_left,
      momentForm_smul_left, ih]

lemma momentForm_sub_left (ν : ℕ → ℝ) (P P' Q : Polynomial ℝ) :
    momentForm ν (P - P') Q = momentForm ν P Q - momentForm ν P' Q := by
  have h : P - P' = P + Polynomial.C (-1) * P' := by
    simp [sub_eq_add_neg]
  rw [h, momentForm_add_left, momentForm_smul_left]
  ring


lemma monic_natDegree_q (k : ℕ) (π : ℕ → Polynomial ℝ) (c : ℕ → ℝ)
    (q : Polynomial ℝ)
    (hmon : ∀ j ≤ k, (π j).Monic ∧ (π j).natDegree = j)
    (hq : q = Polynomial.X ^ (k + 1) -
      ∑ j ∈ Finset.range (k + 1), Polynomial.C (c j) * π j) :
    q.Monic ∧ q.natDegree = k + 1 := by
  have hsum : (∑ i ∈ Finset.range (k + 1), Polynomial.C (c i) * π i).natDegree ≤ k := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    calc (Polynomial.C (c i) * π i).natDegree ≤ (π i).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ = i := (hmon i hi').2
      _ ≤ k := hi'
  have hlt : (∑ i ∈ Finset.range (k + 1), Polynomial.C (c i) * π i).natDegree
      < (Polynomial.X ^ (k + 1) : Polynomial ℝ).natDegree := by
    rw [Polynomial.natDegree_X_pow]
    omega
  have hdeg : (∑ i ∈ Finset.range (k + 1), Polynomial.C (c i) * π i).degree
      < (Polynomial.X ^ (k + 1) : Polynomial ℝ).degree :=
    Polynomial.degree_lt_degree hlt
  have hqmon : q.Monic := by
    rw [hq]
    exact (Polynomial.monic_X_pow (k + 1)).sub_of_left hdeg
  refine ⟨hqmon, ?_⟩
  rw [hq, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt,
    Polynomial.natDegree_X_pow]

lemma momentForm_q_orth (ν : ℕ → ℝ) (d k : ℕ)
    (hpos : ∀ r, 1 ≤ r → r ≤ d → (HankelSeq ν r).PosDef)
    (hk : k + 1 ≤ d) (π : ℕ → Polynomial ℝ) (c : ℕ → ℝ) (q : Polynomial ℝ)
    (hmon : ∀ j ≤ k, (π j).Monic ∧ (π j).natDegree = j)
    (horth : ∀ j l, j ≤ k → l ≤ k → j ≠ l → momentForm ν (π j) (π l) = 0)
    (hc : c = fun j => momentForm ν (Polynomial.X ^ (k + 1)) (π j) /
      momentForm ν (π j) (π j))
    (hq : q = Polynomial.X ^ (k + 1) -
      ∑ j ∈ Finset.range (k + 1), Polynomial.C (c j) * π j) :
    ∀ l ≤ k, momentForm ν q (π l) = 0 := by
  intro l hl
  rw [hq, momentForm_sub_left, momentForm_sum_left]
  rw [Finset.sum_eq_single l]
  · have hne : momentForm ν (π l) (π l) ≠ 0 := by
      have hr : (HankelSeq ν (l + 1)).PosDef :=
        hpos (l + 1) (by omega) (by omega)
      have hpl : 0 < momentForm ν (π l) (π l) :=
        momentForm_pos ν (l + 1) hr (π l)
          (by rw [(hmon l hl).2]; omega) (hmon l hl).1.ne_zero
      exact hpl.ne'
    rw [hc]
    field_simp
    ring
  · intro j hj hjl
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [horth j l hj' hl hjl, mul_zero]
  · intro hl'
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hl)) hl'

lemma exists_orthogonal_monic_upto (ν : ℕ → ℝ) (d : ℕ)
    (hpos : ∀ r, 1 ≤ r → r ≤ d → (HankelSeq ν r).PosDef) :
    ∀ k, k ≤ d → ∃ π : ℕ → Polynomial ℝ,
      (∀ j ≤ k, (π j).Monic ∧ (π j).natDegree = j) ∧
      ∀ j l, j ≤ k → l ≤ k → j ≠ l → momentForm ν (π j) (π l) = 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨fun _ => 1, ?_, ?_⟩
    · intro j hj
      have : j = 0 := Nat.le_zero.mp hj
      subst this
      simp
    · intro j l hj hl hjl
      omega
  | succ k ih =>
    intro hk
    obtain ⟨π, hmon, horth⟩ := ih (Nat.le_of_succ_le hk)
    set c : ℕ → ℝ := fun j => momentForm ν
      (Polynomial.X ^ (k + 1)) (π j) / momentForm ν (π j) (π j) with hc
    set q : Polynomial ℝ := Polynomial.X ^ (k + 1) -
      ∑ j ∈ Finset.range (k + 1), Polynomial.C (c j) * π j with hq
    refine ⟨fun j => if j = k + 1 then q else π j, ?_, ?_⟩
    · intro j hj
      by_cases hjk : j = k + 1
      · subst hjk
        simp only [ite_true]
        exact monic_natDegree_q k π c q hmon hq
      · have hj' : j ≤ k := by omega
        simp only [hjk, ite_false]
        exact hmon j hj'
    · have hqorth := momentForm_q_orth ν d k hpos hk π c q hmon horth hc hq
      intro j l hj hl hjl
      by_cases hjk : j = k + 1
      · subst hjk
        have hl' : l ≤ k := by omega
        have hlk : l ≠ k + 1 := by omega
        simp only [ite_false, hlk, ite_false]
        exact hqorth l hl'
      · by_cases hlk : l = k + 1
        · subst hlk
          have hj' : j ≤ k := by omega
          simp only [hjk, ite_false, ite_true]
          rw [momentForm_comm]
          exact hqorth j hj'
        · have hj' : j ≤ k := by omega
          have hl' : l ≤ k := by omega
          simp only [hjk, hlk, ite_false]
          exact horth j l hj' hl' hjl

theorem exists_orthogonal_monic (ν : ℕ → ℝ) (d : ℕ)
    (hpos : ∀ r, 1 ≤ r → r ≤ d → (HankelSeq ν r).PosDef) :
    ∃ π : ℕ → Polynomial ℝ, (∀ k ≤ d, (π k).Monic ∧ (π k).natDegree = k) ∧
      ∀ j k, j ≤ d → k ≤ d → j ≠ k → momentForm ν (π j) (π k) = 0 :=
  exists_orthogonal_monic_upto ν d hpos d le_rfl

lemma momentForm_add_right (ν : ℕ → ℝ) (P Q Q' : Polynomial ℝ) :
    momentForm ν P (Q + Q') = momentForm ν P Q + momentForm ν P Q' := by
  rw [momentForm_comm, momentForm_add_left,
    momentForm_comm ν Q, momentForm_comm ν Q']

lemma momentForm_sub_right (ν : ℕ → ℝ) (P Q Q' : Polynomial ℝ) :
    momentForm ν P (Q - Q') = momentForm ν P Q - momentForm ν P Q' := by
  rw [momentForm_comm, momentForm_sub_left,
    momentForm_comm ν Q, momentForm_comm ν Q']

lemma momentForm_X_mul (ν : ℕ → ℝ) (P Q : Polynomial ℝ) :
    momentForm ν (Polynomial.X * P) Q = momentForm ν P (Polynomial.X * Q) := by
  set N : ℕ := max P.natDegree Q.natDegree + 1 with hN
  have hPN : P.natDegree < N := by omega
  have hQN : Q.natDegree < N := by omega
  have hXP : (Polynomial.X * P).natDegree < N + 1 := by
    have h1 := Polynomial.natDegree_mul_le (p := Polynomial.X) (q := P)
    have h2 := Polynomial.natDegree_X_le (R := ℝ)
    omega
  have hXQ : (Polynomial.X * Q).natDegree < N + 1 := by
    have h1 := Polynomial.natDegree_mul_le (p := Polynomial.X) (q := Q)
    have h2 := Polynomial.natDegree_X_le (R := ℝ)
    omega
  rw [momentForm_eq_sum_range ν (Polynomial.X * P) Q (N + 1) N hXP hQN,
      momentForm_eq_sum_range ν P (Polynomial.X * Q) N (N + 1) hPN hXQ]
  rw [Finset.sum_range_succ']
  simp only [Polynomial.coeff_X_mul_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  conv_rhs =>
    arg 2
    ext p
    rw [Finset.sum_range_succ']
  simp only [Polynomial.coeff_X_mul_zero, mul_zero, zero_mul, add_zero]
  simp only [Polynomial.coeff_X_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [show p + 1 + q = p + (q + 1) by ring]

lemma natDegree_sub_lead_le (p P : Polynomial ℝ) (m : ℕ)
    (hp : p.natDegree ≤ m + 1) (hP : P.Monic) (hPd : P.natDegree = m + 1) :
    (p - Polynomial.C (p.coeff (m + 1)) * P).natDegree ≤ m := by
  have hcoef : (p - Polynomial.C (p.coeff (m + 1)) * P).coeff (m + 1) = 0 := by
    have hlead : P.coeff (m + 1) = 1 := by
      have := hP.coeff_natDegree
      rwa [hPd] at this
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, hlead, mul_one, sub_self]
  have hle : (p - Polynomial.C (p.coeff (m + 1)) * P).natDegree ≤ m + 1 := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    refine max_le hp ?_
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    exact hPd.le
  by_contra hcon
  have heq : (p - Polynomial.C (p.coeff (m + 1)) * P).natDegree = m + 1 := by omega
  have hne : (p - Polynomial.C (p.coeff (m + 1)) * P) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at heq
    omega
  have := Polynomial.leadingCoeff_ne_zero.mpr hne
  rw [Polynomial.leadingCoeff, heq, hcoef] at this
  exact this rfl


lemma exists_comb_monic_basis (π : ℕ → Polynomial ℝ) (n : ℕ)
    (hmon : ∀ j ≤ n, (π j).Monic ∧ (π j).natDegree = j)
    (p : Polynomial ℝ) (hp : p.natDegree ≤ n) :
    ∃ c : ℕ → ℝ, p = ∑ j ∈ Finset.range (n + 1), Polynomial.C (c j) * π j := by
  induction n generalizing p with
  | zero =>
      have h0 := hmon 0 le_rfl
      have hπ0 : π 0 = 1 := Polynomial.eq_one_of_monic_natDegree_zero h0.1 h0.2
      refine ⟨fun _ => p.coeff 0, ?_⟩
      rw [Finset.sum_range_one, hπ0, mul_one]
      exact Polynomial.eq_C_of_natDegree_le_zero hp
  | succ m ih =>
      have hπ := hmon (m + 1) le_rfl
      have hdeg : (p - Polynomial.C (p.coeff (m + 1)) * π (m + 1)).natDegree ≤ m :=
        natDegree_sub_lead_le p (π (m + 1)) m hp hπ.1 hπ.2
      obtain ⟨c, hc⟩ := ih (fun j hj => hmon j (by omega))
        (p - Polynomial.C (p.coeff (m + 1)) * π (m + 1)) hdeg
      refine ⟨fun j => if j = m + 1 then p.coeff (m + 1) else c j, ?_⟩
      rw [Finset.sum_range_succ]
      have hsum : ∑ j ∈ Finset.range (m + 1),
          Polynomial.C (if j = m + 1 then p.coeff (m + 1) else c j) * π j
          = ∑ j ∈ Finset.range (m + 1), Polynomial.C (c j) * π j := by
        apply Finset.sum_congr rfl
        intro j hj
        have : j ≠ m + 1 := by
          have := Finset.mem_range.mp hj
          omega
        simp [this]
      rw [hsum, ← hc]
      simp

lemma momentForm_C_mul_left (ν : ℕ → ℝ) (a : ℝ) (P Q : Polynomial ℝ) :
    momentForm ν (Polynomial.C a * P) Q = a * momentForm ν P Q := by
  exact momentForm_smul_left ν a P Q

lemma orth_of_natDegree_lt (ν : ℕ → ℝ) (d : ℕ) (π : ℕ → Polynomial ℝ)
    (hmon : ∀ k ≤ d, (π k).Monic ∧ (π k).natDegree = k)
    (horth : ∀ j k, j ≤ d → k ≤ d → j ≠ k → momentForm ν (π j) (π k) = 0)
    (_ : ∀ r, 1 ≤ r → r ≤ d → (HankelSeq ν r).PosDef)
    (k : ℕ) (hk : k ≤ d) (q : Polynomial ℝ) (hq : q.natDegree < k) :
    momentForm ν (π k) q = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  obtain ⟨c, hc⟩ := exists_comb_monic_basis π m
    (fun j hj => hmon j (by omega)) q (by omega)
  rw [momentForm_comm, hc, momentForm_sum_left]
  apply Finset.sum_eq_zero
  intro j hj
  have hjm : j < m + 1 := Finset.mem_range.mp hj
  rw [horth j (m + 1) (by omega) hk (by omega), mul_zero]

lemma momentForm_self_ne_zero (ν : ℕ → ℝ) (d : ℕ) (π : ℕ → Polynomial ℝ)
    (hmon : ∀ k ≤ d, (π k).Monic ∧ (π k).natDegree = k)
    (hpos : ∀ r, 1 ≤ r → r ≤ d → (HankelSeq ν r).PosDef)
    (k : ℕ) (hk : k < d) :
    momentForm ν (π k) (π k) ≠ 0 := by
  have hr : (HankelSeq ν (k + 1)).PosDef := hpos (k + 1) (by omega) (by omega)
  have hπ := hmon k (by omega)
  have hlt : (π k).natDegree < k + 1 := by rw [hπ.2]; omega
  exact ne_of_gt (momentForm_pos ν (k + 1) hr (π k) hlt hπ.1.ne_zero)

lemma decomp_orthogonal (ν : ℕ → ℝ) (d : ℕ) (π : ℕ → Polynomial ℝ)
    (hmon : ∀ k ≤ d, (π k).Monic ∧ (π k).natDegree = k)
    (horth : ∀ j k, j ≤ d → k ≤ d → j ≠ k → momentForm ν (π j) (π k) = 0)
    (hpos : ∀ r, 1 ≤ r → r ≤ d → (HankelSeq ν r).PosDef)
    (k : ℕ) (hk : k < d) (p : Polynomial ℝ) (hp : p.natDegree ≤ k) :
    p = ∑ j ∈ Finset.range (k + 1),
      Polynomial.C (momentForm ν p (π j) / momentForm ν (π j) (π j)) * π j := by
  induction k generalizing p with
  | zero =>
      have h0 := hmon 0 (by omega)
      have hπ0 : π 0 = 1 := Polynomial.eq_one_of_monic_natDegree_zero h0.1 h0.2
      have hne : momentForm ν (π 0) (π 0) ≠ 0 :=
        momentForm_self_ne_zero ν d π hmon hpos 0 hk
      have hpC : p = Polynomial.C (p.coeff 0) :=
        Polynomial.eq_C_of_natDegree_le_zero hp
      rw [Finset.sum_range_one]
      rw [hπ0] at hne ⊢
      have h11 : momentForm ν 1 1 = ν 0 := by simp [momentForm]
      have hp1 : momentForm ν p 1 = p.coeff 0 * ν 0 := by
        conv_lhs => rw [hpC]
        simp [momentForm]
      rw [h11] at hne
      rw [h11, hp1, mul_one, mul_div_assoc, div_self hne, mul_one]
      exact hpC
  | succ n ih =>
      have hπ := hmon (n + 1) (by omega)
      have hdeg : (p - Polynomial.C (p.coeff (n + 1)) * π (n + 1)).natDegree ≤ n :=
        natDegree_sub_lead_le p (π (n + 1)) n hp hπ.1 hπ.2
      set a : ℝ := p.coeff (n + 1) with ha
      set p' : Polynomial ℝ := p - Polynomial.C a * π (n + 1) with hp'
      have hrec := ih (by omega) p' hdeg
      have hcoef : ∀ j ∈ Finset.range (n + 1),
          momentForm ν p' (π j) = momentForm ν p (π j) := by
        intro j hj
        have hjn : j ≤ n := by simpa [Finset.mem_range, Nat.lt_succ_iff] using hj
        rw [hp', momentForm_sub_left, momentForm_C_mul_left,
            horth (n + 1) j (by omega) (by omega) (by omega), mul_zero, sub_zero]
      have hne : momentForm ν (π (n + 1)) (π (n + 1)) ≠ 0 :=
        momentForm_self_ne_zero ν d π hmon hpos (n + 1) hk
      have ha_eq : a = momentForm ν p (π (n + 1)) / momentForm ν (π (n + 1)) (π (n + 1)) := by
        have hortho : momentForm ν p' (π (n + 1)) = 0 := by
          rw [momentForm_comm]
          exact orth_of_natDegree_lt ν d π hmon horth hpos (n + 1) (by omega) p' (by omega)
        rw [hp', momentForm_sub_left, momentForm_C_mul_left] at hortho
        field_simp
        linarith
      rw [Finset.sum_range_succ, ← ha_eq]
      have hsum : ∑ j ∈ Finset.range (n + 1),
            Polynomial.C (momentForm ν p (π j) / momentForm ν (π j) (π j)) * π j = p' := by
        rw [hrec]
        apply Finset.sum_congr rfl
        intro j hj
        rw [hcoef j hj]
      rw [hsum, hp']
      ring

theorem three_term_recurrence (ν : ℕ → ℝ) (d : ℕ) (π : ℕ → Polynomial ℝ)
    (hmon : ∀ k ≤ d, (π k).Monic ∧ (π k).natDegree = k)
    (horth : ∀ j k, j ≤ d → k ≤ d → j ≠ k → momentForm ν (π j) (π k) = 0)
    (hpos : ∀ r, 1 ≤ r → r ≤ d → (HankelSeq ν r).PosDef) :
    ∀ k, 1 ≤ k → k < d → ∃ α β : ℝ, 0 < β ∧
      π (k + 1) = (Polynomial.X - Polynomial.C α) * π k
        - Polynomial.C β * π (k - 1) := by
  intro k hk1 hkd
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : m + 1 - 1 = m := by omega
  rw [hm]
  set r : Polynomial ℝ := Polynomial.X * π (m + 1) - π (m + 2) with hr
  have hdeg_r : r.natDegree ≤ m + 1 := by
    have h1 : (π (m + 1)).Monic ∧ (π (m + 1)).natDegree = m + 1 := hmon (m + 1) (by omega)
    have h2 : (π (m + 2)).Monic ∧ (π (m + 2)).natDegree = m + 2 := hmon (m + 2) (by omega)
    have hA : (Polynomial.X * π (m + 1)).Monic := Polynomial.monic_X.mul h1.1
    have hAdeg : (Polynomial.X * π (m + 1)).natDegree = m + 2 := by
      rw [Polynomial.natDegree_X_mul h1.1.ne_zero, h1.2]
    have hlt : (Polynomial.X * π (m + 1) - π (m + 2)).degree
        < (Polynomial.X * π (m + 1)).degree := by
      apply Polynomial.degree_sub_lt_left
      · rw [Polynomial.degree_eq_natDegree hA.ne_zero,
          Polynomial.degree_eq_natDegree h2.1.ne_zero, hAdeg, h2.2]
      · exact hA.ne_zero
      · rw [hA.leadingCoeff, h2.1.leadingCoeff]
    rw [hr]
    by_cases h0 : Polynomial.X * π (m + 1) - π (m + 2) = 0
    · rw [h0]; simp
    · have := Polynomial.natDegree_lt_natDegree h0 hlt
      omega
  have hdec := decomp_orthogonal ν d π hmon horth hpos (m + 1) (by omega) r hdeg_r
  have hzero : ∀ j ∈ Finset.range (m + 2), j ≠ m → j ≠ m + 1 →
      momentForm ν r (π j) = 0 := by
    intro j hj hjm hjm1
    have hjlt : j < m := by
      have := Finset.mem_range.mp hj
      omega
    rw [hr, momentForm_sub_left]
    have h2 : momentForm ν (π (m + 2)) (π j) = 0 :=
      horth (m + 2) j (by omega) (by omega) (by omega)
    have h1 : momentForm ν (Polynomial.X * π (m + 1)) (π j) = 0 := by
      rw [momentForm_X_mul]
      apply orth_of_natDegree_lt ν d π hmon horth hpos (m + 1) (by omega)
      have hj : (π j).natDegree = j := (hmon j (by omega)).2
      rw [Polynomial.natDegree_X_mul (hmon j (by omega)).1.ne_zero, hj]
      omega
    rw [h1, h2]; simp
  set a : ℝ := momentForm ν r (π (m + 1)) / momentForm ν (π (m + 1)) (π (m + 1)) with ha
  set b : ℝ := momentForm ν r (π m) / momentForm ν (π m) (π m) with hb
  have hr_eq : r = Polynomial.C a * π (m + 1) + Polynomial.C b * π m := by
    have hsum0 : ∑ j ∈ Finset.range m,
        Polynomial.C (momentForm ν r (π j) / momentForm ν (π j) (π j)) * π j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjlt : j < m := Finset.mem_range.mp hj
      rw [hzero j (by simp; omega) (by omega) (by omega)]
      simp
    calc r = ∑ j ∈ Finset.range (m + 1 + 1),
          Polynomial.C (momentForm ν r (π j) / momentForm ν (π j) (π j)) * π j := hdec
      _ = Polynomial.C a * π (m + 1) + Polynomial.C b * π m := by
        rw [Finset.sum_range_succ, Finset.sum_range_succ, hsum0]
        rw [ha, hb]
        ring
  have hb_pos : 0 < b := by
    have hnum : momentForm ν r (π m) = momentForm ν (π (m + 1)) (π (m + 1)) := by
      rw [hr, momentForm_sub_left, momentForm_X_mul]
      have h2 : momentForm ν (π (m + 2)) (π m) = 0 :=
        horth (m + 2) m (by omega) (by omega) (by omega)
      rw [h2, sub_zero]
      have hdiff : momentForm ν (π (m + 1)) (Polynomial.X * π m - π (m + 1)) = 0 := by
        apply orth_of_natDegree_lt ν d π hmon horth hpos (m + 1) (by omega)
        have h1 : (π m).Monic ∧ (π m).natDegree = m := hmon m (by omega)
        have h2 : (π (m + 1)).Monic ∧ (π (m + 1)).natDegree = m + 1 := hmon (m + 1) (by omega)
        have hA : (Polynomial.X * π m).Monic := Polynomial.monic_X.mul h1.1
        have hAdeg : (Polynomial.X * π m).natDegree = m + 1 := by
          rw [Polynomial.natDegree_X_mul h1.1.ne_zero, h1.2]
        have hlt : (Polynomial.X * π m - π (m + 1)).degree
            < (Polynomial.X * π m).degree := by
          apply Polynomial.degree_sub_lt_left
          · rw [Polynomial.degree_eq_natDegree hA.ne_zero,
              Polynomial.degree_eq_natDegree h2.1.ne_zero, hAdeg, h2.2]
          · exact hA.ne_zero
          · rw [hA.leadingCoeff, h2.1.leadingCoeff]
        by_cases h0 : Polynomial.X * π m - π (m + 1) = 0
        · rw [h0]; simp
        · have := Polynomial.natDegree_lt_natDegree h0 hlt
          omega
      rw [momentForm_sub_right] at hdiff
      linarith
    have hpos1 : 0 < momentForm ν (π (m + 1)) (π (m + 1)) := by
      have h := hmon (m + 1) (by omega)
      exact momentForm_pos ν (m + 2) (hpos (m + 2) (by omega) (by omega))
        (π (m + 1)) (by rw [h.2]; omega) h.1.ne_zero
    have hpos2 : 0 < momentForm ν (π m) (π m) := by
      have h := hmon m (by omega)
      exact momentForm_pos ν (m + 1) (hpos (m + 1) (by omega) (by omega))
        (π m) (by rw [h.2]; omega) h.1.ne_zero
    rw [hb, hnum]
    exact div_pos hpos1 hpos2
  refine ⟨a, b, hb_pos, ?_⟩
  have : π (m + 2) = Polynomial.X * π (m + 1) - r := by rw [hr]; ring
  rw [this, hr_eq]
  ring

lemma exists_real_wNode {d : ℕ} (z : Fin d → ℂ) (a : ℂ) (θ : ℝ)
    (hal : ∀ j, ∃ x : ℝ, z j = a + Complex.exp (θ * Complex.I) * x) :
    ∃ x : Fin d → ℝ, ∀ j, wNode z a θ j = (x j : ℂ) := by
  choose x hx using hal
  exact ⟨x, fun j => wNode_real z a θ j (x j) (hx j)⟩

lemma nuMoment_eq_ofReal {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) (a : ℂ) (θ : ℝ)
    (x : Fin d → ℝ) (hx : ∀ j, wNode z a θ j = (x j : ℂ)) (k : ℕ) :
    nuMoment z m a θ k = ((∑ j, (m j : ℝ) * (x j) ^ k : ℝ) : ℂ) := by
  rw [nuMoment_eq]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hx j]

lemma HankelR_eq_map {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) (a : ℂ) (θ : ℝ)
    (x : Fin d → ℝ) (hx : ∀ j, wNode z a θ j = (x j : ℂ)) (r : ℕ) :
    HankelR z m a θ r = (HankelRR x m r).map (algebraMap ℝ ℂ) := by
  ext p q
  simp only [HankelR, HankelRR, Matrix.of_apply, Matrix.map_apply]
  rw [nuMoment_eq_ofReal z m a θ x hx]
  rfl

lemma det_map_ofReal {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) :
    (A.map (algebraMap ℝ ℂ)).det = ((A.det : ℝ) : ℂ) := by
  have := (algebraMap ℝ ℂ).map_det A
  simpa using this.symm

lemma HankelR_entries_real {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) (a : ℂ) (θ : ℝ)
    (hreal : ∀ k ≤ 2 * d - 2, (nuMoment z m a θ k).im = 0)
    {r : ℕ} (hr : r ≤ d) (p q : Fin r) :
    (HankelR z m a θ r p q).im = 0 := by
  simp only [HankelR, Matrix.of_apply]
  apply hreal
  have hp := p.isLt
  have hq := q.isLt
  omega

lemma quad_HankelSeq_eq_re {d : ℕ} (w : Fin d → ℂ) (m : Fin d → ℕ)
    (c : Fin d → ℝ) :
    c ⬝ᵥ ((HankelSeq (fun k => (∑ j, (m j : ℂ) * w j ^ k).re) d) *ᵥ c)
      = (∑ j, (m j : ℂ) * (∑ p, (c p : ℂ) * w j ^ (p : ℕ)) ^ 2).re := by
  have h : (∑ j, (m j : ℂ) * (∑ p, (c p : ℂ) * w j ^ (p : ℕ)) ^ 2)
      = ∑ p, ∑ q, (c p : ℂ) * (c q : ℂ) * ∑ j, (m j : ℂ) * w j ^ ((p : ℕ) + q) := by
    simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [h]
  simp [Matrix.mulVec, dotProduct, HankelSeq, Complex.re_sum, Finset.mul_sum, mul_assoc,
    mul_comm]

------------------------------------------------------------------
-- now the other sens of the equivalence

open Polynomial Matrix BigOperators

variable {d : ℕ}


lemma mem_droite_of_real {d : ℕ} (a : ℂ) (θ : ℝ) (z : Fin d → ℂ)
    (h : ∀ j, (Complex.exp (-(θ * Complex.I)) * (z j - a)).im = 0) :
    ∀ j, ∃ x : ℝ, z j = a + Complex.exp (θ * Complex.I) * x := by
  intro j
  have he :
      Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  refine ⟨(Complex.exp (-(θ * Complex.I)) * (z j - a)).re, ?_⟩
  have hu : Complex.exp (-(θ * Complex.I)) * (z j - a)
      = ((Complex.exp (-(θ * Complex.I)) * (z j - a)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using h j)
  rw [← hu, ← mul_assoc, he, one_mul]
  ring

lemma nodes_injective {d : ℕ} (a : ℂ) (θ : ℝ) (z : Fin d → ℂ)
    (hz : Function.Injective z) :
    Function.Injective (fun j => Complex.exp (-(θ * Complex.I)) * (z j - a)) := by
  intro i j hij
  have hne : Complex.exp (-(θ * Complex.I)) ≠ 0 := Complex.exp_ne_zero _
  have h1 : z i - a = z j - a := by
    have hij' : Complex.exp (-(θ * Complex.I)) * (z i - a)
        = Complex.exp (-(θ * Complex.I)) * (z j - a) := hij
    exact mul_left_cancel₀ hne hij'
  have h2 : z i = z j := by linear_combination h1
  exact hz h2

lemma L_eq_sum {d : ℕ} (w : Fin d → ℂ) (m : Fin d → ℕ)
    (hreal : ∀ k ≤ 2 * d - 2, (nu w m k).im = 0)
    (P : ℝ[X]) (hP : P.natDegree ≤ 2 * d - 2) :
    ((L w m P : ℝ) : ℂ) = ∑ j, (m j : ℂ) * (P.map (algebraMap ℝ ℂ)).eval (w j) := by
  rw [P.as_sum_range' (2 * d - 2 + 1) (Nat.lt_succ_of_le hP)]
  rw [map_sum, Complex.ofReal_sum]
  simp only [Polynomial.map_sum, Polynomial.eval_finsetSum, Polynomial.map_monomial,
    Polynomial.eval_monomial, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ 2 * d - 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hL : L w m (Polynomial.monomial k (P.coeff k))
      = P.coeff k * nuR w m k := by
    simp [L, Polynomial.lsum_apply, nuR]
    ring
  have hnu : ((nuR w m k : ℝ) : ℂ) = nu w m k := by
    apply Complex.ext
    · simp [nuR]
    · simpa [nuR] using (hreal k hk').symm
  rw [hL]
  push_cast
  rw [hnu]
  simp only [nu, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp
  ring

lemma L_monomial_mul {d : ℕ} (w : Fin d → ℂ) (m : Fin d → ℕ) (p q : Fin d) :
    L w m ((X : ℝ[X]) ^ (p : ℕ) * X ^ (q : ℕ)) = hankel w m p q := by
  rw [← pow_add]
  rw [← Polynomial.monomial_one_right_eq_X_pow]
  have hL : L w m (Polynomial.monomial ((p : ℕ) + q) (1 : ℝ))
      = nuR w m ((p : ℕ) + q) := by
    simp [L, Polynomial.lsum_apply, nuR]
  rw [hL]
  simp [hankel]


lemma posDef_fin_zero (H : Matrix (Fin 0) (Fin 0) ℝ) : H.PosDef := by
  refine ⟨?_, ?_⟩
  · ext i
    exact i.elim0
  · intro x hx
    exact absurd (Subsingleton.elim x 0) hx


lemma minors_of_succ {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hminors : ∀ r : ℕ, (hr : r ≤ n + 1) → 0 < (H.submatrix
      (Fin.castLE hr) (Fin.castLE hr)).det) :
    ∀ r : ℕ, (hr : r ≤ n) → 0 < ((H.submatrix Fin.castSucc Fin.castSucc).submatrix
      (Fin.castLE hr) (Fin.castLE hr)).det := by
  intro r hr
  rw [Matrix.submatrix_submatrix]
  have h : (Fin.castSucc ∘ Fin.castLE hr : Fin r → Fin (n+1))
      = Fin.castLE (hr.trans (Nat.le_succ n)) := by
    funext i
    rfl
  rw [h]
  exact hminors r (hr.trans (Nat.le_succ n))

lemma isHermitian_of_isSymm_real {m : Type*}
    (H : Matrix m m ℝ) (hsymm : H.IsSymm) : H.IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hsymm

lemma mulVec_inv_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hAunit : IsUnit A.det) (b : Fin n → ℝ) :
    A *ᵥ (A⁻¹ *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ hAunit, Matrix.one_mulVec]

lemma last_row_eq_last_col {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsymm : H.IsSymm) (j : Fin n) :
    H (Fin.last n) (Fin.castSucc j) = H (Fin.castSucc j) (Fin.last n) := by
  have := congrFun (congrFun hsymm (Fin.castSucc j)) (Fin.last n)
  simpa [Matrix.transpose_apply] using this

lemma submatrix_castSucc_isSymm {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsymm : H.IsSymm) : (H.submatrix Fin.castSucc Fin.castSucc).IsSymm := by
  ext i j
  have := congrFun (congrFun hsymm (Fin.castSucc j)) (Fin.castSucc i)
  simpa [Matrix.transpose_apply] using this.symm

lemma det_eq_det_mul_schur {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsymm : H.IsSymm)
    (hAunit : IsUnit (H.submatrix Fin.castSucc Fin.castSucc).det) :
    H.det = (H.submatrix Fin.castSucc Fin.castSucc).det *
      (H (Fin.last n) (Fin.last n) -
        (fun j => H (Fin.castSucc j) (Fin.last n)) ⬝ᵥ
        ((H.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
          (fun j => H (Fin.castSucc j) (Fin.last n)))) := by
  classical
  set A := H.submatrix Fin.castSucc Fin.castSucc with hAdef
  set b : Fin n → ℝ := fun j => H (Fin.castSucc j) (Fin.last n) with hb
  set c := H (Fin.last n) (Fin.last n) with hc
  set e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv with he
  have hl : ∀ i : Fin n, e (Sum.inl i) = Fin.castSucc i := by
    intro i; exact Fin.ext (by simp [he])
  have hr : ∀ k : Fin 1, e (Sum.inr k) = Fin.last n := by
    intro k; exact Fin.ext (by simp [he, Subsingleton.elim k 0])
  have hblock : Matrix.reindex e.symm e.symm H =
      Matrix.fromBlocks A (Matrix.of fun i (_ : Fin 1) => b i)
        (Matrix.of fun (_ : Fin 1) j => b j) (Matrix.of fun _ _ => c) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [Matrix.reindex_apply, hl, hAdef]
    · simp [Matrix.reindex_apply, hl, hr, hb]
    · simp [Matrix.reindex_apply, hl, hr, hb, last_row_eq_last_col H hsymm j]
    · simp [Matrix.reindex_apply, hr, hc]
  have hinv : Invertible A := Matrix.invertibleOfIsUnitDet A hAunit
  rw [← Matrix.det_reindex_self e.symm H, hblock, Matrix.det_fromBlocks₁₁]
  have hAsymm : A.IsSymm := by
    have h := hsymm.apply
    ext i j
    simp only [Matrix.transpose_apply, hAdef, Matrix.submatrix_apply]
    exact h _ _
  have hAinvsymm : (A⁻¹).IsSymm := hAsymm.inv
  have hsy : ∀ i j, A⁻¹ i j = A⁻¹ j i := fun i j => (hAinvsymm.apply i j).symm
  congr 1
  rw [Matrix.det_fin_one, Matrix.invOf_eq_nonsing_inv]
  have key : ((Matrix.of fun (_ : Fin 1) j => b j) * A⁻¹ *
      (Matrix.of fun i (_ : Fin 1) => b i)) 0 0 = b ⬝ᵥ (A⁻¹ *ᵥ b) := by
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.of_apply]
    simp only [Finset.mul_sum, mul_comm]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ => ?_
    rw [hsy i x]
  simp [Matrix.sub_apply, key]

lemma pos_of_det_factor {dH dA s : ℝ} (hdH : 0 < dH) (hdA : 0 < dA)
    (h : dH = dA * s) : 0 < s := by
  rw [h] at hdH
  exact pos_of_mul_pos_right hdH hdA.le

lemma quad_expand {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hAsymm : A.IsSymm)
    (u b : Fin n → ℝ) (hu : A *ᵥ u = b) (x' : Fin n → ℝ) (t : ℝ) :
    (x' + t • u) ⬝ᵥ A *ᵥ (x' + t • u)
      = x' ⬝ᵥ A *ᵥ x' + 2 * t * (x' ⬝ᵥ b) + t ^ 2 * (u ⬝ᵥ b) := by
  have hcross : u ⬝ᵥ A *ᵥ x' = x' ⬝ᵥ A *ᵥ u := by
    have h1 : u ⬝ᵥ A *ᵥ x' = (u ᵥ* A) ⬝ᵥ x' := Matrix.dotProduct_mulVec u A x'
    have h2 : u ᵥ* A = A *ᵥ u := by
      conv_lhs => rw [← hAsymm]
      exact Matrix.vecMul_transpose A u
    rw [h1, h2, dotProduct_comm]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add, dotProduct_add,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct, hcross, hu]
  simp only [smul_eq_mul]
  ring

lemma snoc_quadratic {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsymm : H.IsSymm) (x' : Fin n → ℝ) (t : ℝ) :
    (Fin.snoc x' t : Fin (n + 1) → ℝ) ⬝ᵥ H *ᵥ (Fin.snoc x' t : Fin (n + 1) → ℝ)
      = x' ⬝ᵥ (H.submatrix Fin.castSucc Fin.castSucc) *ᵥ x'
        + 2 * t * ((fun j => H (Fin.castSucc j) (Fin.last n)) ⬝ᵥ x')
        + t ^ 2 * H (Fin.last n) (Fin.last n) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, Matrix.submatrix_apply, last_row_eq_last_col H hsymm]
  simp only [Finset.mul_sum, mul_add]
  rw [Finset.sum_add_distrib]
  have h1 : ∑ x, x' x * (H x.castSucc (Fin.last n) * t)
      = ∑ i, t * (H i.castSucc (Fin.last n) * x' i) :=
    Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, 2 * t * (H i.castSucc (Fin.last n) * x' i)
      = ∑ i, t * (H i.castSucc (Fin.last n) * x' i)
        + ∑ i, t * (H i.castSucc (Fin.last n) * x' i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2, h1]
  ring

lemma completing_square {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsymm : H.IsSymm)
    (hAunit : IsUnit (H.submatrix Fin.castSucc Fin.castSucc).det)
    (x' : Fin n → ℝ) (t : ℝ) :
    (Fin.snoc x' t : Fin (n + 1) → ℝ) ⬝ᵥ H *ᵥ (Fin.snoc x' t : Fin (n + 1) → ℝ)
      = (x' + t • ((H.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
            (fun j => H (Fin.castSucc j) (Fin.last n))))
        ⬝ᵥ (H.submatrix Fin.castSucc Fin.castSucc) *ᵥ
          (x' + t • ((H.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
            (fun j => H (Fin.castSucc j) (Fin.last n))))
        + t ^ 2 * (H (Fin.last n) (Fin.last n) -
          (fun j => H (Fin.castSucc j) (Fin.last n)) ⬝ᵥ
          ((H.submatrix Fin.castSucc Fin.castSucc)⁻¹ *ᵥ
            (fun j => H (Fin.castSucc j) (Fin.last n)))) := by
  set A := H.submatrix Fin.castSucc Fin.castSucc with hAdef
  set b : Fin n → ℝ := fun j => H (Fin.castSucc j) (Fin.last n) with hb
  set u := A⁻¹ *ᵥ b with hu
  have hu_eq : A *ᵥ u = b := mulVec_inv_mulVec A hAunit b
  have hAsymm : A.IsSymm := submatrix_castSucc_isSymm H hsymm
  rw [snoc_quadratic H hsymm x' t, quad_expand A hAsymm u b hu_eq x' t,
    dotProduct_comm b x', dotProduct_comm u b]
  ring

lemma quad_pos' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    {s : ℝ} (hs : 0 < s) (u : Fin n → ℝ) (x : Fin (n + 1) → ℝ) (hx : x ≠ 0) :
    0 < (Fin.init x + x (Fin.last n) • u) ⬝ᵥ A *ᵥ (Fin.init x + x (Fin.last n) • u)
      + (x (Fin.last n)) ^ 2 * s := by
  rw [Matrix.posDef_iff_dotProduct_mulVec] at hA
  obtain ⟨_, hApos⟩ := hA
  by_cases ht : x (Fin.last n) = 0
  · have hx'ne : Fin.init x ≠ 0 := by
      intro h
      apply hx
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using ht
      · have := congrFun h j
        simpa [Fin.init] using this
    have := hApos hx'ne
    simpa [ht] using this
  · have h1 : 0 ≤ (Fin.init x + x (Fin.last n) • u) ⬝ᵥ
        A *ᵥ (Fin.init x + x (Fin.last n) • u) := by
      by_cases hz : Fin.init x + x (Fin.last n) • u = 0
      · simp [hz]
      · simpa using (hApos hz).le
    have h2 : 0 < (x (Fin.last n)) ^ 2 * s := mul_pos (by positivity) hs
    exact add_pos_of_nonneg_of_pos h1 h2

lemma posDef_succ_step {n : ℕ} (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsymm : H.IsSymm)
    (hA : (H.submatrix Fin.castSucc Fin.castSucc).PosDef)
    (hdet : 0 < H.det) : H.PosDef := by
  classical
  have hdetA : 0 < (H.submatrix Fin.castSucc Fin.castSucc).det := hA.det_pos
  have hAunit : IsUnit (H.submatrix Fin.castSucc Fin.castSucc).det := hdetA.ne'.isUnit
  have hdetH := det_eq_det_mul_schur H hsymm hAunit
  have hs_pos := pos_of_det_factor hdet hdetA hdetH
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_of_isSymm_real H hsymm, ?_⟩
  intro x hx
  have hx' : x = (Fin.snoc (Fin.init x) (x (Fin.last n)) : Fin (n + 1) → ℝ) :=
    (Fin.snoc_init_self x).symm
  rw [star_trivial, hx', completing_square H hsymm hAunit]
  exact quad_pos' _ hA hs_pos _ x hx

lemma posDef_of_leading_minors {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hsymm : H.IsSymm)
    (hminors : ∀ r : ℕ, (hr : r ≤ n) → 0 < (H.submatrix
      (Fin.castLE hr) (Fin.castLE hr)).det) :
    H.PosDef := by
  induction n with
  | zero => exact posDef_fin_zero H
  | succ n ih =>
    have hAsymm : (H.submatrix Fin.castSucc Fin.castSucc).IsSymm := by
      ext i j; exact congrFun (congrFun hsymm _) _
    have hA := ih _ hAsymm (minors_of_succ H hminors)
    have hdet := hminors (n + 1) le_rfl
    refine posDef_succ_step H hsymm hA ?_
    simpa using hdet

lemma L_sq_pos (w : Fin d → ℂ) (hd : 0 < d) (hH : (hankel w m).PosDef)
    (P : ℝ[X]) (hP0 : P ≠ 0) (hP : P.natDegree ≤ d - 1) :
    0 < L w m (P ^ 2) := by
  have hlt : P.natDegree < d := by omega
  have hHS : (HankelSeq (nuR w m) d).PosDef := by
    have : HankelSeq (nuR w m) d = hankel w m := by
      ext p q; rfl
    rw [this]; exact hH
  have hL : L w m (P ^ 2) = momentForm (nuR w m) P P := by
    have hLX : ∀ k : ℕ, L w m (X ^ k) = nuR w m k := by
      intro k
      simp [L, Polynomial.lsum_apply, ← Polynomial.monomial_one_right_eq_X_pow]
    have hPsum : P = ∑ p ∈ Finset.range (P.natDegree + 1),
        Polynomial.C (P.coeff p) * X ^ p := by
      conv_lhs => rw [P.as_sum_range_C_mul_X_pow]
    have hP2 : P ^ 2 = ∑ p ∈ Finset.range (P.natDegree + 1),
        ∑ q ∈ Finset.range (P.natDegree + 1),
          Polynomial.C (P.coeff p * P.coeff q) * X ^ (p + q) := by
      rw [sq]
      calc P * P
          = (∑ p ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff p) * X ^ p) *
            (∑ q ∈ Finset.range (P.natDegree + 1), Polynomial.C (P.coeff q) * X ^ q) := by
            rw [← hPsum]
        _ = _ := by
            rw [Finset.sum_mul_sum]
            refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
            rw [pow_add, Polynomial.C_mul]; ring
    rw [hP2, map_sum]
    unfold momentForm
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← Polynomial.smul_eq_C_mul, map_smul, hLX]
    simp [smul_eq_mul]
  rw [hL]
  exact momentForm_pos (nuR w m) d hHS P hlt hP0

lemma L_mul_eq_momentForm (w : Fin d → ℂ) (m : Fin d → ℕ) (P Q : ℝ[X]) :
    L w m (P * Q) = momentForm (nuR w m) P Q := by
  have hLX : ∀ k : ℕ, L w m (X ^ k) = nuR w m k := by
    intro k
    simp [L, Polynomial.lsum_apply, ← Polynomial.monomial_one_right_eq_X_pow]
  have hP : P = ∑ p ∈ Finset.range (P.natDegree + 1), C (P.coeff p) * X ^ p :=
    P.as_sum_range_C_mul_X_pow
  have hQ : Q = ∑ q ∈ Finset.range (Q.natDegree + 1), C (Q.coeff q) * X ^ q :=
    Q.as_sum_range_C_mul_X_pow
  calc L w m (P * Q)
      = L w m ((∑ p ∈ Finset.range (P.natDegree + 1), C (P.coeff p) * X ^ p) *
          (∑ q ∈ Finset.range (Q.natDegree + 1), C (Q.coeff q) * X ^ q)) := by
        rw [← hP, ← hQ]
    _ = momentForm (nuR w m) P Q := by
        rw [Finset.sum_mul_sum, map_sum]
        unfold momentForm
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        have : (C (P.coeff p) * X ^ p) * (C (Q.coeff q) * X ^ q)
            = C (P.coeff p * Q.coeff q) * X ^ (p + q) := by
          rw [pow_add, C_mul]; ring
        rw [this, ← Polynomial.smul_eq_C_mul, map_smul, hLX]
        simp [smul_eq_mul]

lemma posDef_submatrix_castLE {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ)
    (hH : H.PosDef) {r : ℕ} (hr : r ≤ d) :
    (H.submatrix (Fin.castLE hr) (Fin.castLE hr)).PosDef :=
  hH.submatrix (Fin.castLE_injective hr)


lemma exists_orthogonal_monic' (w : Fin d → ℂ) (m : Fin d → ℕ) (hd : 0 < d)
    (hH : (hankel w m).PosDef) :
    ∃ prod : ℝ[X], prod.Monic ∧ prod.natDegree = d ∧
      ∀ Q : ℝ[X], Q.natDegree ≤ d - 1 → L w m (Q * prod) = 0 := by
  have hpos : ∀ r : ℕ, 1 ≤ r → r ≤ d → (HankelSeq (nuR w m) r).PosDef := by
    intro r _ hr
    have hsub : HankelSeq (nuR w m) r
        = (hankel w m).submatrix (Fin.castLE hr) (Fin.castLE hr) := by
      ext p q; rfl
    rw [hsub]
    exact posDef_submatrix_castLE (hankel w m) hH hr
  obtain ⟨π, hπ, horth⟩ := exists_orthogonal_monic (nuR w m) d hpos
  obtain ⟨hmonic, hdeg⟩ := hπ d le_rfl
  refine ⟨π d, hmonic, hdeg, ?_⟩
  intro Q hQ
  have key : ∀ n : ℕ, ∀ Q : ℝ[X], Q.natDegree ≤ d - 1 → Q.natDegree = n →
      L w m (Q * π d) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro Q hQ hn
      by_cases hQ0 : Q = 0
      · simp [hQ0]
      · set k := Q.natDegree with hk
        have hkd : k < d := by omega
        set R := Q - C Q.leadingCoeff * π k with hR
        have hπk := hπ k (by omega)
        have hCπ_deg : (C Q.leadingCoeff * π k).natDegree = k := by
          rw [natDegree_C_mul (leadingCoeff_ne_zero.mpr hQ0), hπk.2]
        have hCπ_lead : (C Q.leadingCoeff * π k).leadingCoeff = Q.leadingCoeff := by
          rw [leadingCoeff_mul, leadingCoeff_C, hπk.1.leadingCoeff, mul_one]
        have hRdeg : R.natDegree < k ∨ R = 0 := by
          by_cases hR0 : R = 0
          · exact Or.inr hR0
          · left
            have hCπ_ne : C Q.leadingCoeff * π k ≠ 0 := by
              intro h
              have hl : (C Q.leadingCoeff * π k).leadingCoeff = 0 := by rw [h]; simp
              rw [hCπ_lead] at hl
              exact leadingCoeff_ne_zero.mpr hQ0 hl
            have hdeg_eq : Q.degree = (C Q.leadingCoeff * π k).degree := by
              rw [degree_eq_natDegree hQ0, degree_eq_natDegree hCπ_ne, hCπ_deg]
            have hlt : R.degree < Q.degree := by
              rw [hR]
              exact Polynomial.degree_sub_lt_left hdeg_eq hQ0 hCπ_lead.symm
            exact natDegree_lt_natDegree hR0 hlt
        have hLQ : L w m (Q * π d) = Q.leadingCoeff * momentForm (nuR w m) (π k) (π d)
            + L w m (R * π d) := by
          have hQeq : Q * π d = Q.leadingCoeff • (π k * π d) + R * π d := by
            rw [hR, smul_eq_C_mul]; ring
          rw [hQeq, map_add, map_smul, L_mul_eq_momentForm]
          rfl
        rw [hLQ]
        have h1 : momentForm (nuR w m) (π k) (π d) = 0 :=
          horth k d (by omega) le_rfl (by omega)
        have h2 : L w m (R * π d) = 0 := by
          rcases hRdeg with hlt | hR0
          · exact ih R.natDegree (by omega) R (by omega) rfl
          · simp [hR0]
        rw [h1, h2]; simp
  exact key Q.natDegree Q hQ rfl

lemma brahmagupta (p q r s : ℝ[X]) :
    (p ^ 2 + q ^ 2) * (r ^ 2 + s ^ 2) =
    (p * r - q * s) ^ 2 + (p * s + q * r) ^ 2 := by
  ring


lemma even_rootMultiplicity_of_nonneg (R : ℝ[X]) (hR0 : R ≠ 0)
    (hR : ∀ x : ℝ, 0 ≤ R.eval x) (a : ℝ) :
    Even (R.rootMultiplicity a) := by
  obtain ⟨S, hRS, hSa⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd R hR0 a
  set k := R.rootMultiplicity a with hk
  have hSa' : S.eval a ≠ 0 := by
    intro h
    exact hSa (Polynomial.dvd_iff_isRoot.mpr h)
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  have hcont : Continuous fun x => S.eval x := S.continuous
  rcases lt_or_gt_of_ne hSa' with hneg | hpos
  · obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ x, |x - a| < δ → S.eval x < 0 := by
      have hopen : IsOpen {x : ℝ | S.eval x < 0} := isOpen_lt hcont continuous_const
      obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen a hneg
      exact ⟨δ, hδ, fun x hx => hsub (by simpa [Metric.mem_ball, Real.dist_eq] using hx)⟩
    have h1 := hR (a + δ / 2)
    rw [hRS] at h1
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, add_sub_cancel_left] at h1
    have hS1 : S.eval (a + δ / 2) < 0 := hball _ (by
      rw [add_sub_cancel_left, abs_of_pos (by linarith)]; linarith)
    have hpow1 : 0 < (δ / 2) ^ k := pow_pos (by linarith) k
    have h2 := hR (a - δ / 2)
    rw [hRS] at h2
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at h2
    have hS2 : S.eval (a - δ / 2) < 0 := hball _ (by
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by linarith)]; linarith)
    have hpow2 : (a - δ / 2 - a) ^ k < 0 := by
      have : a - δ / 2 - a = -(δ / 2) := by ring
      rw [this, hodd.neg_pow]
      exact neg_neg_of_pos hpow1
    nlinarith [mul_neg_of_pos_of_neg hpow1 hS1]
  · obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, ∀ x, |x - a| < δ → 0 < S.eval x := by
      have hopen : IsOpen {x : ℝ | 0 < S.eval x} := isOpen_lt continuous_const hcont
      obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hopen a hpos
      exact ⟨δ, hδ, fun x hx => hsub (by simpa [Metric.mem_ball, Real.dist_eq] using hx)⟩
    have h2 := hR (a - δ / 2)
    rw [hRS] at h2
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at h2
    have hS2 : 0 < S.eval (a - δ / 2) := hball _ (by
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos (by linarith)]; linarith)
    have hpow2 : (a - δ / 2 - a) ^ k < 0 := by
      have : a - δ / 2 - a = -(δ / 2) := by ring
      rw [this, hodd.neg_pow]
      exact neg_neg_of_pos (pow_pos (by linarith) k)
    nlinarith [mul_neg_of_neg_of_pos hpow2 hS2]

lemma nonneg_of_sq_mul_nonneg (R S : ℝ[X]) (a : ℝ)
    (hS : R = (X - C a) ^ 2 * S) (hR : ∀ x : ℝ, 0 ≤ R.eval x) :
    ∀ x : ℝ, 0 ≤ S.eval x := by
  have hne : ∀ x : ℝ, x ≠ a → 0 ≤ S.eval x := by
    intro x hx
    have h := hR x
    rw [hS] at h
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at h
    have hpos : 0 < (x - a) ^ 2 := by
      have : x - a ≠ 0 := sub_ne_zero.mpr hx
      positivity
    exact nonneg_of_mul_nonneg_right h hpos
  intro x
  by_cases hx : x = a
  · subst hx
    have hlim : Filter.Tendsto (fun k : ℕ => S.eval (x + 1 / ((k : ℝ) + 1)))
        Filter.atTop (nhds (S.eval x)) := by
      have h1 : Filter.Tendsto (fun k : ℕ => x + 1 / ((k : ℝ) + 1))
          Filter.atTop (nhds (x + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
      rw [add_zero] at h1
      exact (S.continuous.tendsto x).comp h1
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun k => hne _ ?_)
    have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    intro h; linarith
  · exact hne x hx

lemma natDegree_of_sq_mul (R S : ℝ[X]) (a : ℝ)
    (hS : R = (X - C a) ^ 2 * S) (hR0 : R ≠ 0) :
    S ≠ 0 ∧ 2 ≤ R.natDegree ∧ S.natDegree = R.natDegree - 2 := by
  have hS0 : S ≠ 0 := by
    intro h
    apply hR0
    rw [hS, h, mul_zero]
  have hdeg : R.natDegree = 2 + S.natDegree := by
    have := congrArg natDegree hS
    rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero a)) hS0,
      natDegree_pow, natDegree_X_sub_C] at this
    simpa using this
  refine ⟨hS0, by omega, by omega⟩

lemma sum_two_squares_real_root (n : ℕ)
    (ih : ∀ m < n, ∀ R : ℝ[X], (∀ x : ℝ, 0 ≤ R.eval x) → R.natDegree = m →
      ∃ A B : ℝ[X], R = A ^ 2 + B ^ 2 ∧ 2 * A.natDegree ≤ m ∧ 2 * B.natDegree ≤ m)
    (R : ℝ[X]) (hR : ∀ x : ℝ, 0 ≤ R.eval x) (hn : R.natDegree = n)
    (hR0 : R ≠ 0) (a : ℝ) (ha : R.IsRoot a) :
    ∃ A B : ℝ[X], R = A ^ 2 + B ^ 2 ∧ 2 * A.natDegree ≤ n ∧ 2 * B.natDegree ≤ n := by
  have hk_even := even_rootMultiplicity_of_nonneg R hR0 hR a
  have hk_pos : 0 < R.rootMultiplicity a :=
    (Polynomial.rootMultiplicity_pos hR0).mpr ha
  obtain ⟨j, hj⟩ := hk_even
  have hdvd : (X - C a) ^ 2 ∣ R := by
    refine dvd_trans (pow_dvd_pow _ (by omega)) (Polynomial.pow_rootMultiplicity_dvd R a)
  obtain ⟨S, hS⟩ := hdvd
  obtain ⟨hS0, hn2', hdegS⟩ := natDegree_of_sq_mul R S a hS hR0
  have hSnn := nonneg_of_sq_mul_nonneg R S a hS hR
  have hn2 : 2 ≤ n := by omega
  obtain ⟨A', B', hSAB, hA', hB'⟩ := ih (n - 2) (by omega) S hSnn (by omega)
  have hdegX : ∀ T : ℝ[X], 2 * T.natDegree ≤ n - 2 →
      2 * ((X - C a) * T).natDegree ≤ n := by
    intro T hT
    have h1 : ((X - C a) * T).natDegree ≤ 1 + T.natDegree := by
      calc _ ≤ (X - C a).natDegree + T.natDegree := natDegree_mul_le
        _ = 1 + T.natDegree := by rw [natDegree_X_sub_C]
    omega
  refine ⟨(X - C a) * A', (X - C a) * B', ?_, hdegX A' hA', hdegX B' hB'⟩
  rw [hS, hSAB]; ring

lemma quad_eval_zero (z : ℂ) :
    (((X - C z.re) ^ 2 + C z.im ^ 2 : ℝ[X]).map (algebraMap ℝ ℂ)).eval z = 0 := by
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, eval_add, eval_pow, eval_sub, eval_X, eval_C,
    Complex.coe_algebraMap]
  apply Complex.ext <;> simp [pow_two]

lemma quad_eval_zero_conj (z : ℂ) :
    (((X - C z.re) ^ 2 + C z.im ^ 2 : ℝ[X]).map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = 0 := by
  simp only [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C, eval_add, eval_pow, eval_sub, eval_X, eval_C,
    Complex.coe_algebraMap]
  apply Complex.ext <;> simp [pow_two]

lemma conj_root (R : ℝ[X]) (z : ℂ)
    (hz : (R.map (algebraMap ℝ ℂ)).eval z = 0) :
    (R.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = 0 := by
  have key : ∀ P : ℝ[X],
      (P.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z)
        = starRingEnd ℂ ((P.map (algebraMap ℝ ℂ)).eval z) := by
    intro P
    induction P using Polynomial.induction_on' with
    | add p q hp hq => simp [Polynomial.map_add, eval_add, hp, hq]
    | monomial n a => simp [Polynomial.map_monomial, eval_monomial]
  rw [key R, hz, map_zero]

lemma poly_deg_lt_two_zero (T : ℝ[X]) (z : ℂ) (hz : z.im ≠ 0) (hT : T.natDegree < 2)
    (h1 : (T.map (algebraMap ℝ ℂ)).eval z = 0)
    (h2 : (T.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ z) = 0) : T = 0 := by
  by_contra hT0
  set Tc : ℂ[X] := T.map (algebraMap ℝ ℂ) with hTc
  have hTc0 : Tc ≠ 0 := by
    rw [hTc]; exact (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hT0
  have hdegc : Tc.natDegree < 2 := by
    rw [hTc, Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective]; exact hT
  have hne : z ≠ starRingEnd ℂ z := by
    intro h
    apply hz
    have := congrArg Complex.im h
    simp at this
    linarith
  have hsub : ({z, starRingEnd ℂ z} : Finset ℂ) ⊆ Tc.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hTc0]
    rcases hx with rfl | rfl
    · exact h1
    · exact h2
  have hcard : 2 ≤ Tc.roots.toFinset.card := by
    calc 2 = ({z, starRingEnd ℂ z} : Finset ℂ).card := by
            rw [Finset.card_pair hne]
      _ ≤ _ := Finset.card_le_card hsub
  have hle : Tc.roots.toFinset.card ≤ Tc.natDegree :=
    (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' Tc)
  omega

lemma exists_quadratic_factor (R : ℝ[X]) (hdeg : 0 < R.natDegree)
    (hroot : ∀ a : ℝ, ¬ R.IsRoot a) :
    ∃ b c : ℝ, c ≠ 0 ∧ ((X - C b) ^ 2 + C c ^ 2) ∣ R := by
  set Rc : ℂ[X] := R.map (algebraMap ℝ ℂ) with hRc
  have hRcdeg : 0 < Rc.degree := by
    have hnat : Rc.natDegree = R.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (algebraMap ℝ ℂ).injective R
    exact Polynomial.natDegree_pos_iff_degree_pos.mp (by rw [hnat]; exact hdeg)
  obtain ⟨z, hz⟩ := Complex.exists_root hRcdeg
  have hz' : Rc.eval z = 0 := hz
  have him : z.im ≠ 0 := by
    intro h0
    apply hroot z.re
    have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
    rw [hzr] at hz'
    rw [hRc, Polynomial.eval_map_algebraMap] at hz'
    have h1 : (aeval ((algebraMap ℝ ℂ) z.re)) R = (algebraMap ℝ ℂ) (aeval z.re R) :=
      Polynomial.aeval_algebraMap_apply ℂ z.re R
    rw [Complex.coe_algebraMap] at h1
    rw [h1] at hz'
    have h2 : aeval z.re R = 0 := by
      have := (algebraMap ℝ ℂ).injective (by simpa using hz')
      exact this
    simpa [Polynomial.IsRoot, Polynomial.aeval_def, Polynomial.eval₂_id] using h2
  refine ⟨z.re, z.im, him, ?_⟩
  set q : ℝ[X] := (X - C z.re) ^ 2 + C z.im ^ 2 with hq
  have hqm : q.Monic := by
    have hA : ((X - C z.re) ^ 2 : ℝ[X]).degree = 2 := by
      rw [Polynomial.degree_pow, Polynomial.degree_X_sub_C]; rfl
    have hB : (C z.im ^ 2 : ℝ[X]).degree ≤ 0 := by
      rw [← C_pow]; exact Polynomial.degree_C_le
    refine Polynomial.Monic.add_of_left ((Polynomial.monic_X_sub_C _).pow 2) ?_
    rw [hA]
    exact lt_of_le_of_lt hB (by decide)
  have hdvd : q ∣ R := by
    rw [← Polynomial.modByMonic_eq_zero_iff_dvd hqm]
    have hdecomp : R %ₘ q + q * (R /ₘ q) = R :=
      Polynomial.modByMonic_add_div R q
    have hqdeg : q.natDegree = 2 := by
      have hA : ((X - C z.re) ^ 2 : ℝ[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      have hB : (C z.im ^ 2 : ℝ[X]).natDegree = 0 := by
        rw [← C_pow]; exact Polynomial.natDegree_C _
      rw [hq, Polynomial.natDegree_add_eq_left_of_natDegree_lt
        (by rw [hA, hB]; norm_num), hA]
    have hlt : (R %ₘ q).natDegree < 2 := by
      have := Polynomial.natDegree_modByMonic_lt R hqm (by
        intro h; rw [h] at hqdeg; simp at hqdeg)
      omega
    have hzc : Rc.eval (starRingEnd ℂ z) = 0 := conj_root R z hz'
    have hev : ∀ w : ℂ, Rc.eval w = 0 →
        (q.map (algebraMap ℝ ℂ)).eval w = 0 →
        ((R %ₘ q).map (algebraMap ℝ ℂ)).eval w = 0 := by
      intro w hRw hqw
      have := congrArg (fun P : ℝ[X] => (P.map (algebraMap ℝ ℂ)).eval w) hdecomp
      simp only [Polynomial.map_add, Polynomial.map_mul, eval_add, eval_mul, hqw] at this
      rw [hRc] at hRw
      simpa [hRw] using this
    exact poly_deg_lt_two_zero (R %ₘ q) z him hlt
      (hev z hz' (quad_eval_zero z)) (hev _ hzc (quad_eval_zero_conj z))
  exact hdvd

lemma sum_two_squares_const (R : ℝ[X]) (hR : ∀ x : ℝ, 0 ≤ R.eval x)
    (h0 : R.natDegree = 0) :
    ∃ A B : ℝ[X], R = A ^ 2 + B ^ 2 ∧ A.natDegree = 0 ∧ B.natDegree = 0 := by
  rw [Polynomial.natDegree_eq_zero] at h0
  obtain ⟨c, rfl⟩ := h0
  have hc : 0 ≤ c := by simpa using hR 0
  refine ⟨C (Real.sqrt c), 0, ?_, natDegree_C _, natDegree_zero⟩
  rw [← C_pow, Real.sq_sqrt hc]
  simp

lemma nonneg_of_quad_mul_nonneg (R S : ℝ[X]) (b c : ℝ) (hc : c ≠ 0)
    (hS : R = ((X - C b) ^ 2 + C c ^ 2) * S) (hR : ∀ x : ℝ, 0 ≤ R.eval x) :
    ∀ x : ℝ, 0 ≤ S.eval x := by
  intro x
  have h := hR x
  rw [hS] at h
  simp only [eval_mul, eval_add, eval_pow, eval_sub, eval_X, eval_C] at h
  have hpos : 0 < (x - b) ^ 2 + c ^ 2 := by positivity
  exact nonneg_of_mul_nonneg_right h hpos

lemma brahmagupta_degree (A B : ℝ[X]) (b c : ℝ) (k : ℕ)
    (hA : 2 * A.natDegree ≤ k) (hB : 2 * B.natDegree ≤ k) :
    2 * ((X - C b) * A - C c * B).natDegree ≤ k + 2 ∧
    2 * (C c * A + (X - C b) * B).natDegree ≤ k + 2 := by
  have h1 : ((X - C b) * A).natDegree ≤ A.natDegree + 1 := by
    calc ((X - C b) * A).natDegree ≤ (X - C b).natDegree + A.natDegree :=
          Polynomial.natDegree_mul_le
      _ = A.natDegree + 1 := by rw [Polynomial.natDegree_X_sub_C]; ring
  have h2 : (C c * B).natDegree ≤ B.natDegree := Polynomial.natDegree_C_mul_le c B
  have h3 : (C c * A).natDegree ≤ A.natDegree := Polynomial.natDegree_C_mul_le c A
  have h4 : ((X - C b) * B).natDegree ≤ B.natDegree + 1 := by
    calc ((X - C b) * B).natDegree ≤ (X - C b).natDegree + B.natDegree :=
          Polynomial.natDegree_mul_le
      _ = B.natDegree + 1 := by rw [Polynomial.natDegree_X_sub_C]; ring
  have h5 : ((X - C b) * A - C c * B).natDegree ≤
    max ((X - C b) * A).natDegree (C c * B).natDegree :=
    Polynomial.natDegree_sub_le _ _
  have h6 : (C c * A + (X - C b) * B).natDegree ≤
    max (C c * A).natDegree ((X - C b) * B).natDegree :=
    Polynomial.natDegree_add_le _ _
  constructor
  · rw [max_def] at h5
    split_ifs at h5 <;> omega
  · rw [max_def] at h6
    split_ifs at h6 <;> omega

lemma sum_two_squares_no_real_root (n : ℕ)
    (ih : ∀ m < n, ∀ R : ℝ[X], (∀ x : ℝ, 0 ≤ R.eval x) → R.natDegree = m →
      ∃ A B : ℝ[X], R = A ^ 2 + B ^ 2 ∧ 2 * A.natDegree ≤ m ∧ 2 * B.natDegree ≤ m)
    (R : ℝ[X]) (hR : ∀ x : ℝ, 0 ≤ R.eval x) (hn : R.natDegree = n)
    (hR0 : R ≠ 0) (hroot : ∀ a : ℝ, ¬ R.IsRoot a) :
    ∃ A B : ℝ[X], R = A ^ 2 + B ^ 2 ∧ 2 * A.natDegree ≤ n ∧ 2 * B.natDegree ≤ n := by
  by_cases hdeg : R.natDegree = 0
  · obtain ⟨A, B, h, hA, hB⟩ := sum_two_squares_const R hR hdeg
    exact ⟨A, B, h, by omega, by omega⟩
  · have hpos : 0 < R.natDegree := Nat.pos_of_ne_zero hdeg
    obtain ⟨b, c, hc, S, hS⟩ := exists_quadratic_factor R hpos hroot
    have hS0 : S ≠ 0 := by
      intro h; apply hR0; rw [hS, h, mul_zero]
    have hq_deg : (((X - C b) ^ 2 + C c ^ 2 : ℝ[X])).natDegree = 2 := by
      have hA : ((X - C b) ^ 2 : ℝ[X]).natDegree = 2 := by
        rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
      have hB : ((C c) ^ 2 : ℝ[X]).natDegree = 0 := by
        rw [← C_pow]; exact Polynomial.natDegree_C _
      rw [Polynomial.natDegree_add_eq_left_of_natDegree_lt
        (by rw [hA, hB]; norm_num), hA]
    have hq0 : ((X - C b) ^ 2 + C c ^ 2 : ℝ[X]) ≠ 0 := by
      intro h; rw [h] at hq_deg; simp at hq_deg
    have hdegS : S.natDegree = n - 2 := by
      have := congrArg natDegree hS
      rw [natDegree_mul hq0 hS0, hq_deg] at this
      omega
    have hn2 : 2 ≤ n := by
      have := congrArg natDegree hS
      rw [natDegree_mul hq0 hS0, hq_deg] at this
      omega
    have hSnn := nonneg_of_quad_mul_nonneg R S b c hc hS hR
    have hSnn := nonneg_of_quad_mul_nonneg R S b c hc hS hR
    obtain ⟨A', B', hSAB, hA', hB'⟩ := ih (n - 2) (by omega) S hSnn hdegS
    obtain ⟨hd1, hd2⟩ := brahmagupta_degree A' B' b c (n - 2) hA' hB'
    refine ⟨(X - C b) * A' - C c * B', C c * A' + (X - C b) * B', ?_, ?_, ?_⟩
    · rw [hS, hSAB]; ring
    · omega
    · omega

lemma sum_two_squares_of_nonneg (R : ℝ[X]) (hR : ∀ x : ℝ, 0 ≤ R.eval x) :
    ∃ A B : ℝ[X], R = A ^ 2 + B ^ 2 ∧
      2 * A.natDegree ≤ R.natDegree ∧ 2 * B.natDegree ≤ R.natDegree := by
  have key : ∀ n : ℕ, ∀ R : ℝ[X], (∀ x : ℝ, 0 ≤ R.eval x) → R.natDegree = n →
      ∃ A B : ℝ[X], R = A ^ 2 + B ^ 2 ∧
        2 * A.natDegree ≤ n ∧ 2 * B.natDegree ≤ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro R hR hn
      by_cases hR0 : R = 0
      · exact ⟨0, 0, by simp [hR0], by simp, by simp⟩
      by_cases hroot : ∃ a : ℝ, R.IsRoot a
      · obtain ⟨a, ha⟩ := hroot
        exact sum_two_squares_real_root n ih R hR hn hR0 a ha
      · push Not at hroot
        exact sum_two_squares_no_real_root n ih R hR hn hR0 hroot
  obtain ⟨A, B, h, hA, hB⟩ := key R.natDegree R hR rfl
  exact ⟨A, B, h, hA, hB⟩

lemma even_mult_of_odd_roots_prod (prod : ℝ[X]) (hprod : prod.Monic) (a : ℝ) :
    Even (rootMultiplicity a ((∏ x ∈ prod.roots.toFinset.filter
      (fun x => Odd (prod.roots.count x)), (X - C x)) * prod)) := by
  classical
  set T : Finset ℝ := prod.roots.toFinset.filter (fun x => Odd (prod.roots.count x)) with hT
  set Q : ℝ[X] := ∏ x ∈ T, (X - C x) with hQ
  have hQm : Q.Monic := monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)
  have hQ0 : Q ≠ 0 := hQm.ne_zero
  have hp0 : prod ≠ 0 := hprod.ne_zero
  have hmul : rootMultiplicity a (Q * prod) = rootMultiplicity a Q + rootMultiplicity a prod :=
    Polynomial.rootMultiplicity_mul (mul_ne_zero hQ0 hp0)
  have hcount : prod.roots.count a = rootMultiplicity a prod :=
    Polynomial.count_roots prod
  rw [hmul, ← hcount]
  have hQmult : rootMultiplicity a Q = if a ∈ T then 1 else 0 := by
    rw [← Polynomial.count_roots, hQ, Polynomial.roots_prod_X_sub_C]
    by_cases ha : a ∈ T
    · simp [ha, Multiset.count_eq_one_of_mem T.nodup ha]
    · simp [ha]
  rw [hQmult]
  by_cases ha : a ∈ T
  · rw [ite_eq_left ha]
    have hodd : Odd (prod.roots.count a) := (Finset.mem_filter.mp ha).2
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k + 1, by omega⟩
  · rw [ite_eq_right ha, zero_add]
    by_cases hmem : a ∈ prod.roots.toFinset
    · have hnodd : ¬ Odd (prod.roots.count a) := fun h =>
        ha (Finset.mem_filter.mpr ⟨hmem, h⟩)
      rw [Nat.not_odd_iff_even] at hnodd
      exact hnodd
    · have h0 : prod.roots.count a = 0 :=
        Multiset.count_eq_zero.mpr (fun h => hmem (Multiset.mem_toFinset.mpr h))
      rw [h0]; exact ⟨0, rfl⟩

lemma nonneg_of_even_mult_aux (n : ℕ) :
    ∀ P : ℝ[X], P.Monic → (∀ a : ℝ, Even (P.rootMultiplicity a)) →
      P.natDegree = n → ∀ x : ℝ, 0 ≤ P.eval x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P hP h hn
    by_cases hroot : ∃ a : ℝ, P.IsRoot a
    · obtain ⟨a, ha⟩ := hroot
      have hP0 : P ≠ 0 := hP.ne_zero
      have hpos : 0 < P.rootMultiplicity a := (Polynomial.rootMultiplicity_pos hP0).mpr ha
      obtain ⟨j, hj⟩ := h a
      have hdvd : (X - C a) ^ 2 ∣ P :=
        dvd_trans (pow_dvd_pow _ (by omega)) (Polynomial.pow_rootMultiplicity_dvd P a)
      obtain ⟨S, hS⟩ := hdvd
      have hSm : S.Monic := by
        have hm : ((X - C a) ^ 2 * S).Monic := hS ▸ hP
        exact Polynomial.Monic.of_mul_monic_left ((monic_X_sub_C a).pow 2) hm
      have hX2 : (X - C a) ^ 2 ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero a)
      have hSmult : ∀ b : ℝ, Even (S.rootMultiplicity b) := by
        intro b
        have hmul : P.rootMultiplicity b =
            ((X - C a) ^ 2).rootMultiplicity b + S.rootMultiplicity b := by
          rw [hS]
          exact Polynomial.rootMultiplicity_mul (mul_ne_zero hX2 hSm.ne_zero)
        have hm2 : ((X - C a) ^ 2).rootMultiplicity b = if b = a then 2 else 0 := by
          by_cases hba : b = a
          · subst hba
            rw [ite_eq_left rfl]
            have hsq : (X - C b) ^ 2 = (X - C b) * (X - C b) := sq _
            rw [hsq, Polynomial.rootMultiplicity_mul
              (mul_ne_zero (X_sub_C_ne_zero b) (X_sub_C_ne_zero b)),
              Polynomial.rootMultiplicity_X_sub_C_self]
          · rw [ite_eq_right hba]
            apply Polynomial.rootMultiplicity_eq_zero
            simp [sub_eq_zero, hba]
        obtain ⟨u, hu⟩ := h b
        by_cases hba : b = a
        · rw [ite_eq_left hba] at hm2
          exact ⟨u - 1, by omega⟩
        · rw [ite_eq_right hba] at hm2
          exact ⟨u, by omega⟩
      have hdegS : S.natDegree < n := by
        have := congrArg natDegree hS
        rw [natDegree_mul hX2 hSm.ne_zero, natDegree_pow, natDegree_X_sub_C] at this
        omega
      have hSnn := ih S.natDegree hdegS S hSm hSmult rfl
      intro x
      rw [hS, eval_mul, eval_pow]
      simp only [eval_sub, eval_X, eval_C]
      exact mul_nonneg (sq_nonneg _) (hSnn x)
    · push Not at hroot
      intro x
      by_contra hneg
      push Not at hneg
      have hdeg : 0 < P.degree := by
        by_contra hd
        push Not at hd
        have h1 : P = 1 := Polynomial.eq_one_of_monic_natDegree_zero hP
          (natDegree_eq_zero_iff_degree_le_zero.mpr hd)
        rw [h1] at hneg
        simp at hneg
        linarith
      have htend := Polynomial.tendsto_atTop_of_leadingCoeff_nonneg P hdeg
        (by rw [hP.leadingCoeff]; norm_num)
      obtain ⟨y, hy1, hy2⟩ := ((htend.eventually (Filter.eventually_gt_atTop 0)).and
        (Filter.eventually_ge_atTop x)).exists
      obtain ⟨c, _, hc⟩ := intermediate_value_Icc hy2
        P.continuous.continuousOn ⟨hneg.le, hy1.le⟩
      exact hroot c hc

lemma nonneg_of_even_mult (P : ℝ[X]) (hP : P.Monic)
    (h : ∀ a : ℝ, Even (P.rootMultiplicity a)) : ∀ x : ℝ, 0 ≤ P.eval x :=
  nonneg_of_even_mult_aux P.natDegree P hP h rfl

lemma nonneg_of_odd_roots_prod (prod : ℝ[X]) (hprod : prod.Monic) :
    ∃ Q : ℝ[X], Q.Monic ∧
      Q.natDegree = (prod.roots.toFinset.filter
        (fun x => Odd (prod.roots.count x))).card ∧
      ∀ x : ℝ, 0 ≤ (Q * prod).eval x := by
  classical
  refine ⟨∏ x ∈ prod.roots.toFinset.filter (fun x => Odd (prod.roots.count x)),
    (X - C x), ?_, ?_, ?_⟩
  · exact monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)
  · rw [natDegree_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)]
    simp
  · have hQm : (∏ x ∈ prod.roots.toFinset.filter (fun x => Odd (prod.roots.count x)),
        (X - C x)).Monic :=
      monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)
    exact nonneg_of_even_mult _ (hQm.mul hprod)
      (fun a => even_mult_of_odd_roots_prod prod hprod a)

lemma L_sq_nonneg (w : Fin d → ℂ) (m : Fin d → ℕ) (hd : 0 < d)
    (hH : (hankel w m).PosDef) (P : ℝ[X]) (hP : P.natDegree ≤ d - 1) :
    0 ≤ L w m (P ^ 2) := by
  by_cases hP0 : P = 0
  · subst hP0
    simp
  · exact le_of_lt (L_sq_pos w hd hH P hP0 hP)

lemma coeff_sq_two_mul {P : ℝ[X]} {k : ℕ} (hP : P.natDegree ≤ k) :
    (P ^ 2).coeff (2 * k) = (P.coeff k) ^ 2 := by
  have h := Polynomial.coeff_pow_of_natDegree_le
    (p := P) (n := k) (m := 2) hP
  exact h

lemma natDegree_le_of_sq_add_sq {A B : ℝ[X]} {n : ℕ}
    (h : (A ^ 2 + B ^ 2).natDegree ≤ n) :
    2 * A.natDegree ≤ n ∧ 2 * B.natDegree ≤ n := by
  by_cases hA : A = 0
  · subst hA
    by_cases hB : B = 0
    · subst hB
      simp
    · have : (B ^ 2).natDegree = 2 * B.natDegree := by
        rw [Polynomial.natDegree_pow]
      simp at h
      refine ⟨by simp, ?_⟩
      omega
  by_cases hB : B = 0
  · subst hB
    have : (A ^ 2).natDegree = 2 * A.natDegree := by
      rw [Polynomial.natDegree_pow]
    simp at h
    refine ⟨by omega, by simp⟩
  set k := max A.natDegree B.natDegree with hk
  have hAk : A.natDegree ≤ k := le_max_left _ _
  have hBk : B.natDegree ≤ k := le_max_right _ _
  have hcoeff : (A ^ 2 + B ^ 2).coeff (2 * k) = (A.coeff k) ^ 2 + (B.coeff k) ^ 2 := by
    rw [Polynomial.coeff_add, coeff_sq_two_mul hAk, coeff_sq_two_mul hBk]
  have hpos : 0 < (A.coeff k) ^ 2 + (B.coeff k) ^ 2 := by
    rcases le_total A.natDegree B.natDegree with hle | hle
    · have hkB : k = B.natDegree := by rw [hk]; exact max_eq_right hle
      have hBc : B.coeff k ≠ 0 := by
        rw [hkB]; exact Polynomial.leadingCoeff_ne_zero.mpr hB
      have := sq_pos_of_ne_zero hBc
      positivity
    · have hkA : k = A.natDegree := by rw [hk]; exact max_eq_left hle
      have hAc : A.coeff k ≠ 0 := by
        rw [hkA]; exact Polynomial.leadingCoeff_ne_zero.mpr hA
      have := sq_pos_of_ne_zero hAc
      positivity
  have hne : (A ^ 2 + B ^ 2).coeff (2 * k) ≠ 0 := by
    rw [hcoeff]; exact ne_of_gt hpos
  have h2k : 2 * k ≤ (A ^ 2 + B ^ 2).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hne
  have hk2 : 2 * k ≤ n := le_trans h2k h
  constructor <;> omega

lemma exists_sq_add_sq_of_nonneg (P : ℝ[X]) (hP : ∀ x : ℝ, 0 ≤ P.eval x) :
    ∃ A B : ℝ[X], P = A ^ 2 + B ^ 2 := by
  obtain ⟨A, B, hAB, -, -⟩ := sum_two_squares_of_nonneg P hP
  exact ⟨A, B, hAB⟩

lemma roots_real_simple (w : Fin d → ℂ) (m : Fin d → ℕ) (hd : 0 < d)
    (hH : (hankel w m).PosDef) (prod : ℝ[X])
    (hmon : prod.Monic) (hdeg : prod.natDegree = d)
    (horth : ∀ Q : ℝ[X], Q.natDegree ≤ d - 1 → L w m (Q * prod) = 0) :
    prod.roots.Nodup ∧ prod.roots.card = d := by
  classical
  set T : Finset ℝ := prod.roots.toFinset.filter (fun x => Odd (prod.roots.count x)) with hT
  obtain ⟨Q, hQm, hQdeg, hQnn⟩ := nonneg_of_odd_roots_prod prod hmon
  have hQdeg' : Q.natDegree = T.card := hQdeg
  have hTcard : T.card ≤ d := by
    calc T.card ≤ prod.roots.toFinset.card := Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ Multiset.card prod.roots := Multiset.toFinset_card_le _
      _ ≤ prod.natDegree := Polynomial.card_roots' prod
      _ = d := hdeg
  have hTlt : ¬ (T.card ≤ d - 1) := by
    intro hle
    have h0 : L w m (Q * prod) = 0 := horth Q (by rw [hQdeg']; exact hle)
    have hQp0 : Q * prod ≠ 0 := (hQm.mul hmon).ne_zero
    have hdegQP : (Q * prod).natDegree ≤ 2 * d - 1 := by
      rw [hQm.natDegree_mul hmon, hQdeg', hdeg]
      omega
    have hpos : 0 < L w m (Q * prod) := by
      obtain ⟨A, B, hAB⟩ := exists_sq_add_sq_of_nonneg (Q * prod) hQnn
      have hdeg2 : (A ^ 2 + B ^ 2).natDegree ≤ 2 * d - 1 := hAB ▸ hdegQP
      obtain ⟨hA2, hB2⟩ := natDegree_le_of_sq_add_sq hdeg2
      have hAdeg : A.natDegree ≤ d - 1 := by omega
      have hBdeg : B.natDegree ≤ d - 1 := by omega
      have hAB0 : A ≠ 0 ∨ B ≠ 0 := by
        by_contra h
        push Not at h
        apply hQp0
        rw [hAB, h.1, h.2]; simp
      rw [hAB, map_add]
      rcases hAB0 with hA | hB
      · have h1 := L_sq_pos w hd hH A hA hAdeg
        have h2 := L_sq_nonneg w m hd hH B hBdeg
        linarith
      · have h1 := L_sq_pos w hd hH B hB hBdeg
        have h2 := L_sq_nonneg w m hd hH A hAdeg
        linarith
    exact absurd h0 (ne_of_gt hpos)
  have hTd : T.card = d := by omega
  have h1 : T.card ≤ prod.roots.toFinset.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have h2 : prod.roots.toFinset.card ≤ Multiset.card prod.roots :=
    Multiset.toFinset_card_le _
  have h3 : Multiset.card prod.roots ≤ prod.natDegree := Polynomial.card_roots' prod
  have hcard : Multiset.card prod.roots = d := by omega
  refine ⟨?_, hcard⟩
  rw [← Multiset.toFinset_card_eq_card_iff_nodup]
  omega

lemma eq_prod_of_roots (prod : ℝ[X]) (hmon : prod.Monic) (hdeg : prod.natDegree = d)
    (hnd : prod.roots.Nodup) (hcard : prod.roots.card = d) :
    ∃ ξ : Fin d → ℝ, Function.Injective ξ ∧ prod = ∏ k, (X - C (ξ k)) := by
  have hprod : prod = (prod.roots.map fun a => X - C a).prod :=
    (prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by rw [hcard, hdeg])).symm
  set S : Finset ℝ := prod.roots.toFinset with hS
  have hScard : S.card = d := by
    rw [hS, Multiset.toFinset_card_of_nodup hnd, hcard]
  let e : Fin d ≃o S := S.orderIsoOfFin hScard
  refine ⟨fun k => (e k : ℝ), ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · have hval : prod.roots = S.val := by
      rw [hS, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
    conv_lhs => rw [hprod, hval]
    rw [← Finset.prod_eq_multiset_prod,
        ← Finset.prod_coe_sort S (fun a => X - C a)]
    exact (Equiv.prod_comp e.toEquiv (fun x : S => X - C (x : ℝ))).symm

lemma orthogonal_sum_identity (w : Fin d → ℂ) (m : Fin d → ℕ)
    (hreal : ∀ k ≤ 2 * d - 2, (nu w m k).im = 0)
    (hreal1 : (nu w m (2 * d - 1)).im = 0)
    (prod : ℝ[X]) (horth : ∀ Q : ℝ[X], Q.natDegree ≤ d - 1 → L w m (Q * prod) = 0)
    (hdeg : prod.natDegree = d) (p : ℕ) (hp : p ≤ d - 1) :
    ∑ j, (m j : ℂ) * (prod.map (algebraMap ℝ ℂ)).eval (w j) * w j ^ p = 0 := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp
  rcases Nat.lt_or_ge p (d - 1) with hlt | hge
  · have hQ : ((X : ℝ[X]) ^ p).natDegree ≤ d - 1 := by
      rw [natDegree_X_pow]; exact hp
    have hdegP : ((X : ℝ[X]) ^ p * prod).natDegree ≤ 2 * d - 2 := by
      refine (natDegree_mul_le).trans ?_
      rw [natDegree_X_pow, hdeg]
      omega
    have h := L_eq_sum w m hreal ((X : ℝ[X]) ^ p * prod) hdegP
    rw [horth _ hQ] at h
    simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X] at h
    rw [Complex.ofReal_zero] at h
    rw [h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  · have hpd : p = d - 1 := le_antisymm hp hge
    subst hpd
    set P : ℝ[X] := (X : ℝ[X]) ^ (d - 1) * prod with hP
    have hQ : ((X : ℝ[X]) ^ (d - 1)).natDegree ≤ d - 1 := by
      rw [natDegree_X_pow]
    have hL0 : L w m P = 0 := horth _ hQ
    set a : ℝ := prod.leadingCoeff with ha
    set R : ℝ[X] := P - C a * (X : ℝ[X]) ^ (2 * d - 1) with hR
    have hPdeg : P.natDegree ≤ 2 * d - 1 := by
      refine (natDegree_mul_le).trans ?_
      rw [natDegree_X_pow, hdeg]
      omega
    have hRdeg : R.natDegree ≤ 2 * d - 2 := by
      have hPd : P.natDegree ≤ 2 * d - 1 := hPdeg
      have hcoefP : P.coeff (2 * d - 1) = a := by
        have h1 : P.coeff (d - 1 + d) = (X ^ (d - 1) : ℝ[X]).coeff (d - 1) * prod.coeff d := by
          rw [hP]
          exact coeff_X_pow_mul' _ _ _ |>.trans (by simp)
        have h2 : d - 1 + d = 2 * d - 1 := by omega
        rw [← h2, h1, coeff_X_pow_self, one_mul, ha, leadingCoeff, hdeg]
      refine natDegree_le_iff_coeff_eq_zero.mpr ?_
      intro k hk
      rw [hR, coeff_sub, coeff_C_mul, coeff_X_pow]
      by_cases hk1 : k = 2 * d - 1
      · subst hk1
        rw [hcoefP]; simp
      · have hk2 : 2 * d - 1 < k := by omega
        have hPk : P.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
        rw [hPk, ite_eq_right hk1]; simp
    have hLR := L_eq_sum w m hreal R hRdeg
    have hLX : L w m (C a * (X : ℝ[X]) ^ (2 * d - 1)) = a * nuR w m (2 * d - 1) := by
      rw [C_mul_X_pow_eq_monomial]
      simp [L, Polynomial.lsum_apply, Polynomial.sum_monomial_index,
        smul_eq_mul, mul_comm]
    have hPR : P = R + C a * (X : ℝ[X]) ^ (2 * d - 1) := by
      rw [hR]; ring
    have hLsplit : L w m P = L w m R + a * nuR w m (2 * d - 1) := by
      rw [hPR, map_add, hLX]
    have hnuC : ((nuR w m (2 * d - 1) : ℝ) : ℂ) = nu w m (2 * d - 1) := by
      apply Complex.ext
      · simp [nuR]
      · simp [hreal1]
    have hsumP : ∑ j, (m j : ℂ) * eval (w j) (Polynomial.map (algebraMap ℝ ℂ) prod) * w j ^ (d - 1)
        = ∑ j, (m j : ℂ) * eval (w j) (Polynomial.map (algebraMap ℝ ℂ) P) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hP]
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
      ring
    have hevalP : ∀ j, eval (w j) (Polynomial.map (algebraMap ℝ ℂ) P)
        = eval (w j) (Polynomial.map (algebraMap ℝ ℂ) R) + (a : ℂ) * w j ^ (2 * d - 1) := by
      intro j
      rw [hPR]
      simp
    rw [hsumP]
    simp only [hevalP, mul_add, Finset.sum_add_distrib]
    rw [← hLR]
    have hνterm : ∑ j, (m j : ℂ) * ((a : ℂ) * w j ^ (2 * d - 1))
        = (a : ℂ) * nu w m (2 * d - 1) := by
      simp only [nu, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hνterm, ← hnuC]
    have hL0' : ((L w m P : ℝ) : ℂ) = 0 := by rw [hL0]; simp
    rw [hLsplit] at hL0'
    push_cast at hL0'
    exact hL0'

lemma vandermonde_det_ne_zero (w : Fin d → ℂ) (hw : Function.Injective w) :
    (Matrix.vandermonde w).det ≠ 0 := by
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact hw

lemma eval_zero_of_orthogonal (w : Fin d → ℂ) (m : Fin d → ℕ)
    (hw : Function.Injective w) (hm : ∀ j, 0 < m j) (prod : ℝ[X])
    (hsum : ∀ p ≤ d - 1,
      ∑ j, (m j : ℂ) * (prod.map (algebraMap ℝ ℂ)).eval (w j) * w j ^ p = 0) :
    ∀ j, (prod.map (algebraMap ℝ ℂ)).eval (w j) = 0 := by
  set u : Fin d → ℂ := fun j => (m j : ℂ) * (prod.map (algebraMap ℝ ℂ)).eval (w j) with hu
  have hVu : (Matrix.vandermonde w).transpose.mulVec u = 0 := by
    funext i
    have hi : (i : ℕ) ≤ d - 1 := by omega
    have h := hsum i hi
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.vandermonde_apply, hu, Pi.zero_apply]
    rw [← h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hdet : (Matrix.vandermonde w).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact vandermonde_det_ne_zero w hw
  have hu0 : u = 0 := by
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hVu
    exact this
  intro j
  have hj : u j = 0 := by rw [hu0]; rfl
  simp only [hu] at hj
  rcases mul_eq_zero.mp hj with h | h
  · exfalso
    have : m j = 0 := by exact_mod_cast h
    exact (hm j).ne' this
  · exact h


lemma node_real_of_root (w : Fin d → ℂ) (ξ : Fin d → ℝ) (prod : ℝ[X])
    (hprod : prod = ∏ k, (X - C (ξ k)))
    (hroot : ∀ j, (prod.map (algebraMap ℝ ℂ)).eval (w j) = 0) :
    ∀ j, (w j).im = 0 := by
  intro j
  have h := hroot j
  rw [hprod, Polynomial.map_prod, Polynomial.eval_prod] at h
  obtain ⟨k, _, hk⟩ := Finset.prod_eq_zero_iff.mp h
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hk
  have hwk : w j = (ξ k : ℂ) := by
    have := sub_eq_zero.mp hk
    simpa using this
  rw [hwk]
  exact Complex.ofReal_im _

theorem reciproque_aligned_imp_hankel (a : ℂ) (θ : ℝ) (z : Fin d → ℂ) (m : Fin d → ℕ)
    (hz : Function.Injective z) (hm : ∀ j, 0 < m j) (hd : 0 < d)
    (hreal : ∀ k ≤ 2 * d - 1,
      (nu (fun j => Complex.exp (-(θ * Complex.I)) * (z j - a)) m k).im = 0)
    (hpos : (hankel (fun j => Complex.exp (-(θ * Complex.I)) * (z j - a)) m).PosDef) :
    ∀ j, ∃ x : ℝ, z j = a + Complex.exp (θ * Complex.I) * x := by
  set w : Fin d → ℂ := fun j => Complex.exp (-(θ * Complex.I)) * (z j - a) with hw_def
  have hw : Function.Injective w := by
    intro i j hij
    have hne : Complex.exp (-(θ * Complex.I)) ≠ 0 := Complex.exp_ne_zero _
    have h1 : z i - a = z j - a := mul_left_cancel₀ hne hij
    exact hz (sub_left_injective h1)
  have hreal1 : (nu w m (2 * d - 1)).im = 0 := hreal (2 * d - 1) le_rfl
  have hreal0 : ∀ k ≤ 2 * d - 2, (nu w m k).im = 0 :=
    fun k hk => hreal k (by omega)
  obtain ⟨prod, hmon, hdeg, hnd, hcard, horth⟩ :
      ∃ prod : ℝ[X], prod.Monic ∧ prod.natDegree = d ∧ prod.roots.Nodup ∧
        prod.roots.card = d ∧
        ∀ Q : ℝ[X], Q.natDegree ≤ d - 1 → L w m (Q * prod) = 0 := by
    obtain ⟨prod, hmon, hdeg, horth⟩ := exists_orthogonal_monic' w m hd hpos
    obtain ⟨hnd, hcard⟩ := roots_real_simple w m hd hpos prod hmon hdeg horth
    exact ⟨prod, hmon, hdeg, hnd, hcard, horth⟩
  obtain ⟨ξ, _, hprod⟩ := eq_prod_of_roots prod hmon hdeg hnd hcard
  have hsum : ∀ p ≤ d - 1,
      ∑ j, (m j : ℂ) * (prod.map (algebraMap ℝ ℂ)).eval (w j) * w j ^ p = 0 :=
    fun p hp => orthogonal_sum_identity w m hreal0 hreal1 prod horth hdeg p hp
  have hroot : ∀ j, (prod.map (algebraMap ℝ ℂ)).eval (w j) = 0 :=
    eval_zero_of_orthogonal w m hw hm prod hsum
  have him : ∀ j, (w j).im = 0 := node_real_of_root w ξ prod hprod hroot
  intro j
  refine ⟨(w j).re, ?_⟩
  have hwj : w j = ((w j).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him j]
  have hexp : Complex.exp (θ * Complex.I) * Complex.exp (-(θ * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have hwdef : w j = Complex.exp (-(θ * Complex.I)) * (z j - a) := rfl
  calc z j = a + Complex.exp (θ * Complex.I) * (Complex.exp (-(θ * Complex.I)) * (z j - a)) := by
        rw [← mul_assoc, hexp, one_mul]; ring
    _ = a + Complex.exp (θ * Complex.I) * w j := by rw [hwdef]
    _ = a + Complex.exp (θ * Complex.I) * ((w j).re : ℂ) := by rw [← hwj]

lemma posDef_of_hankelR {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) (a : ℂ) (θ : ℝ)
    (hreal : ∀ k ≤ 2 * d - 2, (nuMoment z m a θ k).im = 0)
    (hminors : ∀ r : ℕ, 1 ≤ r → r ≤ d →
      0 < (HankelR z m a θ r).det.re ∧ (HankelR z m a θ r).det.im = 0) :
    (hankel (fun j => Complex.exp (-(θ * Complex.I)) * (z j - a)) m).PosDef := by
  set w : Fin d → ℂ := fun j => Complex.exp (-(θ * Complex.I)) * (z j - a) with hw
  apply posDef_of_leading_minors
  · ext p q
    simp [Matrix.transpose_apply, hankel, add_comm]
  · intro r hr
    rcases Nat.eq_zero_or_pos r with h0 | hr1
    · subst h0
      simp
    · have hcoe : ((hankel w m).submatrix (Fin.castLE hr) (Fin.castLE hr)).map
            (algebraMap ℝ ℂ) = HankelR z m a θ r := by
        ext p q
        have hk : (p : ℕ) + q ≤ 2 * d - 2 := by
          have := p.isLt; have := q.isLt; omega
        have him := hreal _ hk
        simp only [Matrix.map_apply, Matrix.submatrix_apply, hankel, Matrix.of_apply,
          Fin.val_castLE, HankelR, nuR]
        apply Complex.ext
        · simp [nuMoment, nu, hw] at him ⊢
        · simp [nuMoment, nu, hw] at him ⊢
          simp_all
      obtain ⟨hre, him⟩ := hminors r hr1 hr
      have hdet : (algebraMap ℝ ℂ) ((hankel w m).submatrix (Fin.castLE hr) (Fin.castLE hr)).det
          = (HankelR z m a θ r).det := by
        rw [← hcoe, RingHom.map_det]
        rfl
      rw [← hdet] at hre
      simpa using hre


-------------------------------------------------------------------
-- conclusion

lemma aligned_imp_hankel {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ)
    (hz : Function.Injective z) (hm : ∀ j, 0 < m j) :
    Aligned z → HankelCriterion z m := by
  rintro ⟨a, θ, hal⟩
  obtain ⟨x, hx⟩ := exists_real_wNode z a θ hal
  refine ⟨a, θ, ?_, ?_⟩
  · intro k _
    rw [nuMoment_eq_ofReal z m a θ x hx k]
    exact Complex.ofReal_im _
  · intro r _ hr
    rw [HankelR_eq_map z m a θ x hx r, det_map_ofReal]
    have hx_inj : Function.Injective x := by
      intro i j hij
      apply hz
      have hi := hx i
      have hj := hx j
      unfold wNode at hi hj
      have hexp : Complex.exp (-(θ * Complex.I)) ≠ 0 := Complex.exp_ne_zero _
      have : z i - a = z j - a := by
        apply mul_left_cancel₀ hexp
        rw [hi, hj, hij]
      exact sub_left_inj.mp this
    have hpos := (HankelRR_posDef x m hm hx_inj hr).det_pos
    exact ⟨by simpa using hpos, Complex.ofReal_im _⟩

theorem hankel_imp_aligned {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ)
    (hz : Function.Injective z) (hm : ∀ j, 0 < m j) :
    HankelCriterion z m → Aligned z := by
  rintro ⟨a, θ, hreal, hminors⟩
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨a, θ, fun j => j.elim0⟩
  refine ⟨a, θ, ?_⟩
  have hpos : (hankel (fun j => Complex.exp (-(θ * Complex.I)) * (z j - a)) m).PosDef :=
    posDef_of_hankelR z m a θ (fun k hk => hreal k (by omega)) hminors
  have hreal' : ∀ k ≤ 2 * d - 1,
      (nu (fun j => Complex.exp (-(θ * Complex.I)) * (z j - a)) m k).im = 0 := by
    intro k hk
    simpa [nuMoment, nu] using hreal k hk
  exact reciproque_aligned_imp_hankel a θ z m hz hm hd hreal' hpos


theorem alignement_zeros_hankel {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ)
    (hz : Function.Injective z) (hm : ∀ j, 0 < m j) :
    Aligned z ↔ HankelCriterion z m :=
  ⟨aligned_imp_hankel z m hz hm, hankel_imp_aligned z m hz hm⟩






end CritColi
