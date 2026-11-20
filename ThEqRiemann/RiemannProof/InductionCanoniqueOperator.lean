import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.SchurPassageMatrix
import ThEqRiemann.RiemannProof.SchurMatrixInverse

/-! -/
namespace InductionCanoniqueOp


open Set Complex
open RiemannDef
open scoped ComplexOrder

lemma mom_eq_sum_pow {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (hSimple : ∀ i : Fin D, mult i = 1) (n : ℕ) (hn : n ≤ D) (k : ℕ) :
    mom γ mult n hn k = ∑ i : Fin n, γ (Fin.castLE hn i) ^ k := by
  unfold mom
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hSimple, Nat.cast_one, one_mul]

lemma gamma_eq_mom_sub_sum {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (hSimple : ∀ i : Fin D, mult i = 1) (p : ℕ) (hp : p + 1 ≤ D) :
    γ ⟨p, by omega⟩ = mom γ mult (p + 1) hp 1
      - ∑ i : Fin p, γ (Fin.castLE (by omega) i) := by
  rw [mom_eq_sum_pow γ mult hSimple]
  simp only [pow_one]
  rw [Fin.sum_univ_castSucc]
  have h1 : Fin.castLE hp (Fin.last p) = (⟨p, by omega⟩ : Fin D) := by ext; simp
  have h2 : ∀ i : Fin p, Fin.castLE hp (Fin.castSucc i)
      = Fin.castLE (by omega : p ≤ D) i := by intro i; ext; simp
  simp only [h1, h2]
  ring


lemma hankelN_succ_eq_fromBlocks {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) :
    hankelN γ mult (p + 1) hp =
      Matrix.of fun i j : Fin (p + 1) => mom γ mult (p + 1) hp (i.val + j.val) := rfl

lemma det_hankelN_eq_prod {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (hSimple : ∀ i : Fin D, mult i = 1) (n : ℕ) (hn : n ≤ D) :
    (hankelN γ mult n hn).det =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (γ (Fin.castLE hn j) - γ (Fin.castLE hn i)) ^ 2 := by
  have hV : hankelN γ mult n hn =
      (Matrix.vandermonde (fun i : Fin n => γ (Fin.castLE hn i))).transpose *
      Matrix.vandermonde (fun i : Fin n => γ (Fin.castLE hn i)) := by
    ext i j
    simp [hankelN, Matrix.mul_apply, Matrix.vandermonde,
      mom_eq_sum_pow γ mult hSimple, pow_add]
  rw [hV, Matrix.det_mul, Matrix.det_transpose, Matrix.det_vandermonde, ← sq,
    ← Finset.prod_pow]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Finset.prod_pow]

lemma versFin_det {p : ℕ} (M : Matrix (Fin p ⊕ Fin 1) (Fin p ⊕ Fin 1) ℂ) :
    (versFin M).det = M.det := by
  unfold versFin
  exact Matrix.det_submatrix_equiv_self _ _



open SchurPassage in
lemma hankelN_succ_eq_versFin {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) :
    hankelN γ mult (p + 1) hp =
      versFin (Matrix.fromBlocks (coinHankel γ mult p hp) (hVec γ mult p hp)
        (hVec γ mult p hp).transpose (scal (mom γ mult (p + 1) hp (2 * p)))) := by
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · simp only [versFin_fromBlocks_22, hankelN, scal, Matrix.of_apply,
      Fin.val_last]
    congr 1; omega
  · simp only [versFin_fromBlocks_21, hankelN, hVec, Matrix.of_apply,
      Fin.val_last, Fin.val_castSucc]
    congr 1
  · simp only [versFin_fromBlocks_12, hankelN, hVec, Matrix.of_apply,
      Fin.val_last, Fin.val_castSucc]
    congr 1; omega
  · simp only [versFin_fromBlocks_11, hankelN, coinHankel, Matrix.of_apply,
      Fin.val_castSucc]

open SchurInverse in
lemma schurN_eq_det_div {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) (hinv : IsUnit (coinHankel γ mult p hp).det) :
    schurN γ mult p hp
      = (hankelN γ mult (p + 1) hp).det / (coinHankel γ mult p hp).det := by
  have hdet : (hankelN γ mult (p + 1) hp).det
      = (coinHankel γ mult p hp).det * schurN γ mult p hp := by
    rw [hankelN_succ_eq_versFin, versFin_det]
    rw [show Matrix.fromBlocks (coinHankel γ mult p hp) (hVec γ mult p hp)
          (hVec γ mult p hp).transpose (scal (mom γ mult (p + 1) hp (2 * p)))
        = blockMatrix (coinHankel γ mult p hp) (hVec γ mult p hp)
          (hVec γ mult p hp).transpose (scal (mom γ mult (p + 1) hp (2 * p))) from rfl]
    rw [det_blockMatrix_eq _ _ _ _ hinv]
    congr 1
    simp [schurN, scal, Matrix.det_unique]
  rw [hdet, mul_div_cancel_left₀ _ hinv.ne_zero]

lemma coinHankel_posDef {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) (hpos : (hankelN γ mult (p + 1) hp).PosDef) :
    (coinHankel γ mult p hp).PosDef := by
  have hinj : Function.Injective (Fin.castSucc : Fin p → Fin (p + 1)) :=
    Fin.castSucc_injective p
  have h := hpos.submatrix hinj
  convert h using 1
  ext i j
  simp [coinHankel, hankelN, Matrix.submatrix]

lemma coinHankel_isUnit_det {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (p : ℕ) (hp : p + 1 ≤ D) (hpos : (hankelN γ mult (p + 1) hp).PosDef) :
    IsUnit (coinHankel γ mult p hp).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (coinHankel_posDef γ mult p hp hpos).isUnit

theorem construction_operateurs_TN_zeros_partiel
    (D : ℕ) (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (hDef : ∀ (n : ℕ) (hnD : n ≤ D), 1 ≤ n → (hankelN γ mult n hnD).PosDef)
    (hReel : ∀ i : Fin D, (γ i).im = 0)
    (hSimple : ∀ i : Fin D, mult i = 1)
    (hDistinct : Function.Injective γ) :
    ∀ (n : ℕ) (hnD : n ≤ D), 1 ≤ n →
      (∀ i : Fin n, (γ (Fin.castLE hnD i)).im = 0) ∧
      (∀ i : Fin n, mult (Fin.castLE hnD i) = 1) ∧
      (∀ i j : Fin n, i ≠ j → γ (Fin.castLE hnD i) ≠ γ (Fin.castLE hnD j)) ∧
      (∀ (p : ℕ) (hp : p + 1 ≤ D), n = p + 1 →
        (γ ⟨p, by omega⟩ = mom γ mult (p + 1) hp 1
          - ∑ i : Fin p, γ (Fin.castLE (by omega) i)) ∧
        (schurN γ mult p hp
          = (hankelN γ mult (p + 1) hp).det / (coinHankel γ mult p hp).det)) := by
  intro n hnD _
  refine ⟨fun i => hReel _, fun i => hSimple _, ?_, ?_⟩
  · intro i j hij h
    exact hij (Fin.ext (by simpa using congrArg Fin.val (hDistinct h)))
  · intro p hp _
    exact ⟨gamma_eq_mom_sub_sum γ mult hSimple p hp,
      schurN_eq_det_div γ mult p hp
        (coinHankel_isUnit_det γ mult p hp (hDef (p + 1) hp (by omega)))⟩

lemma det_posDef_re_pos {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.PosDef) :
    0 < M.det.re ∧ M.det.im = 0 := by
  have h : (0 : ℂ) < M.det := hM.det_pos
  exact ⟨(Complex.pos_iff.mp h).1, ((Complex.pos_iff.mp h).2).symm⟩

lemma det_hankelN_succ {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (hSimple : ∀ i : Fin D, mult i = 1) (p : ℕ) (hp : p + 1 ≤ D) :
    (hankelN γ mult (p + 1) hp).det =
      (hankelN γ mult p (by omega)).det *
        ∏ i : Fin p, (γ ⟨p, by omega⟩ - γ (Fin.castLE (by omega) i)) ^ 2 := by
  rw [det_hankelN_eq_prod γ mult hSimple (p+1) hp,
      det_hankelN_eq_prod γ mult hSimple p (by omega)]
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ j ∈ Finset.Ioi (Fin.last p),
      (γ (Fin.castLE hp j) - γ (Fin.castLE hp (Fin.last p))) ^ 2 = 1 := by
    have : Finset.Ioi (Fin.last p) = ∅ := by
      ext j
      simp [not_lt.mpr (Fin.le_last j)]
    rw [this, Finset.prod_empty]
  rw [hlast, mul_one]
  have hsplit : ∀ i : Fin p,
      ∏ j ∈ Finset.Ioi i.castSucc,
        (γ (Fin.castLE hp j) - γ (Fin.castLE hp i.castSucc)) ^ 2
      = (∏ k ∈ Finset.Ioi i,
          (γ (Fin.castLE (by omega) k) - γ (Fin.castLE (by omega) i)) ^ 2)
        * (γ ⟨p, by omega⟩ - γ (Fin.castLE (by omega) i)) ^ 2 := by
    intro i
    have hset : Finset.Ioi i.castSucc
        = insert (Fin.last p) ((Finset.Ioi i).map Fin.castSuccEmb) := by
      ext j
      refine Fin.lastCases ?_ (fun k => ?_) j
      · simp [Fin.castSucc_lt_last]
      · simp [Fin.castSucc_lt_castSucc_iff, Fin.le_last]
    have hnot : Fin.last p ∉ (Finset.Ioi i).map Fin.castSuccEmb := by
      simp
    rw [hset, Finset.prod_insert hnot, Finset.prod_map, mul_comm]
    congr 1
  rw [Finset.prod_congr rfl (fun i _ => hsplit i), Finset.prod_mul_distrib]

lemma estUnitriSup_eq_one_of_tri_inf {n : ℕ} (R : Matrix (Fin n) (Fin n) ℂ)
    (hR : EstUnitriSup R) (hInf : ∀ i j : Fin n, i < j → R i j = 0) : R = 1 := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · rw [hInf i j h, Matrix.one_apply_ne (ne_of_lt h)]
  · subst h; rw [hR.2 i, Matrix.one_apply_eq]
  · rw [hR.1 i j h, Matrix.one_apply_ne (ne_of_gt h)]

lemma EstUnitriSup.mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
    (hA : EstUnitriSup A) (hB : EstUnitriSup B) : EstUnitriSup (A * B) := by
  refine ⟨?_, ?_⟩
  · intro i j hji
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k < i
    · rw [hA.1 i k hk, zero_mul]
    · push Not at hk
      have : j < k := lt_of_lt_of_le hji hk
      rw [hB.1 k j this, mul_zero]
  · intro i
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single i]
    · rw [hA.2 i, hB.2 i, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [hA.1 i k h, zero_mul]
      · rw [hB.1 k i h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i) h

lemma commute_diag_distinct {n : ℕ} (δ : Fin n → ℂ) (hδ : Function.Injective δ)
    (M : Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix.diagonal δ * M = M * Matrix.diagonal δ) :
    ∀ i j : Fin n, i ≠ j → M i j = 0 := by
  intro i j hij
  have h' := congrFun (congrFun h i) j
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at h'
  have : (δ i - δ j) * M i j = 0 := by linear_combination h'
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (hδ (sub_eq_zero.mp h0)) hij
  · exact h0

lemma EstUnitriSup.det_eq_one {n : ℕ} {R : Matrix (Fin n) (Fin n) ℂ}
    (hR : EstUnitriSup R) : R.det = 1 := by
  have hT : R.BlockTriangular id := fun i j hij => hR.1 i j hij
  rw [Matrix.det_of_isUpperTriangular hT]
  exact Finset.prod_eq_one (fun i _ => hR.2 i)

lemma EstUnitriSup.inv {n : ℕ} {R : Matrix (Fin n) (Fin n) ℂ}
    (hR : EstUnitriSup R) : EstUnitriSup R⁻¹ := by
  have hdet : IsUnit R.det := by
    rw [EstUnitriSup.det_eq_one hR]; exact isUnit_one
  let _ : Invertible R := Matrix.invertibleOfIsUnitDet R hdet
  have hT : R.BlockTriangular id := fun i j hij => hR.1 i j hij
  have hTi : R⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hT
  refine ⟨fun i j hij => hTi hij, fun i => ?_⟩
  have h1 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hdet
  have h2 := congrFun (congrFun h1 i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h2
  · rwa [hR.2 i, mul_one, Matrix.one_apply_eq] at h2
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with h | h
    · rw [hTi h, zero_mul]
    · rw [hR.1 k i h, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma ligne_diag {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (δ : Fin n → ℂ)
    (hTtri : ∀ i j : Fin n, j < i → T i j = 0)
    (hTdiag : ∀ i, T i i = δ i)
    (v : Fin n → ℂ) (j : Fin n) (hv1 : v j = 1)
    (hv0 : ∀ i, j < i → v i = 0)
    (i : Fin n) (hij : i = j) :
    ∑ k, T i k * v k = δ j * v i := by
  subst hij
  rw [Finset.sum_eq_single i]
  · rw [hTdiag, hv1]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h' | h'
    · rw [hTtri i k h', zero_mul]
    · rw [hv0 k h', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma somme_erase_update {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hTtri : ∀ i j : Fin n, j < i → T i j = 0)
    (v : Fin n → ℂ) (i0 : Fin n) (c : ℂ) :
    ∑ k ∈ Finset.univ.erase i0, T i0 k * Function.update v i0 c k
      = ∑ k ∈ Finset.Ioi i0, T i0 k * v k := by
  symm
  rw [← Finset.sum_subset (s₁ := Finset.Ioi i0) (s₂ := Finset.univ.erase i0)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Function.update_of_ne (ne_of_gt (Finset.mem_Ioi.mp hk))]
  · intro k hk
    simp only [Finset.mem_Ioi] at hk
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ne_of_gt hk
  · intro k hk hknot
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hk
    simp only [Finset.mem_Ioi, not_lt] at hknot
    have hlt : k < i0 := lt_of_le_of_ne hknot hk
    rw [hTtri i0 k hlt, zero_mul]

lemma algebre_correction (a b s : ℂ) (hne : a - b ≠ 0) :
    a * (-s / (a - b)) + s = b * (-s / (a - b)) := by
  field_simp
  ring

lemma correction_ligne {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (δ : Fin n → ℂ)
    (hδ : Function.Injective δ)
    (hTtri : ∀ i j : Fin n, j < i → T i j = 0)
    (hTdiag : ∀ i, T i i = δ i)
    (j i0 : Fin n) (hlt : i0 < j)
    (v : Fin n → ℂ) (hv1 : v j = 1) (hv0 : ∀ i, j < i → v i = 0)
    (hveq : ∀ i : Fin n, i0 < i → ∑ k, T i k * v k = δ j * v i) :
    ∃ v' : Fin n → ℂ, v' j = 1 ∧ (∀ i, j < i → v' i = 0) ∧
      ∀ i : Fin n, i0 ≤ i → ∑ k, T i k * v' k = δ j * v' i := by
  have hne : δ i0 - δ j ≠ 0 :=
    sub_ne_zero.mpr (fun h => (ne_of_lt hlt) (hδ h))
  set s : ℂ := ∑ k ∈ Finset.Ioi i0, T i0 k * v k with hs
  set c : ℂ := -s / (δ i0 - δ j) with hc
  refine ⟨Function.update v i0 c, ?_, ?_, ?_⟩
  · rw [Function.update_of_ne (ne_of_gt hlt)]
    exact hv1
  · intro i hi
    rw [Function.update_of_ne (ne_of_gt (lt_trans hlt hi))]
    exact hv0 i hi
  · intro i hi
    have hagree : ∀ k, i0 < k → Function.update v i0 c k = v k := fun k hk =>
      Function.update_of_ne (ne_of_gt hk) _ _
    rcases hi.eq_or_lt with rfl | hlt'
    · have hsum : ∑ k, T i0 k * Function.update v i0 c k = T i0 i0 * c + s := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0), Function.update_self,
          somme_erase_update T hTtri v i0 c]
      rw [hsum, Function.update_self, hTdiag i0, hc]
      exact algebre_correction (δ i0) (δ j) s hne
    · have hrow : ∑ k, T i k * Function.update v i0 c k = ∑ k, T i k * v k := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k < i
        · rw [hTtri i k hk, zero_mul, zero_mul]
        · push Not at hk
          rw [hagree k (lt_of_lt_of_le hlt' hk)]
      rw [hrow, hveq i hlt', hagree i hlt']

lemma existe_passage {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (δ : Fin n → ℂ)
    (hδ : Function.Injective δ)
    (hTtri : ∀ i j : Fin n, j < i → T i j = 0)
    (hTdiag : ∀ i, T i i = δ i) :
    ∃ P : Matrix (Fin n) (Fin n) ℂ, EstUnitriSup P ∧
      P⁻¹ * T * P = Matrix.diagonal δ := by
  have hcol : ∀ j : Fin n, ∃ v : Fin n → ℂ,
      v j = 1 ∧ (∀ i, j < i → v i = 0) ∧
      ∀ i, (∑ k, T i k * v k) = δ j * v i := by
    intro j
    have key : ∀ m : ℕ, ∃ v : Fin n → ℂ,
        v j = 1 ∧ (∀ i, j < i → v i = 0) ∧
        ∀ i : Fin n, n - m ≤ i.val → (∑ k, T i k * v k) = δ j * v i := by
      intro m
      induction m with
      | zero =>
        refine ⟨fun i => if i = j then 1 else 0, by simp, ?_, ?_⟩
        · intro i hji
          simp [ne_of_gt hji]
        · intro i hi
          exfalso
          have := i.isLt
          omega
      | succ m ih =>
        obtain ⟨v, hv1, hv0, hveq⟩ := ih
        by_cases hm : m + 1 ≤ n
        · let i0 : Fin n := ⟨n - (m + 1), by omega⟩
          have hi0 : ∀ i : Fin n, n - (m + 1) ≤ i.val → i = i0 ∨ n - m ≤ i.val := by
            intro i hi
            by_cases h : i = i0
            · exact Or.inl h
            · right
              have : i.val ≠ n - (m + 1) := fun h' => h (Fin.ext h')
              omega
          by_cases hji : j < i0
          · refine ⟨v, hv1, hv0, ?_⟩
            intro i hi
            rcases hi0 i hi with rfl | h
            · have hz : ∑ k, T i0 k * v k = 0 := by
                apply Finset.sum_eq_zero
                intro k _
                by_cases hk : k < i0
                · rw [hTtri i0 k hk, zero_mul]
                · push Not at hk
                  have : v k = 0 := hv0 k (lt_of_lt_of_le hji hk)
                  rw [this, mul_zero]
              rw [hz, hv0 i0 hji, mul_zero]
            · exact hveq i h
          · push Not at hji
            rcases hji.eq_or_lt with heq | hlt
            · refine ⟨v, hv1, hv0, ?_⟩
              intro i hi
              rcases hi0 i hi with rfl | h
              · exact ligne_diag T δ hTtri hTdiag v j hv1 hv0 i0 heq
              · exact hveq i h
            · obtain ⟨v', h1, h2, h3⟩ := correction_ligne T δ hδ hTtri hTdiag j i0 hlt v hv1 hv0
                (fun i hi => hveq i (by
                  have : i0.val < i.val := hi
                  have : i0.val = n - (m+1) := rfl
                  omega))
              exact ⟨v', h1, h2, fun i hi => h3 i (by
                change i0.val ≤ i.val
                have : i0.val = n - (m+1) := rfl
                omega)⟩
        · refine ⟨v, hv1, hv0, ?_⟩
          intro i hi
          exact hveq i (by omega)
    obtain ⟨v, hv1, hv0, hveq⟩ := key n
    exact ⟨v, hv1, hv0, fun i => hveq i (by omega)⟩
  choose v hv1 hv0 hveq using hcol
  let P : Matrix (Fin n) (Fin n) ℂ := Matrix.of (fun i j => v j i)
  have hP : EstUnitriSup P := by
    refine ⟨?_, ?_⟩
    · intro i j hji
      exact hv0 j i hji
    · intro i
      exact hv1 i
  have hTP : T * P = P * Matrix.diagonal δ := by
    ext i j
    rw [Matrix.mul_diagonal]
    simp only [Matrix.mul_apply, P, Matrix.of_apply]
    rw [hveq j i, mul_comm]
  have hdet : IsUnit P.det := by rw [EstUnitriSup.det_eq_one hP]; exact isUnit_one
  refine ⟨P, hP, ?_⟩
  calc P⁻¹ * T * P = P⁻¹ * (T * P) := by rw [Matrix.mul_assoc]
    _ = P⁻¹ * (P * Matrix.diagonal δ) := by rw [hTP]
    _ = Matrix.diagonal δ := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul P hdet, Matrix.one_mul]


lemma unicite_passage {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) (δ : Fin n → ℂ)
    (hδ : Function.Injective δ) (P₁ P₂ : Matrix (Fin n) (Fin n) ℂ)
    (h1 : EstUnitriSup P₁) (h2 : EstUnitriSup P₂)
    (e1 : P₁⁻¹ * T * P₁ = Matrix.diagonal δ)
    (e2 : P₂⁻¹ * T * P₂ = Matrix.diagonal δ) : P₁ = P₂ := by
  have d1 : IsUnit P₁.det := by rw [EstUnitriSup.det_eq_one h1]; exact isUnit_one
  have d2 : IsUnit P₂.det := by rw [EstUnitriSup.det_eq_one h2]; exact isUnit_one
  set M := P₂⁻¹ * P₁ with hM
  have hcomm : Matrix.diagonal δ * M = M * Matrix.diagonal δ := by
    have hA : Matrix.diagonal δ * M = P₂⁻¹ * T * P₁ := by
      rw [← e2, hM]
      calc P₂⁻¹ * T * P₂ * (P₂⁻¹ * P₁)
          = P₂⁻¹ * T * (P₂ * P₂⁻¹) * P₁ := by simp only [Matrix.mul_assoc]
        _ = P₂⁻¹ * T * P₁ := by
          rw [Matrix.mul_nonsing_inv _ d2, Matrix.mul_one]
    have hB : M * Matrix.diagonal δ = P₂⁻¹ * T * P₁ := by
      rw [← e1, hM]
      calc P₂⁻¹ * P₁ * (P₁⁻¹ * T * P₁)
          = P₂⁻¹ * (P₁ * P₁⁻¹) * T * P₁ := by simp only [Matrix.mul_assoc]
        _ = P₂⁻¹ * T * P₁ := by
          rw [Matrix.mul_nonsing_inv _ d1, Matrix.mul_one]
    rw [hA, hB]
  have hdiag := commute_diag_distinct δ hδ M hcomm
  have hMup : EstUnitriSup M := EstUnitriSup.mul (EstUnitriSup.inv h2) h1
  have hinf : ∀ i j : Fin n, i < j → M i j = 0 := fun i j hij => hdiag i j (ne_of_lt hij)
  have hM1 : M = 1 := estUnitriSup_eq_one_of_tri_inf M hMup hinf
  have : P₁ = P₂ := by
    calc P₁ = P₂ * (P₂⁻¹ * P₁) := by rw [← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ d2, Matrix.one_mul]
      _ = P₂ := by rw [← hM, hM1, Matrix.mul_one]
  exact this

lemma hankelN_real {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (hReel : ∀ i : Fin D, (γ i).im = 0) (n : ℕ) (hn : n ≤ D) :
    ∀ i j : Fin n, (hankelN γ mult n hn i j).im = 0 := by
  intro i j
  simp only [hankelN, Matrix.of_apply, mom]
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro k _
  have hpow : ((γ (Fin.castLE hn k)) ^ (i.val + j.val)).im = 0 := by
    have : γ (Fin.castLE hn k) = ((γ (Fin.castLE hn k)).re : ℂ) :=
      Complex.ext (by simp) (by simp [hReel])
    rw [this, ← Complex.ofReal_pow]
    exact Complex.ofReal_im _
  rw [Complex.mul_im, hpow]
  simp

lemma pivot_pos {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (v : Fin n → ℂ) (hvre : ∀ i, (v i).im = 0) (hv : v ≠ 0) :
    0 < (v ⬝ᵥ (H.mulVec v)).re := by
  have hstar : star v = v := by
    funext i
    simp only [Pi.star_apply]
    exact Complex.conj_eq_iff_im.mpr (hvre i)
  have h := hH.dotProduct_mulVec_pos hv
  rw [hstar] at h
  exact (Complex.pos_iff.mp h).1

lemma existe_LDL_reel_zero (H : Matrix (Fin 0) (Fin 0) ℂ) :
    ∃ R : Matrix (Fin 0) (Fin 0) ℂ, EstUnitriSup R ∧ (∀ i j, (R i j).im = 0) ∧
      ∃ s : Fin 0 → ℂ, (∀ k, 0 < (s k).re) ∧ (∀ k, (s k).im = 0) ∧
        R.transpose * H * R = Matrix.diagonal s := by
  refine ⟨1, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0, ?_⟩
  refine ⟨fun i => 0, fun k => k.elim0, fun k => k.elim0, ?_⟩
  ext i
  exact i.elim0

lemma posDef_coin {p : ℕ} (H : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ) (hH : H.PosDef) :
    (H.submatrix Fin.castSucc Fin.castSucc).PosDef :=
  hH.submatrix (Fin.castSucc_injective p)

lemma dotProduct_mulVec_im {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hreal : ∀ i j, (H i j).im = 0) (v : Fin n → ℂ) (hvre : ∀ i, (v i).im = 0) :
    (v ⬝ᵥ H.mulVec v).im = 0 := by
  simp only [dotProduct, Matrix.mulVec, Complex.im_sum]
  apply Finset.sum_eq_zero
  intro i _
  simp only [Complex.mul_im, hvre i]
  simp only [Complex.re_sum, Complex.im_sum,
    Complex.mul_im, Complex.mul_re, hreal, hvre]
  simp

lemma solution_reelle {p : ℕ} (A : Matrix (Fin p) (Fin p) ℂ) (hAunit : IsUnit A.det)
    (hAre : ∀ i j, (A i j).im = 0) (b : Fin p → ℂ) (hbre : ∀ i, (b i).im = 0) :
    ∃ w : Fin p → ℂ, (∀ i, (w i).im = 0) ∧ A.mulVec w = -b := by
  set w₀ : Fin p → ℂ := -(A⁻¹.mulVec b) with hw₀
  have hw₀A : A.mulVec w₀ = -b := by
    rw [hw₀, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hAunit,
      Matrix.one_mulVec]
  have hconj : A.mulVec (fun i => star (w₀ i)) = -b := by
    funext i
    have h := congrFun hw₀A i
    have h' := congrArg star h
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Pi.neg_apply, star_neg] at h' ⊢
    have hA' : ∀ k, star (A i k) = A i k := fun k => Complex.conj_eq_iff_im.mpr (hAre i k)
    have hb' : star (b i) = b i := Complex.conj_eq_iff_im.mpr (hbre i)
    simp only [hA', hb'] at h'
    simpa [mul_comm] using h'
  have heq : (fun i => star (w₀ i)) = w₀ := by
    have h0 : A.mulVec ((fun i => star (w₀ i)) - w₀) = 0 := by
      rw [Matrix.mulVec_sub, hconj, hw₀A, sub_self]
    have := congrArg (fun x => A⁻¹.mulVec x) h0
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hAunit, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact sub_eq_zero.mp this
  refine ⟨w₀, fun i => ?_, hw₀A⟩
  have := congrFun heq i
  exact Complex.conj_eq_iff_im.mp this

lemma bloc_dot {p : ℕ} (H : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ)
    (x' y' : Fin p → ℂ) (α β : ℂ) :
    (Fin.snoc x' α : Fin (p + 1) → ℂ) ⬝ᵥ H.mulVec (Fin.snoc y' β : Fin (p + 1) → ℂ)
    = x' ⬝ᵥ (H.submatrix Fin.castSucc Fin.castSucc).mulVec y'
      + β * (x' ⬝ᵥ fun i => H (Fin.castSucc i) (Fin.last p))
      + α * ((fun j => H (Fin.last p) (Fin.castSucc j)) ⬝ᵥ y')
      + α * β * H (Fin.last p) (Fin.last p) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
    Fin.snoc_last, Matrix.submatrix_apply, Finset.mul_sum,
    mul_add, Finset.sum_add_distrib]
  have h : ∑ x : Fin p, x' x * (H x.castSucc (Fin.last p) * β)
      = ∑ i : Fin p, β * (x' i * H i.castSucc (Fin.last p)) :=
    Finset.sum_congr rfl fun x _ => by ring
  rw [h]
  ring

lemma dot_col_eq {p : ℕ} (R' A : Matrix (Fin p) (Fin p) ℂ) (i' j' : Fin p) :
    (fun k => R' k i') ⬝ᵥ A.mulVec (fun k => R' k j') = (R'.transpose * A * R') i' j' := by
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

lemma dot_mulVec_comm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hsym : ∀ i j, H i j = H j i) (x y : Fin n → ℂ) :
    x ⬝ᵥ H.mulVec y = y ⬝ᵥ H.mulVec x := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [hsym a c]
  ring

lemma posDef_reel_symm {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (hreal : ∀ i j, (H i j).im = 0) : ∀ i j, H i j = H j i := by
  intro i j
  have h' := congrFun (congrFun hH.isHermitian j) i
  simp only [Matrix.conjTranspose_apply] at h'
  have hs : star (H i j) = H i j := Complex.conj_eq_iff_im.mpr (hreal i j)
  rw [hs] at h'
  exact h'

lemma dot_eq_zero_of_last {p : ℕ} (u y : Fin (p + 1) → ℂ)
    (hu : u (Fin.last p) = 0) (hy : ∀ i : Fin p, y (Fin.castSucc i) = 0) :
    u ⬝ᵥ y = 0 := by
  simp [dotProduct, Fin.sum_univ_castSucc, hu, hy]

lemma orth_col {p : ℕ} (H : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ)
    (hsym : ∀ i j, H i j = H j i) (v u : Fin (p + 1) → ℂ)
    (hu : u (Fin.last p) = 0) (hHv : ∀ i : Fin p, (H.mulVec v) (Fin.castSucc i) = 0) :
    u ⬝ᵥ H.mulVec v = 0 ∧ v ⬝ᵥ H.mulVec u = 0 := by
  have h1 : u ⬝ᵥ H.mulVec v = 0 := dot_eq_zero_of_last u _ hu hHv
  refine ⟨h1, ?_⟩
  rw [dot_mulVec_comm H hsym]
  exact h1

lemma coin_bloc {p : ℕ} (H : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ)
    (R' : Matrix (Fin p) (Fin p) ℂ) (i' j' : Fin p) :
    (Fin.snoc (fun k => R' k i') (0 : ℂ) : Fin (p + 1) → ℂ) ⬝ᵥ
      H.mulVec (Fin.snoc (fun k => R' k j') (0 : ℂ) : Fin (p + 1) → ℂ)
    = (R'.transpose * H.submatrix Fin.castSucc Fin.castSucc * R') i' j' := by
  rw [bloc_dot]
  simp only [zero_mul, mul_zero, add_zero]
  exact dot_col_eq R' (H.submatrix Fin.castSucc Fin.castSucc) i' j'

lemma existe_LDL_reel_succ {p : ℕ} (H : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ)
    (hH : H.PosDef) (hreal : ∀ i j, (H i j).im = 0)
    (R' : Matrix (Fin p) (Fin p) ℂ) (hR' : EstUnitriSup R')
    (hR're : ∀ i j, (R' i j).im = 0)
    (s' : Fin p → ℂ) (hs' : ∀ k, 0 < (s' k).re) (hs're : ∀ k, (s' k).im = 0)
    (hRe' : R'.transpose * H.submatrix Fin.castSucc Fin.castSucc * R' = Matrix.diagonal s') :
    ∃ R : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ, EstUnitriSup R ∧
      (∀ i j, (R i j).im = 0) ∧
      ∃ s : Fin (p + 1) → ℂ, (∀ k, 0 < (s k).re) ∧ (∀ k, (s k).im = 0) ∧
        R.transpose * H * R = Matrix.diagonal s := by
  set A : Matrix (Fin p) (Fin p) ℂ := H.submatrix Fin.castSucc Fin.castSucc with hAdef
  set b : Fin p → ℂ := fun i => H (Fin.castSucc i) (Fin.last p) with hbdef
  have hA : A.PosDef := posDef_coin H hH
  have hAunit : IsUnit A.det := by
    have := hA.det_pos
    exact isUnit_iff_ne_zero.mpr this.ne'
  have hAre : ∀ i j, (A i j).im = 0 := fun i j => hreal _ _
  have hbre : ∀ i, (b i).im = 0 := fun i => hreal _ _
  have hw : ∃ w : Fin p → ℂ, (∀ i, (w i).im = 0) ∧ A.mulVec w = -b :=
    solution_reelle A hAunit hAre b hbre
  obtain ⟨w, hwre, hwA⟩ := hw
  let R : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ :=
    Matrix.of fun i j =>
      Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j)
        (fun i' => Fin.lastCases (w i') (fun j' => R' i' j') j) i
  have hR : EstUnitriSup R := by
    refine ⟨?_, ?_⟩
    · intro i j hji
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hji (lt_irrefl _)
        | cast j' => simp [R]
      | cast i' =>
        induction j using Fin.lastCases with
        | last =>
          exfalso
          exact absurd hji (not_lt.mpr (Fin.le_last _))
        | cast j' =>
          have hj' : j' < i' := by simpa using hji
          simp [R, hR'.1 i' j' hj']
    · intro i
      induction i using Fin.lastCases with
      | last => simp [R]
      | cast i' => simp [R, hR'.2 i']
  have hRre : ∀ i j, (R i j).im = 0 := by
    intro i j
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => simp [R]
      | cast j' => simp [R]
    | cast i' =>
      induction j using Fin.lastCases with
      | last => simpa [R] using hwre i'
      | cast j' => simpa [R] using hR're i' j'
  set v : Fin (p + 1) → ℂ := fun i => R i (Fin.last p) with hvdef
  have hvre : ∀ i, (v i).im = 0 := fun i => hRre i _
  have hv0 : v ≠ 0 := by
    intro h
    have h1 : v (Fin.last p) = 0 := congrFun h (Fin.last p)
    simp [hvdef, R] at h1
  have hpiv : 0 < (v ⬝ᵥ H.mulVec v).re := pivot_pos H hH v hvre hv0
  have hentry : ∀ i j, (R.transpose * H * R) i j
      = (fun k => R k i) ⬝ᵥ H.mulVec (fun k => R k j) := by
    intro i j
    simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hHv : ∀ i : Fin p, (H.mulVec v) (Fin.castSucc i) = 0 := by
    intro i
    have h1 := congrFun hwA i
    simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at h1 ⊢
    rw [Fin.sum_univ_castSucc]
    simp only [hvdef, R, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc]
    simp only [hAdef, hbdef, Matrix.submatrix_apply] at h1
    linear_combination h1
  have hcolc : ∀ j' : Fin p, (fun k => R k (Fin.castSucc j'))
      = Fin.snoc (fun i' => R' i' j') (0 : ℂ) := by
    intro j'
    funext k
    induction k using Fin.lastCases with
    | last => simp [R]
    | cast i' => simp [R]
  have hcoll : (fun k => R k (Fin.last p)) = Fin.snoc w (1 : ℂ) := by
    funext k
    induction k using Fin.lastCases with
    | last => simp [R]
    | cast i' => simp [R]
  have hsym : ∀ i j, H i j = H j i := posDef_reel_symm H hH hreal
  refine ⟨R, hR, hRre, Fin.lastCases (v ⬝ᵥ H.mulVec v) s', ?_, ?_, ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp only [Fin.lastCases_last]
      exact hpiv
    · simp only [Fin.lastCases_castSucc]
      exact hs' i
  · intro k
    refine Fin.lastCases ?_ (fun i => ?_) k
    · simp only [Fin.lastCases_last]
      exact dotProduct_mulVec_im H hreal v hvre
    · simp only [Fin.lastCases_castSucc]
      exact hs're i
  · have hsym := posDef_reel_symm H hH hreal
    ext i j
    rw [hentry i j]
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last =>
        simp [Matrix.diagonal_apply_eq, hvdef]
      | cast j' =>
        have hu : (fun k => R k (Fin.castSucc j')) (Fin.last p) = 0 := by simp [R]
        have key := (orth_col H hsym v (fun k => R k (Fin.castSucc j')) hu hHv).2
        have key' : (fun k => R k (Fin.last p)) ⬝ᵥ
          H.mulVec (fun k => R k (Fin.castSucc j')) = 0 := key
        rw [key', Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last j').symm]
    | cast i' =>
      induction j using Fin.lastCases with
      | last =>
        have hu : (fun k => R k (Fin.castSucc i')) (Fin.last p) = 0 := by simp [R]
        have key := (orth_col H hsym v (fun k => R k (Fin.castSucc i')) hu hHv).1
        have key' : (fun k => R k (Fin.castSucc i')) ⬝ᵥ
          H.mulVec (fun k => R k (Fin.last p)) = 0 := key
        rw [key', Matrix.diagonal_apply_ne _ (Fin.castSucc_ne_last i')]
      | cast j' =>
        rw [hcolc i', hcolc j', coin_bloc, hRe']
        simp [Matrix.diagonal_apply, Fin.castSucc_inj]

lemma existe_LDL_reel {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (hreal : ∀ i j, (H i j).im = 0) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, EstUnitriSup R ∧ (∀ i j, (R i j).im = 0) ∧
      ∃ s : Fin n → ℂ, (∀ k, 0 < (s k).re) ∧ (∀ k, (s k).im = 0) ∧
        R.transpose * H * R = Matrix.diagonal s := by
  induction n with
  | zero => exact existe_LDL_reel_zero H
  | succ p ih =>
    have hA := posDef_coin H hH
    have hAreal : ∀ i j, ((H.submatrix Fin.castSucc Fin.castSucc) i j).im = 0 :=
      fun i j => hreal _ _
    obtain ⟨R', hR', hR're, s', hs', hs're, hRe'⟩ := ih _ hA hAreal
    exact existe_LDL_reel_succ H hH hreal R' hR' hR're s' hs' hs're hRe'

lemma existe_LDL {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (hreal : ∀ i j, (H i j).im = 0) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, EstUnitriSup R ∧
      ∃ s : Fin n → ℂ, (∀ k, 0 < (s k).re) ∧ R.transpose * H * R = Matrix.diagonal s := by
  obtain ⟨R, hR, _, s, hs, _, hRe⟩ := existe_LDL_reel H hH hreal
  exact ⟨R, hR, s, hs, hRe⟩

lemma unicite_LDL {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : IsUnit H.det)
    (Q R : Matrix (Fin n) (Fin n) ℂ) (hQ : EstUnitriSup Q) (hR : EstUnitriSup R)
    (t s : Fin n → ℂ)
    (hQe : Q.transpose * H * Q = Matrix.diagonal t)
    (hRe : R.transpose * H * R = Matrix.diagonal s) :
    Q = R := by
  have hRunit : IsUnit R.det := by rw [EstUnitriSup.det_eq_one hR]; exact isUnit_one
  have hQunit : IsUnit Q.det := by rw [EstUnitriSup.det_eq_one hQ]; exact isUnit_one
  have hs : ∀ i, s i ≠ 0 := by
    have hdet := congrArg Matrix.det hRe
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      EstUnitriSup.det_eq_one hR,
      Matrix.det_diagonal] at hdet
    intro i hi
    have : ∏ j, s j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [this] at hdet
    rw [one_mul, mul_one] at hdet
    exact (isUnit_iff_ne_zero.mp hH) hdet
  have hM : EstUnitriSup (R⁻¹ * Q) :=
    EstUnitriSup.mul (EstUnitriSup.inv hR) hQ
  have hMe : (R⁻¹ * Q).transpose * Matrix.diagonal s * (R⁻¹ * Q) = Matrix.diagonal t := by
    have h1 : R * R⁻¹ = 1 := Matrix.mul_nonsing_inv _ hRunit
    have h2 : (R⁻¹).transpose * R.transpose = 1 := by
      rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    rw [← hRe, Matrix.transpose_mul]
    calc Q.transpose * (R⁻¹).transpose * (R.transpose * H * R) * (R⁻¹ * Q)
        = Q.transpose * ((R⁻¹).transpose * R.transpose) * H * (R * R⁻¹) * Q := by
          simp only [Matrix.mul_assoc]
      _ = Q.transpose * H * Q := by
          rw [h2, h1]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = Matrix.diagonal t := hQe
  have hM1 : R⁻¹ * Q = 1 := by
    set M := R⁻¹ * Q with hMdef
    have hoff : ∀ (m : ℕ) (i j : Fin n), j.val = m → i < j → M i j = 0 := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro i j hjm hij
        have hentry : (M.transpose * Matrix.diagonal s * M) j i = 0 := by
          rw [hMe, Matrix.diagonal_apply_ne _ (ne_of_gt hij)]
        have hsum : (M.transpose * Matrix.diagonal s * M) j i = s i * M i j := by
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single i]
          · rw [Matrix.mul_apply, Finset.sum_eq_single i]
            · simp [Matrix.transpose_apply, Matrix.diagonal_apply_eq, hM.2 i]
              ring
            · intro k _ hki
              simp [Matrix.diagonal_apply_ne _ hki]
            · intro h; exact absurd (Finset.mem_univ i) h
          · intro k _ hki
            rw [Matrix.mul_apply, Finset.sum_eq_single k]
            · rcases lt_or_gt_of_ne hki with hk | hk
              · have hMki : M k i = 0 :=
                  ih i.val (by rw [← hjm]; exact hij) k i rfl hk
                simp [hMki]
              · simp [hM.1 k i hk]
            · intro l _ hlk
              simp [Matrix.diagonal_apply_ne _ hlk]
            · intro h; exact absurd (Finset.mem_univ k) h
          · intro h; exact absurd (Finset.mem_univ i) h
        rw [hsum] at hentry
        exact (mul_eq_zero.mp hentry).resolve_left (hs i)
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · rw [hoff j.val i j rfl h]; simp [Matrix.one_apply_ne h.ne]
    · subst h; rw [hM.2 i]; simp
    · rw [hM.1 i j h]; simp [Matrix.one_apply_ne h.ne']
  calc Q = R * (R⁻¹ * Q) := by
        rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hRunit, Matrix.one_mul]
    _ = R := by rw [hM1, Matrix.mul_one]


lemma det_hankelN_vandermonde {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (hSimple : ∀ i : Fin D, mult i = 1) (n : ℕ) (hn : n ≤ D) :
    (hankelN γ mult n hn).det
      = ∏ i : Fin n, ∏ j : Fin n, if i < j then
          (γ (Fin.castLE hn j) - γ (Fin.castLE hn i)) ^ 2 else 1 := by
  rw [det_hankelN_eq_prod γ mult hSimple n hn]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [← Finset.prod_filter]
  congr 1
  ext j
  simp [Finset.mem_Ioi, Finset.mem_filter]

theorem construction_operateurs_TN_zeros
    (D : ℕ) (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (T : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ)
    (hDef : ∀ (n : ℕ) (hnD : n ≤ D), 1 ≤ n → (hankelN γ mult n hnD).PosDef)
    (hReel : ∀ i : Fin D, (γ i).im = 0)
    (hSimple : ∀ i : Fin D, mult i = 1)
    (hDistinct : Function.Injective γ)
    (hTtri : ∀ (n : ℕ) (i j : Fin n), j < i → T n i j = 0)
    (hTdiag : ∀ (n : ℕ) (hnD : n ≤ D) (i : Fin n), T n i i = γ (Fin.castLE hnD i)) :
    ∀ (n : ℕ) (hnD : n ≤ D), 1 ≤ n →
      ((∀ i : Fin n, (γ (Fin.castLE hnD i)).im = 0) ∧
       (∀ i : Fin n, mult (Fin.castLE hnD i) = 1) ∧
       (∀ i j : Fin n, i ≠ j → γ (Fin.castLE hnD i) ≠ γ (Fin.castLE hnD j)) ∧
       (∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P.det ∧
          P⁻¹ * T n * P = Matrix.diagonal (fun i : Fin n => γ (Fin.castLE hnD i)))) ∧
      (∀ (p : ℕ) (hp : p + 1 ≤ D), 1 ≤ p → n = p + 1 →
        (γ ⟨p, by omega⟩ = mom γ mult (p + 1) hp 1
              - ∑ i : Fin p, γ (Fin.castLE (by omega) i)) ∧
        (schurN γ mult p hp
            = (hankelN γ mult (p + 1) hp).det / (coinHankel γ mult p hp).det) ∧
        ((hankelN γ mult (p + 1) hp).det / (hankelN γ mult p (by omega)).det
            = ∏ i : Fin p, (γ ⟨p, by omega⟩ - γ (Fin.castLE (by omega) i)) ^ 2) ∧
        0 < (schurN γ mult p hp).re) ∧
      (∃! R : Matrix (Fin n) (Fin n) ℂ, EstUnitriSup R ∧
          ∃ s : Fin n → ℂ, (∀ k : Fin n, 0 < (s k).re) ∧
            R.transpose * hankelN γ mult n hnD * R = Matrix.diagonal s) ∧
      (∃! P : Matrix (Fin n) (Fin n) ℂ, EstUnitriSup P ∧
          P⁻¹ * T n * P = Matrix.diagonal (fun i : Fin n => γ (Fin.castLE hnD i))) := by
  intro n hnD hn
  have h1 := construction_operateurs_TN_zeros_partiel D γ mult hDef hReel hSimple hDistinct n hnD hn
  obtain ⟨hre, hsimp, hdist, h2⟩ := h1
  have hinj : Function.Injective (fun i : Fin n => γ (Fin.castLE hnD i)) := by
    intro i j hij
    by_contra hne
    exact hdist i j hne hij
  have hex := existe_passage (T n) (fun i : Fin n => γ (Fin.castLE hnD i)) hinj
    (hTtri n) (hTdiag n hnD)
  refine ⟨⟨hre, hsimp, hdist, ?_⟩, ?_, ?_, ?_⟩
  · obtain ⟨P, hP, hPe⟩ := hex
    exact ⟨P, by rw [EstUnitriSup.det_eq_one hP]; exact isUnit_one, hPe⟩
  · intro p hp hp1 hnp
    obtain ⟨ha, hb⟩ := h2 p hp hnp
    refine ⟨ha, hb, ?_, ?_⟩
    · have hPDp : (hankelN γ mult p (by omega)).PosDef := hDef p (by omega) hp1
      obtain ⟨hr, _⟩ := det_posDef_re_pos _ hPDp
      have hne : (hankelN γ mult p (by omega)).det ≠ 0 := by
        intro h0
        rw [h0] at hr
        simp at hr
      have hm := det_hankelN_succ γ mult hSimple p hp
      rw [hm]
      field_simp
    · have hPD1 : (hankelN γ mult (p + 1) hp).PosDef := hDef (p + 1) hp (by omega)
      have hPD2 : (coinHankel γ mult p hp).PosDef := coinHankel_posDef γ mult p hp hPD1
      obtain ⟨hr1, hi1⟩ := det_posDef_re_pos _ hPD1
      obtain ⟨hr2, hi2⟩ := det_posDef_re_pos _ hPD2
      have e1 : (hankelN γ mult (p+1) hp).det = ((hankelN γ mult (p+1) hp).det.re : ℂ) :=
        Complex.ext (by simp) (by simp [hi1])
      have e2 : (coinHankel γ mult p hp).det = ((coinHankel γ mult p hp).det.re : ℂ) :=
        Complex.ext (by simp) (by simp [hi2])
      rw [hb, e1, e2, ← Complex.ofReal_div, Complex.ofReal_re]
      exact div_pos hr1 hr2
  · have hPD : (hankelN γ mult n hnD).PosDef := hDef n hnD hn
    have hreal : ∀ i j : Fin n, ((hankelN γ mult n hnD) i j).im = 0 :=
      hankelN_real γ mult hReel n hnD
    have hdet : IsUnit (hankelN γ mult n hnD).det := by
      obtain ⟨hr, _⟩ := det_posDef_re_pos _ hPD
      refine isUnit_iff_ne_zero.mpr ?_
      intro h0
      rw [h0] at hr
      simp at hr
    obtain ⟨R, hR, s, hs, hRe⟩ := existe_LDL (hankelN γ mult n hnD) hPD hreal
    refine ⟨R, ⟨hR, s, hs, hRe⟩, ?_⟩
    rintro Q ⟨hQ, t, ht, hQe⟩
    exact unicite_LDL (hankelN γ mult n hnD) hdet Q R hQ hR t s hQe hRe
  · obtain ⟨P, hP, hPe⟩ := hex
    refine ⟨P, ⟨hP, hPe⟩, ?_⟩
    rintro Q ⟨hQ, hQe⟩
    exact unicite_passage (T n) _ hinj Q P hQ hP hQe hPe


---------------------------------------------------------------------

lemma blocPrinc_hankelN {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (n : ℕ) (hnD : n ≤ D) (k : ℕ) (hk : k ≤ n) :
    blocPrinc (hankelN γ mult n hnD) k hk = blocPrincipal γ mult n hnD k hk := by
  ext i j
  simp [blocPrinc, hankelN, blocPrincipal]

lemma blocPrinc_mul_sandwich {n : ℕ} (A R : Matrix (Fin n) (Fin n) ℂ)
    (hR : ∀ i j : Fin n, j < i → R i j = 0) (k : ℕ) (hk : k ≤ n) :
    blocPrinc (R.transpose * A * R) k hk
      = (blocPrinc R k hk).transpose * blocPrinc A k hk * blocPrinc R k hk := by
  ext i j
  simp only [blocPrinc, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have hred : ∀ f : Fin n → ℂ, (∀ m : Fin n, k ≤ m.val → f m = 0) →
      ∑ m : Fin n, f m = ∑ m : Fin k, f (Fin.castLE hk m) := by
    intro f hf
    symm
    apply Finset.sum_bij_ne_zero (fun m _ _ => Fin.castLE hk m)
    · intro m _ _; exact Finset.mem_univ _
    · intro a _ _ b _ _ hab; exact Fin.castLE_injective hk hab
    · intro m _ hm
      have hmk : m.val < k := by
        by_contra hcon
        exact hm (hf m (by omega))
      exact ⟨⟨m.val, hmk⟩, Finset.mem_univ _, by simpa using hm, Fin.ext rfl⟩
    · intro m _ _; rfl
  have hin : ∀ j1 : Fin n,
      ∑ m : Fin n, R m (Fin.castLE hk i) * A m j1
        = ∑ m : Fin k, R (Fin.castLE hk m) (Fin.castLE hk i) * A (Fin.castLE hk m) j1 := by
    intro j1
    apply hred
    intro m hm
    have : R m (Fin.castLE hk i) = 0 := hR m _ (by
      simp only [Fin.lt_def, Fin.val_castLE]; omega)
    simp [this]
  simp_rw [hin]
  apply hred
  intro m hm
  have : R m (Fin.castLE hk j) = 0 := hR m _ (by
    simp only [Fin.lt_def, Fin.val_castLE]; omega)
  simp [this]

lemma pivots_eq_pivotsN {D : ℕ} (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (hDef : ∀ (n : ℕ) (hnD : n ≤ D), 1 ≤ n → (hankelN γ mult n hnD).PosDef)
    (n : ℕ) (hnD : n ≤ D) (hn : 1 ≤ n)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : EstUnitriSup R) (s : Fin n → ℂ)
    (h : R.transpose * hankelN γ mult n hnD * R = Matrix.diagonal s) :
    s = pivotsN γ mult n hnD := by
  set A := hankelN γ mult n hnD with hA
  have hdet : ∀ (k : ℕ) (hk : k ≤ n),
      (blocPrinc A k hk).det = ∏ i : Fin k, s (Fin.castLE hk i) := by
    intro k hk
    have h1 := congrArg (fun M => blocPrinc M k hk) h
    rw [blocPrinc_mul_sandwich A R hR.1 k hk] at h1
    have hRk : (blocPrinc R k hk).det = 1 := by
      rw [Matrix.det_of_isUpperTriangular]
      · simp [blocPrinc, hR.2]
      · intro i j hij
        simp only [blocPrinc, Matrix.submatrix_apply]
        apply hR.1
        change j.val < i.val at hij
        simp only [Fin.lt_def, Fin.val_castLE]
        exact hij
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hRk] at h2
    have h3 : blocPrinc (Matrix.diagonal s) k hk
        = Matrix.diagonal (fun i : Fin k => s (Fin.castLE hk i)) := by
      ext i j
      simp only [blocPrinc, Matrix.submatrix_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · have : Fin.castLE hk i ≠ Fin.castLE hk j :=
          fun e => hij (Fin.castLE_injective hk e)
        simp [hij, this]
    rw [h3, Matrix.det_diagonal] at h2
    simpa using h2
  have hne : ∀ (k : ℕ) (hk : k ≤ n), (blocPrinc A k hk).det ≠ 0 := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp [Matrix.det_isEmpty]
    · have hpd : (blocPrinc A k hk).PosDef :=
        (hDef n hnD hn).submatrix (Fin.castLE_injective hk)
      exact hpd.det_pos.ne'
  funext k
  have hk1 : k.val + 1 ≤ n := by omega
  have e1 := hdet (k.val + 1) hk1
  have e0 := hdet k.val (by omega)
  have hn0 := hne k.val (by omega)
  simp only [pivotsN]
  have hb1 : blocPrincipal γ mult n hnD (k.val + 1) (by omega)
      = blocPrinc A (k.val + 1) hk1 :=
    (blocPrinc_hankelN γ mult n hnD (k.val + 1) hk1).symm
  have hb0 : blocPrincipal γ mult n hnD k.val (by omega)
      = blocPrinc A k.val (by omega) :=
    (blocPrinc_hankelN γ mult n hnD k.val (by omega)).symm
  rw [hb1, hb0, e1]
  rw [e0] at hn0 ⊢
  rw [Fin.prod_univ_castSucc]
  have hlast : Fin.castLE hk1 (Fin.last k.val) = k := Fin.ext rfl
  have hprod : ∀ (h' : k.val ≤ n),
      ∏ i : Fin k.val, s (Fin.castLE hk1 i.castSucc)
        = ∏ i : Fin k.val, s (Fin.castLE h' i) := by
    intro h'
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg s (Fin.ext rfl)
  rw [hlast, hprod (by omega)]
  field_simp


theorem th_ConstructionOperateursTNZerosRiemann
    (D : ℕ) (γ : Fin D → ℂ) (mult : Fin D → ℕ)
    (T : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ)
    (hDef : ∀ (n : ℕ) (hnD : n ≤ D), 1 ≤ n → (hankelN γ mult n hnD).PosDef)
    (hReel : ∀ i : Fin D, (γ i).im = 0)
    (hSimple : ∀ i : Fin D, mult i = 1)
    (hDistinct : Function.Injective γ)
    (hTtri : ∀ (n : ℕ) (i j : Fin n), j < i → T n i j = 0)
    (hTdiag : ∀ (n : ℕ) (hnD : n ≤ D) (i : Fin n), T n i i = γ (Fin.castLE hnD i)) :
    ∀ (n : ℕ) (hnD : n ≤ D), 1 ≤ n →
      -- point 1
      ((∀ i : Fin n, (γ (Fin.castLE hnD i)).im = 0) ∧
       (∀ i : Fin n, mult (Fin.castLE hnD i) = 1) ∧
       (∀ i j : Fin n, i ≠ j → γ (Fin.castLE hnD i) ≠ γ (Fin.castLE hnD j)) ∧
       (∃ P : Matrix (Fin n) (Fin n) ℂ, IsUnit P.det ∧
          P⁻¹ * T n * P = diagZeros γ n hnD)) ∧
      -- point 2
      (∀ (p : ℕ) (hp : p + 1 ≤ D), 1 ≤ p → n = p + 1 →
        (γ ⟨p, by omega⟩ = mom γ mult (p + 1) hp 1
              - ∑ i : Fin p, γ (Fin.castLE (by omega) i)) ∧
        (sN γ mult p hp
            = (hankelN γ mult (p + 1) hp).det / (blocHankel γ mult p hp).det) ∧
        ((hankelN γ mult (p + 1) hp).det / (hankelN γ mult p (by omega)).det
            = ∏ i : Fin p, (γ ⟨p, by omega⟩ - γ (Fin.castLE (by omega) i)) ^ 2) ∧
        0 < (sN γ mult p hp).re) ∧
      -- point 3
      (∃! R : Matrix (Fin n) (Fin n) ℂ, EstUnitriSup R ∧
          (∀ k : Fin n, 0 < (pivotsN γ mult n hnD k).re) ∧
            R.transpose * hankelN γ mult n hnD * R = Matrix.diagonal (pivotsN γ mult n hnD)) ∧
      (∃! P : Matrix (Fin n) (Fin n) ℂ, EstUnitriSup P ∧
          P⁻¹ * T n * P = diagZeros γ n hnD) := by
  intro n hnD hn
  obtain ⟨h1, h2, h3, h4⟩ :=
    construction_operateurs_TN_zeros D γ mult T hDef hReel hSimple hDistinct
      hTtri hTdiag n hnD hn
  refine ⟨h1, h2, ?_, h4⟩
  obtain ⟨R, ⟨hR, s, hs, hRe⟩, huniq⟩ := h3
  have hsS : s = pivotsN γ mult n hnD :=
    pivots_eq_pivotsN γ mult hDef n hnD hn R hR s hRe
  subst hsS
  refine ⟨R, ⟨hR, hs, hRe⟩, ?_⟩
  rintro Q ⟨hQ, _, hQe⟩
  exact huniq Q ⟨hQ, pivotsN γ mult n hnD, hs, hQe⟩






end InductionCanoniqueOp
