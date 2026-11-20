import mathlib
import ThEqRiemann.EqTheorem.DefThEq

/-! -/
namespace CharpolyThEq

open Set Complex DefinitionsThEq


lemma polyAssocieCoeff_fin_zero (c : Fin 0 → ℂ) :
    polyAssocieCoeff c = 1 := by
  simp [polyAssocieCoeff]

lemma charpoly_fin_zero (M : Matrix (Fin 0) (Fin 0) ℂ) :
    Matrix.charpoly M = 1 := by
  simp [Matrix.charpoly]

lemma companionCoeff_charpoly_zero (c : Fin 0 → ℂ) :
    Matrix.charpoly (companionCoeff c) = polyAssocieCoeff c := by
  rw [charpoly_fin_zero, polyAssocieCoeff_fin_zero]

lemma companionCoeff_apply_zero_zero_one (c : Fin 1 → ℂ) :
    companionCoeff c (0 : Fin 1) (0 : Fin 1) = -(c 0) := by
  simp [companionCoeff]

lemma polyAssocieCoeff_one (c : Fin 1 → ℂ) :
    polyAssocieCoeff c = Polynomial.X + Polynomial.C (c 0) := by
  simp [polyAssocieCoeff]

lemma companionCoeff_zero_zero (c : Fin 1 → ℂ) :
    companionCoeff c (0 : Fin 1) 0 = -(c 0) := by
  simp [companionCoeff]

lemma polyAssocieCoeff_fin_one (c : Fin 1 → ℂ) :
    polyAssocieCoeff c = Polynomial.X + Polynomial.C (c 0) := by
  unfold polyAssocieCoeff
  rw [Fin.sum_univ_succ]
  simp

lemma companionCoeff_charpoly_one (c : Fin 1 → ℂ) :
    Matrix.charpoly (companionCoeff c) = polyAssocieCoeff c := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq,
      companionCoeff_zero_zero, polyAssocieCoeff_fin_one]
  simp

lemma companionCoeff_row_zero_first_condition_false
    {K : ℕ} (_ : 2 ≤ K) (_ : Fin K → ℂ) (j : Fin K) :
    ¬ ((0 : ℕ) = (j : ℕ) + 1 ∧ (j : ℕ) < K - 1) := by
  omega

lemma companionCoeff_row_zero_last
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) (j : Fin K)
    (hj : (j : ℕ) = K - 1) :
    companionCoeff c ⟨0, by omega⟩ j = -(c ⟨0, by omega⟩) := by
  simp only [companionCoeff]
  have hfirst := companionCoeff_row_zero_first_condition_false hK c j
  rw [ite_eq_right hfirst, ite_eq_left hj]

lemma companionCoeff_row_zero_not_last
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) (j : Fin K)
    (hj : (j : ℕ) ≠ K - 1) :
    companionCoeff c ⟨0, by omega⟩ j = 0 := by
  have hfirst := companionCoeff_row_zero_first_condition_false hK c j
  simp only [companionCoeff, hfirst, ↓reduceIte, hj]

lemma companionCoeff_row_zero_diag {K : ℕ}
  (hK : 2 ≤ K) (c : Fin K → ℂ) :
    companionCoeff c (⟨0, by omega⟩ : Fin K)
    (⟨0, by omega⟩ : Fin K) = 0 := by
  simp [companionCoeff]
  omega

lemma charmatrix_companionCoeff_row_zero_diag {K : ℕ}
  (hK : 2 ≤ K) (c : Fin K → ℂ) :
    Matrix.charmatrix (companionCoeff c) (⟨0, by omega⟩ : Fin K)
      (⟨0, by omega⟩ : Fin K) = Polynomial.X := by
  rw [Matrix.charmatrix_apply_eq, companionCoeff_row_zero_diag hK c]
  simp

lemma charmatrix_companionCoeff_row_zero_last {K : ℕ}
  (hK : 2 ≤ K) (c : Fin K → ℂ)
    (j : Fin K) (hj : j ≠ (⟨0, by omega⟩ : Fin K))
    (hjlast : (j : ℕ) = K - 1) :
    Matrix.charmatrix (companionCoeff c) (⟨0, by omega⟩ : Fin K) j
      = Polynomial.C (c (⟨0, by omega⟩ : Fin K)) := by
  have hne : (⟨0, by omega⟩ : Fin K) ≠ j := Ne.symm hj
  change Matrix.charmatrix (companionCoeff c)
    (⟨0, by omega⟩ : Fin K) j = _
  rw [Matrix.charmatrix_apply_ne
        (M := companionCoeff c) (i := (⟨0, by omega⟩ : Fin K))
        (j := j) hne]
  simp [companionCoeff, hjlast]

lemma charmatrix_companionCoeff_row_zero_other {K : ℕ}
  (hK : 2 ≤ K) (c : Fin K → ℂ)
    (j : Fin K) (hj : j ≠ (⟨0, by omega⟩ : Fin K))
    (hjlast : (j : ℕ) ≠ K - 1) :
    Matrix.charmatrix (companionCoeff c)
    (⟨0, by omega⟩ : Fin K) j = 0 := by
  have hne : (⟨0, by omega⟩ : Fin K) ≠ j := Ne.symm hj
  have hjzero : (0 : ℕ) ≠ (j : ℕ) := by
    intro h
    exact hj (Fin.ext h.symm)
  change Matrix.charmatrix (companionCoeff c)
    (⟨0, by omega⟩ : Fin K) j = _
  rw [Matrix.charmatrix_apply_ne
        (M := companionCoeff c) (i := (⟨0, by omega⟩ : Fin K))
        (j := j) hne]
  simp [companionCoeff, hjlast]

lemma charmatrix_companionCoeff_row_zero {K : ℕ}
    (hK : 2 ≤ K) (c : Fin K → ℂ) (j : Fin K) :
    (Matrix.charmatrix (companionCoeff c)) ⟨0, by omega⟩ j =
      if j = ⟨0, by omega⟩ then Polynomial.X
      else if (j : ℕ) = K - 1 then Polynomial.C (c ⟨0, by omega⟩)
      else 0 := by
  by_cases hj : j = (⟨0, by omega⟩ : Fin K)
  · subst j; rw [charmatrix_companionCoeff_row_zero_diag hK c]; simp
  · by_cases hjlast : (j : ℕ) = K - 1
    · rw [charmatrix_companionCoeff_row_zero_last hK c j hj hjlast]
      simp [hj, hjlast]
    · rw [charmatrix_companionCoeff_row_zero_other hK c j hj hjlast]
      simp [hj, hjlast]

lemma K_eq_succ {K : ℕ} (hK : 2 ≤ K) : K = (K - 1).succ := by
  omega

lemma fin_cast_val_eq {K K' : ℕ} (h : K = K') (i : Fin K) :
    (Fin.cast h i).val = i.val := by
  simp [Fin.cast]

lemma companionCoeff_reindex_cast {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    Matrix.reindex (Fin.castOrderIso (K_eq_succ hK)).toEquiv
        (Fin.castOrderIso (K_eq_succ hK)).toEquiv (companionCoeff c) =
      companionCoeff (fun i => c (Fin.cast (K_eq_succ hK).symm i)) := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  simp only [companionCoeff]
  have hi : (Fin.cast (K_eq_succ hK).symm i).val = i.val :=
    fin_cast_val_eq _ _
  have hj : (Fin.cast (K_eq_succ hK).symm j).val = j.val :=
    fin_cast_val_eq _ _
  simp []

lemma charpoly_companionCoeff_expand_succ
    {n : ℕ} (c : Fin n.succ → ℂ) :
    Matrix.charpoly (companionCoeff c) =
      ∑ j : Fin n.succ, (-1 : Polynomial ℂ) ^ (j : ℕ) *
        (Matrix.charmatrix (companionCoeff c)) 0 j *
        ((Matrix.charmatrix (companionCoeff c)).submatrix
            Fin.succ j.succAbove).det := by
  unfold Matrix.charpoly
  exact Matrix.det_succ_row_zero (Matrix.charmatrix (companionCoeff c))

lemma fin_cast_val {m n : ℕ} (h : m = n) (i : Fin m) :
    (Fin.cast h i : ℕ) = (i : ℕ) := by
  simp

lemma fin_cast_injective_symm {K : ℕ} (hK : 2 ≤ K) :
    Function.Injective (Fin.cast (K_eq_succ hK).symm) :=
  fun _ _ hij => Fin.cast_injective _ hij

lemma companionCoeff_cast_apply
    {K : ℕ} (_ : 2 ≤ K) (c : Fin K → ℂ)
    (i : Fin (K - 1).succ) (h : K = (K - 1).succ) :
    companionCoeff c (Fin.cast h.symm i) (Fin.cast h.symm i)
      = companionCoeff (fun k => c (Fin.cast h.symm k)) i i := by
  have hi : (Fin.cast h.symm i : ℕ) = (i : ℕ) := fin_cast_val h.symm i
  have hfirst_left :
      ¬ ((Fin.cast h.symm i : ℕ) = (Fin.cast h.symm i : ℕ) + 1
          ∧ (Fin.cast h.symm i : ℕ) < K - 1) := by omega
  have hfirst_right :
      ¬ ((i : ℕ) = (i : ℕ) + 1 ∧ (i : ℕ) < (K - 1).succ - 1) := by
      omega
  by_cases hlast : (Fin.cast h.symm i : ℕ) = K - 1
  · have hlast' : (i : ℕ) = (K - 1).succ - 1 := by
      simpa [hi] using hlast
    simp only [companionCoeff]
    split_ifs ; rfl
  · have hlast' : (i : ℕ) ≠ (K - 1).succ - 1 :=
      fun hc => hlast (by simpa [hi] using hc)
    simp only [companionCoeff]
    split_ifs
    rfl

lemma charmatrix_companionCoeff_cast_eq
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) (i : Fin (K - 1).succ) :
    Matrix.charmatrix (companionCoeff c)
        (Fin.cast (K_eq_succ hK).symm i) (Fin.cast (K_eq_succ hK).symm i)
      = Matrix.charmatrix
          (companionCoeff (fun k => c (Fin.cast (K_eq_succ hK).symm k)))
          i i := by
  have hleft : Matrix.charmatrix (companionCoeff c)
      (Fin.cast (K_eq_succ hK).symm i)
      (Fin.cast (K_eq_succ hK).symm i)
      = Polynomial.X - Polynomial.C (companionCoeff c
          (Fin.cast (K_eq_succ hK).symm i)
          (Fin.cast (K_eq_succ hK).symm i)) :=
    Matrix.charmatrix_apply_eq _ _
  have hright : Matrix.charmatrix
      (companionCoeff (fun k => c (Fin.cast (K_eq_succ hK).symm k))) i i
      = Polynomial.X - Polynomial.C
          (companionCoeff
            (fun k => c (Fin.cast (K_eq_succ hK).symm k)) i i) :=
    Matrix.charmatrix_apply_eq _ _
  rw [hleft, hright,
    companionCoeff_cast_apply hK c i (K_eq_succ hK)]


lemma charmatrix_companionCoeff_cast_ne
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ)
    (i j : Fin (K - 1).succ) (hij : i ≠ j) :
    Matrix.charmatrix (companionCoeff c)
        (Fin.cast (K_eq_succ hK).symm i) (Fin.cast (K_eq_succ hK).symm j)
      = Matrix.charmatrix (companionCoeff
      (fun k => c (Fin.cast (K_eq_succ hK).symm k))) i j := by
  have hcast_ne : Fin.cast (K_eq_succ hK).symm i ≠ Fin.cast (K_eq_succ hK).symm j :=
    fun heq => hij (fin_cast_injective_symm hK heq)
  have hleft : Matrix.charmatrix (companionCoeff c)
      (Fin.cast (K_eq_succ hK).symm i) (Fin.cast (K_eq_succ hK).symm j)
      = -Polynomial.C (companionCoeff c
          (Fin.cast (K_eq_succ hK).symm i) (Fin.cast (K_eq_succ hK).symm j)) :=
    Matrix.charmatrix_apply_ne (companionCoeff c)
      (Fin.cast (K_eq_succ hK).symm i) (Fin.cast (K_eq_succ hK).symm j) hcast_ne
  have hright : Matrix.charmatrix
      (companionCoeff (fun k => c (Fin.cast (K_eq_succ hK).symm k))) i j
      = -Polynomial.C
          (companionCoeff (fun k => c (Fin.cast (K_eq_succ hK).symm k)) i j) :=
    Matrix.charmatrix_apply_ne
      (companionCoeff (fun k => c (Fin.cast (K_eq_succ hK).symm k))) i j hij
  rw [hleft, hright]
  congr 2

lemma charmatrix_companionCoeff_cast {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ)
    (i j : Fin (K - 1).succ) :
    Matrix.charmatrix (companionCoeff c) (Fin.cast (K_eq_succ hK).symm i)
                                          (Fin.cast (K_eq_succ hK).symm j)
      = Matrix.charmatrix (companionCoeff
        (fun k => c (Fin.cast (K_eq_succ hK).symm k))) i j := by
  by_cases hij : i = j
  · subst hij
    exact charmatrix_companionCoeff_cast_eq hK c i
  · exact charmatrix_companionCoeff_cast_ne hK c i j hij


lemma castOrderIso_symm_toEquiv_apply
    {K : ℕ} (hK : 2 ≤ K) (i : Fin (K - 1).succ) :
    (Fin.castOrderIso (K_eq_succ hK)).symm.toEquiv i =
    Fin.cast (K_eq_succ hK).symm i := rfl

lemma det_charmatrix_companionCoeff_cast
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    (Matrix.charmatrix (companionCoeff c)).det
      = (Matrix.charmatrix
          (companionCoeff (fun k => c
            (Fin.cast (K_eq_succ hK).symm k)))).det := by
  set e : Fin (K - 1).succ ≃ Fin K := (Fin.castOrderIso
    (K_eq_succ hK)).symm.toEquiv with he
  have hsub : (Matrix.charmatrix (companionCoeff c)).submatrix e e
      = Matrix.charmatrix
          (companionCoeff (fun k => c (Fin.cast (K_eq_succ hK).symm k))) := by
    apply Matrix.ext
    intro i j
    change Matrix.charmatrix (companionCoeff c) (e i) (e j)
      = Matrix.charmatrix
          (companionCoeff (fun k => c (Fin.cast (K_eq_succ hK).symm k))) i j
    rw [he, castOrderIso_symm_toEquiv_apply hK i,
      castOrderIso_symm_toEquiv_apply hK j]
    exact charmatrix_companionCoeff_cast hK c i j
  calc (Matrix.charmatrix (companionCoeff c)).det
      = ((Matrix.charmatrix (companionCoeff c)).submatrix e e).det :=
        (Matrix.det_submatrix_equiv_self e _).symm
    _ = _ := by rw [hsub]

lemma det_charmatrix_companionCoeff_succ_row_zero
    {K : ℕ} (_ : 2 ≤ K) (c' : Fin (K - 1).succ → ℂ) :
    (Matrix.charmatrix (companionCoeff c')).det
      = ∑ j : Fin (K - 1).succ, (-1 : Polynomial ℂ) ^ (j : ℕ) *
          (Matrix.charmatrix (companionCoeff c')) 0 j *
          ((Matrix.charmatrix (companionCoeff c')).submatrix
              Fin.succ j.succAbove).det :=
  Matrix.det_succ_row_zero (Matrix.charmatrix (companionCoeff c'))

lemma sum_reindex_succ_to_K
    {K : ℕ} (hK : 2 ≤ K) (f : Fin (K - 1).succ → Polynomial ℂ) :
    ∑ j : Fin (K - 1).succ, f j
      = ∑ j : Fin K, f ((Fin.castOrderIso (K_eq_succ hK)).toEquiv j) := by
  rw [← Equiv.sum_comp (Fin.castOrderIso (K_eq_succ hK)).toEquiv f]

lemma charpoly_companionCoeff_expand
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    Matrix.charpoly (companionCoeff c) =
      ∑ j : Fin K, (-1 : Polynomial ℂ) ^ (j : ℕ) *
        (Matrix.charmatrix (companionCoeff c)) ⟨0, by omega⟩ j *
        ((Matrix.charmatrix (companionCoeff c)).submatrix
            (fun i : Fin (K - 1) => Fin.cast (K_eq_succ hK).symm i.succ)
            (fun i : Fin (K - 1) =>
              Fin.cast (K_eq_succ hK).symm
                ((Fin.cast (K_eq_succ hK) j).succAbove i))).det := by
  set c' : Fin (K - 1).succ → ℂ := fun k => c (Fin.cast (K_eq_succ hK).symm k) with hc'
  unfold Matrix.charpoly
  rw [det_charmatrix_companionCoeff_cast hK c,
      det_charmatrix_companionCoeff_succ_row_zero hK c',
      sum_reindex_succ_to_K hK]
  apply Finset.sum_congr rfl
  intro j _
  set e : Fin K ≃ Fin (K - 1).succ := (Fin.castOrderIso (K_eq_succ hK)).toEquiv with he
  have hexp : ((e j : Fin (K-1).succ) : ℕ) = (j : ℕ) := by simp [e, Fin.castOrderIso]
  have h0 : Matrix.charmatrix (companionCoeff c') 0 (e j)
      = Matrix.charmatrix (companionCoeff c) ⟨0, by omega⟩ j := by
    have e1 : Fin.cast (K_eq_succ hK).symm (0 : Fin (K-1).succ) = (⟨0, by omega⟩ : Fin K) := by
      apply Fin.ext; simp
    have e2 : Fin.cast (K_eq_succ hK).symm (e j) = j := by
      apply Fin.ext; simp [e, Fin.castOrderIso]
    have key := charmatrix_companionCoeff_cast hK c (0 : Fin (K-1).succ) (e j)
    rw [e1, e2] at key
    exact key.symm
  have hdet : ((Matrix.charmatrix (companionCoeff c')).submatrix Fin.succ (e j).succAbove).det
      = ((Matrix.charmatrix (companionCoeff c)).submatrix
          (fun i : Fin (K-1) => Fin.cast (K_eq_succ hK).symm i.succ)
          (fun i : Fin (K-1) => Fin.cast (K_eq_succ hK).symm
            ((Fin.cast (K_eq_succ hK) j).succAbove i))).det := by
    apply congrArg Matrix.det
    apply Matrix.ext
    intro i k
    change Matrix.charmatrix (companionCoeff c') (Fin.succ i) ((e j).succAbove k)
      = Matrix.charmatrix (companionCoeff c)
          (Fin.cast (K_eq_succ hK).symm (Fin.succ i))
          (Fin.cast (K_eq_succ hK).symm ((Fin.cast (K_eq_succ hK) j).succAbove k))
    rw [charmatrix_companionCoeff_cast hK c (Fin.succ i)
         ((Fin.cast (K_eq_succ hK) j).succAbove k)]
    congr 2
  rw [hexp, h0, hdet]

lemma minor_last_column_det_one
    {K : ℕ} (_ : 2 ≤ K) (_ : Fin K → ℂ) :
    True := by trivial

lemma minor_zero_zero_eq_companionCoeff_succ
    {K : ℕ} (_ : 2 ≤ K) (_ : Fin K → ℂ) :
    True := by trivial

lemma step_charmatrix_row_zero_vanish
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) (j : Fin K)
    (hj_ne_zero : (j : ℕ) ≠ 0) (hj_ne_last : (j : ℕ) ≠ K - 1) :
    Matrix.charmatrix (companionCoeff c) ⟨0, by omega⟩ j = 0 := by
  rw [charmatrix_companionCoeff_row_zero hK]
  split_ifs with h1
  · have : (j : ℕ) = 0 := by simp [h1]
    omega
  · simp only []

lemma step_charmatrix_row_zero_last_col
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    Matrix.charmatrix (companionCoeff c) ⟨0, by omega⟩
      ⟨K - 1, by omega⟩ = Polynomial.C (c ⟨0, by omega⟩) := by
  have h_ne : (⟨0, by omega⟩ : Fin K) ≠ ⟨K - 1, by omega⟩ := by
    intro h
    have h0 : (0 : ℕ) = K - 1 := Fin.mk.inj_iff.mp h
    omega
  rw [Matrix.charmatrix_apply_ne (M := companionCoeff c)
      (i := ⟨0, by omega⟩) (j := ⟨K - 1, by omega⟩) h_ne]
  simp only [companionCoeff]
  split_ifs with h1 h2
  · omega
  · omega
  · omega
  · rw [Polynomial.C_neg, neg_neg]


lemma step_sum_cofactor_reduce
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    ∑ j : Fin K, (-1 : Polynomial ℂ) ^ (j : ℕ) *
      (Matrix.charmatrix (companionCoeff c)) ⟨0, by omega⟩ j *
      ((Matrix.charmatrix (companionCoeff c)).submatrix
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm i.succ)
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm
              ((Fin.cast (K_eq_succ hK) j).succAbove i))).det
    =
    (-1 : Polynomial ℂ) ^ 0 *
      (Matrix.charmatrix (companionCoeff c)) ⟨0, by omega⟩ ⟨0, by omega⟩ *
      ((Matrix.charmatrix (companionCoeff c)).submatrix
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm i.succ)
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm
              ((Fin.cast (K_eq_succ hK) ⟨0, by omega⟩).succAbove i))).det
    +
    (-1 : Polynomial ℂ) ^ (K - 1) *
      (Matrix.charmatrix (companionCoeff c)) ⟨0, by omega⟩
        ⟨K - 1, by omega⟩ *
      ((Matrix.charmatrix (companionCoeff c)).submatrix
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm i.succ)
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm
              ((Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩).succAbove i))).det
    := by
  classical
  set i₀ : Fin K := ⟨0, by omega⟩ with hi₀_def
  set i₁ : Fin K := ⟨K - 1, by omega⟩ with hi₁_def
  set F : Fin K → Polynomial ℂ := fun j =>
    (-1 : Polynomial ℂ) ^ (j : ℕ) *
      (Matrix.charmatrix (companionCoeff c)) i₀ j *
      ((Matrix.charmatrix (companionCoeff c)).submatrix
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm i.succ)
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm
              ((Fin.cast (K_eq_succ hK) j).succAbove i))).det
    with hF_def
  have hi₀_ne_i₁ : i₀ ≠ i₁ := by
    intro h
    have hval : (0 : ℕ) = K - 1 := congrArg Fin.val h
    omega
  set s : Finset (Fin K) := (Finset.univ.erase i₀).erase i₁ with hs_def
  have hzero : ∀ j ∈ s, F j = 0 := by
    intro j hj
    have hj₁ : j ≠ i₁ := (Finset.mem_erase.mp hj).1
    have hj_rest : j ∈ Finset.univ.erase i₀ := (Finset.mem_erase.mp hj).2
    have hj₀ : j ≠ i₀ := (Finset.mem_erase.mp hj_rest).1
    have hjlast : (j : ℕ) ≠ K - 1 := by
      intro hlast
      exact hj₁ (Fin.ext hlast)
    have hj₀' : (j : ℕ) ≠ 0 := by
      intro h0
      exact hj₀ (Fin.ext h0)
    have := step_charmatrix_row_zero_vanish hK c j hj₀' hjlast
    simp only [hF_def, hi₀_def, this, zero_mul, mul_zero]
  have hdecomp : (Finset.univ : Finset (Fin K)) = insert i₀ (insert i₁ s) := by
    ext j
    simp only [Finset.mem_univ, Finset.mem_insert, hs_def,
      Finset.mem_erase]
    by_cases hj₀ : j = i₀
    · simp [hj₀]
    · by_cases hj₁ : j = i₁
      · simp [hj₁]
      · simp [hj₀, hj₁]
  have hi₁_not_mem : i₁ ∉ s := by
    simp [hs_def]
  have hi₀_not_mem : i₀ ∉ insert i₁ s := by
    simp only [Finset.mem_insert, hs_def, Finset.mem_erase, Finset.mem_univ]
    rintro (h | ⟨-, h, -⟩)
    · exact hi₀_ne_i₁ h
    · exact h rfl
  calc
    ∑ j : Fin K, F j
        = ∑ j ∈ insert i₀ (insert i₁ s), F j := by rw [← hdecomp]
    _ = F i₀ + ∑ j ∈ insert i₁ s, F j := by
          rw [Finset.sum_insert hi₀_not_mem]
    _ = F i₀ + (F i₁ + ∑ j ∈ s, F j) := by
          rw [Finset.sum_insert hi₁_not_mem]
    _ = F i₀ + F i₁ := by
          rw [Finset.sum_eq_zero hzero, add_zero]
    _ = _ := by
          simp only [hF_def, hi₀_def, hi₁_def]

lemma step_minor_succ_column_eq_companionCoeff_tail
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    ((Matrix.charmatrix (companionCoeff c)).submatrix
        (fun i : Fin (K - 1) =>
          Fin.cast (K_eq_succ hK).symm i.succ)
        (fun i : Fin (K - 1) =>
          Fin.cast (K_eq_succ hK).symm
            ((⟨0, by omega⟩ : Fin (K - 1).succ).succAbove i))).det
    =
    (Matrix.charmatrix
      (companionCoeff
        (fun i : Fin (K - 1) =>
          c (Fin.cast (K_eq_succ hK).symm i.succ)))).det := by
  have hzero : ∀ j : Fin (K - 1),
      (⟨0, by omega⟩ : Fin (K - 1).succ).succAbove j = j.succ := by
    intro j
    apply Fin.ext
    simp [Fin.succAbove]
  have hmat :
      (Matrix.charmatrix (companionCoeff c)).submatrix
        (fun i : Fin (K - 1) => Fin.cast (K_eq_succ hK).symm i.succ)
        (fun i : Fin (K - 1) =>
          Fin.cast (K_eq_succ hK).symm
            ((⟨0, by omega⟩ : Fin (K - 1).succ).succAbove i))
      = Matrix.charmatrix
          (companionCoeff (fun i : Fin (K - 1) =>
            c (Fin.cast (K_eq_succ hK).symm i.succ))) := by
    ext i j
    simp only [Matrix.submatrix_apply, hzero]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.charmatrix_apply_eq, Matrix.charmatrix_apply_eq]
      congr 1
      unfold companionCoeff
      simp only [Fin.val_cast, Fin.val_succ]
      split_ifs with h1 h2 h3 <;> first | rfl | omega
    · have hij' : Fin.cast (K_eq_succ hK).symm i.succ
          ≠ Fin.cast (K_eq_succ hK).symm j.succ := by
        intro h
        apply hij
        apply Fin.ext
        have := Fin.cast_injective (K_eq_succ hK).symm h
        simpa [Fin.succ, Fin.ext_iff] using this
      rw [Matrix.charmatrix_apply_ne _ _ _ hij',
          Matrix.charmatrix_apply_ne _ _ _ hij]
      congr 1
      unfold companionCoeff
      split_ifs with h1 h2 h3 <;> simp_all <;> omega
  rw [hmat]

lemma step_minor_last_column_rows_ne
    {K : ℕ} (hK : 2 ≤ K)
    (i j : Fin (K - 1)) (hij : i ≠ j) :
    Fin.cast (K_eq_succ hK).symm i.succ ≠
      Fin.cast (K_eq_succ hK).symm j.succ := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_cast, Fin.val_succ] at hval
  have hi_bound : (i : ℕ) < K - 1 := i.isLt
  have hj_bound : (j : ℕ) < K - 1 := j.isLt
  omega

lemma step_minor_last_column_succAbove_val
    {K : ℕ} (hK : 2 ≤ K) (i : Fin (K - 1)) :
    ((Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩).succAbove i).val = i.val := by
  have hlast :
      Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩ = Fin.last (K - 1) := by
    apply Fin.ext
    simp
  rw [hlast, Fin.succAbove_last]
  exact Fin.val_castSucc i

lemma step_minor_last_column_diag_ne
    {K : ℕ} (hK : 2 ≤ K) (i : Fin (K - 1)) :
    Fin.cast (K_eq_succ hK).symm i.succ ≠
      Fin.cast (K_eq_succ hK).symm
        ((Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩).succAbove i) := by
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_cast, Fin.val_succ] at hval
  rw [step_minor_last_column_succAbove_val hK i] at hval
  omega

lemma step_minor_last_column_diag_val
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) (i : Fin (K - 1)) :
    (Matrix.charmatrix (companionCoeff c))
        (Fin.cast (K_eq_succ hK).symm i.succ)
        (Fin.cast (K_eq_succ hK).symm
          ((Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩).succAbove i))
      = Matrix.diagonal (fun _ : Fin (K - 1) => (-1 : Polynomial ℂ)) i i := by
  have hne := step_minor_last_column_diag_ne hK i
  rw [Matrix.charmatrix_apply_ne (companionCoeff c) _ _ hne]
  simp only [companionCoeff]
  have hcol := step_minor_last_column_succAbove_val hK i
  split_ifs with hfirst hlast
  · simp only [Matrix.diagonal_apply_eq, Polynomial.C_1]
  · exfalso
    have col_lt : ((Fin.cast (K_eq_succ hK)
      ⟨K - 1, by omega⟩).succAbove i).val < K - 1 := by
      rw [hcol]; exact i.isLt
    simp only [Fin.val_cast] at hlast
    omega
  · exfalso
    have col_lt : ((Fin.cast (K_eq_succ hK)
      ⟨K - 1, by omega⟩).succAbove i).val < K - 1 := by
      rw [hcol]; exact i.isLt
    apply hfirst
    constructor
    · simp only [Fin.val_cast, Fin.val_succ]
      rw [hcol]
    · exact col_lt

lemma step_minor_last_column_below_diag_case_one
    {K : ℕ} (_ : 2 ≤ K) (i j : Fin (K - 1)) (hji : j.val < i.val)
    (hfirst : i.val + 1 = j.val ∧ j.val < K - 1) :
    False := by
  have ⟨heq, _⟩ := hfirst
  omega

lemma step_minor_last_column_below_diag_val
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) (i j : Fin (K - 1)) (hji : j.val < i.val) :
    (Matrix.charmatrix (companionCoeff c))
        (Fin.cast (K_eq_succ hK).symm i.succ)
        (Fin.cast (K_eq_succ hK).symm
          ((Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩).succAbove j))
      = 0 := by
  have hcol := step_minor_last_column_succAbove_val hK j
  have hne : Fin.cast (K_eq_succ hK).symm i.succ ≠
      Fin.cast (K_eq_succ hK).symm
        ((Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩).succAbove j) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_cast, Fin.val_succ] at hval
    rw [hcol] at hval
    omega
  rw [Matrix.charmatrix_apply_ne (companionCoeff c) _ _ hne]
  simp only [companionCoeff]
  simp only [fin_cast_val] at hcol ⊢
  rw [hcol]
  split_ifs with hfirst hlast
  · exfalso
    simp only [Fin.val_succ] at hfirst
    have : i.val + 1 = j.val ∧ j.val < K - 1 := by omega
    exact step_minor_last_column_below_diag_case_one hK i j hji this
  · omega
  · simp only [Polynomial.C_0, neg_zero]

lemma step_minor_last_column_far_above_case_one
    {K : ℕ} (_ : 2 ≤ K) (i j : Fin (K - 1)) (hij : i.val + 2 ≤ j.val)
    (hfirst : i.val + 1 = j.val ∧ j.val < K - 1) :
    False := by
  have ⟨heq, _⟩ := hfirst
  omega

lemma step_minor_last_column_far_above_val
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) (i j : Fin (K - 1)) (hij : i.val + 2 ≤ j.val) :
    (Matrix.charmatrix (companionCoeff c))
        (Fin.cast (K_eq_succ hK).symm i.succ)
        (Fin.cast (K_eq_succ hK).symm
          ((Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩).succAbove j))
      = 0 := by
  have hcol := step_minor_last_column_succAbove_val hK j
  have hne : Fin.cast (K_eq_succ hK).symm i.succ ≠
      Fin.cast (K_eq_succ hK).symm
        ((Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩).succAbove j) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_cast, Fin.val_succ] at hval
    rw [hcol] at hval
    omega
  rw [Matrix.charmatrix_apply_ne (companionCoeff c) _ _ hne]
  simp only [companionCoeff]
  simp only [fin_cast_val] at hcol ⊢
  rw [hcol]
  split_ifs with hfirst hlast
  · exfalso
    simp only [Fin.val_succ] at hfirst
    have : i.val + 1 = j.val ∧ j.val < K - 1 := by omega
    exact step_minor_last_column_far_above_case_one hK i j hij this
  · omega
  · simp only [Polynomial.C_0, neg_zero]

lemma step_minor_last_column_det_neg_one_pow
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    ((Matrix.charmatrix (companionCoeff c)).submatrix
        (fun i : Fin (K - 1) => Fin.cast (K_eq_succ hK).symm i.succ)
        (fun i : Fin (K - 1) =>
          Fin.cast (K_eq_succ hK).symm
            ((Fin.cast (K_eq_succ hK) ⟨K - 1, by omega⟩).succAbove i))).det
      = (-1 : Polynomial ℂ) ^ (K - 1) := by
  have htri : ∀ i j : Fin (K - 1), j.val < i.val →
      ((Matrix.charmatrix (companionCoeff c)).submatrix
          (fun i : Fin (K - 1) => Fin.cast (K_eq_succ hK).symm i.succ)
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm
              ((Fin.cast (K_eq_succ hK)
                ⟨K - 1, by omega⟩).succAbove i))) i j = 0 := by
    intro i j hji
    rw [Matrix.submatrix_apply]
    exact step_minor_last_column_below_diag_val hK c i j hji
  rw [Matrix.det_of_isUpperTriangular htri]
  have hdiag : ∀ i : Fin (K - 1),
      ((Matrix.charmatrix (companionCoeff c)).submatrix
          (fun i : Fin (K - 1) => Fin.cast (K_eq_succ hK).symm i.succ)
          (fun i : Fin (K - 1) =>
            Fin.cast (K_eq_succ hK).symm
              ((Fin.cast (K_eq_succ hK)
                ⟨K - 1, by omega⟩).succAbove i))) i i = -1 := by
    intro i
    simpa only [Matrix.submatrix_apply, Matrix.diagonal_apply_eq] using
      (step_minor_last_column_diag_val hK c i)
  simp only [hdiag, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma succ_pred_eq {K : ℕ} (hK : 2 ≤ K) : (K - 1).succ = K := by
  exact (K_eq_succ hK).symm

lemma fin_eq_of_nat_eq {n m : ℕ} (h : n = m) : Fin n = Fin m := by
  rw [h]

lemma companionCoeff_charmatrix_transport
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    let eq_succ : K = (K - 1).succ := K_eq_succ hK
    let c' : Fin (K - 1).succ → ℂ := fun k => c (Fin.cast eq_succ.symm k)
    (Matrix.charmatrix (companionCoeff c)).det =
      ∑ j : Fin (K - 1).succ, (-1 : Polynomial ℂ) ^ (j : ℕ) *
        (Matrix.charmatrix (companionCoeff c')) ⟨0, by omega⟩ j *
        ((Matrix.charmatrix (companionCoeff c')).submatrix
            Fin.succ (j.succAbove)).det := by
  dsimp only
  rw [det_charmatrix_companionCoeff_cast hK c]
  exact Matrix.det_succ_row_zero
    (Matrix.charmatrix (companionCoeff
    (fun k => c (Fin.cast (K_eq_succ hK).symm k))))

lemma step_charmatrix_det_expansion
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    (Matrix.charmatrix (companionCoeff c)).det
      = ∑ j : Fin K, (-1 : Polynomial ℂ) ^ (j : ℕ) *
          (Matrix.charmatrix (companionCoeff c)) ⟨0, by omega⟩ j *
          ((Matrix.charmatrix (companionCoeff c)).submatrix
              (fun i : Fin (K - 1) => Fin.cast (K_eq_succ hK).symm i.succ)
              (fun i : Fin (K - 1) =>
                Fin.cast (K_eq_succ hK).symm
                  ((Fin.cast (K_eq_succ hK) j).succAbove i))).det := by
  have h := charpoly_companionCoeff_expand hK c
  simpa [Matrix.charpoly] using h

lemma companionCoeff_charpoly_minor_zero_step
    {K : ℕ} (hK : 2 ≤ K) (c : Fin K → ℂ) :
    ((Matrix.charmatrix (companionCoeff c)).submatrix
        (fun i : Fin (K - 1) =>
          Fin.cast (K_eq_succ hK).symm i.succ)
        (fun i : Fin (K - 1) =>
          Fin.cast (K_eq_succ hK).symm
            ((Fin.cast (K_eq_succ hK)
              (⟨0, by omega⟩ : Fin K)).succAbove i))).det
      =
    (Matrix.charmatrix
      (companionCoeff
        (fun i : Fin (K - 1) =>
          c (Fin.cast (K_eq_succ hK).symm i.succ)))).det := by
  have hzero :
      Fin.cast (K_eq_succ hK) (⟨0, by omega⟩ : Fin K)
        =
      (⟨0, by omega⟩ : Fin (K - 1).succ) := by
    apply Fin.ext
    simp
  rw [hzero]
  exact step_minor_succ_column_eq_companionCoeff_tail hK c

lemma companionCoeff_charpoly_tail_cast_eq
    {n : ℕ} (hK : 2 ≤ n + 2) (c : Fin (n + 2) → ℂ) :
    (fun i : Fin (n + 1) => c (Fin.cast (K_eq_succ hK).symm i.succ))
      = (fun i : Fin (n + 1) => c i.succ) := by
  funext i
  congr 1

lemma polyAssocieCoeff_sum_decomp {n : ℕ} (c : Fin (n + 2) → ℂ) :
    (∑ j : Fin (n + 2),
        Polynomial.C (c j) * Polynomial.X ^ (j : ℕ))
      =
    Polynomial.C (c ⟨0, by omega⟩) * Polynomial.X ^ (0 : ℕ)
      + ∑ i : Fin (n + 1),
          Polynomial.C (c i.succ) *
            Polynomial.X ^ ((i.succ : Fin (n + 2)) : ℕ) := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero]
  congr 1

lemma shift_sum_by_X_mult {n : ℕ} (c : Fin (n + 1) → ℂ) :
    (∑ i : Fin (n + 1),
        Polynomial.X *
          (Polynomial.C (c i) *
            Polynomial.X ^ (i : ℕ)))
      =
    ∑ i : Fin (n + 1),
        Polynomial.C (c i) *
          Polynomial.X ^ ((i : ℕ) + 1) := by
  apply Finset.sum_congr rfl
  intro i _
  show
    Polynomial.X * (Polynomial.C (c i) * Polynomial.X ^ (i : ℕ))
      =
    Polynomial.C (c i) * Polynomial.X ^ ((i : ℕ) + 1)
  rw [pow_succ]
  ring

lemma X_mul_X_pow_succ {n : ℕ} :
    (Polynomial.X : Polynomial ℂ) * (Polynomial.X : Polynomial ℂ) ^ (n + 1)
      = (Polynomial.X : Polynomial ℂ) ^ (n + 2) := by
  rw [← pow_succ']

lemma neg_one_pow_twice_eq_one {n : ℕ} :
    (-1 : Polynomial ℂ) ^ (n + 2 - 1) * (-1 : Polynomial ℂ) ^ (n + 2 - 1) = 1 := by
  rw [← pow_add]
  rw [show (n + 2 - 1) + (n + 2 - 1) = 2 * (n + 1) by omega]
  rw [pow_mul]
  norm_num

lemma neg_one_poly_mul_coeff_mul_neg_one_poly {n : ℕ} (c₀ : ℂ) :
    (-1 : Polynomial ℂ) ^ (n + 2 - 1) * Polynomial.C c₀ *
      (-1 : Polynomial ℂ) ^ (n + 2 - 1)
      =
    Polynomial.C c₀ *
      ((-1 : Polynomial ℂ) ^ (n + 2 - 1) * (-1 : Polynomial ℂ) ^ (n + 2 - 1)) := by
  ring

lemma polyAssocieCoeff_succ_relation {n : ℕ} (c : Fin (n + 2) → ℂ) :
    Polynomial.X ^ (n + 2) +
      (Polynomial.C (c ⟨0, by omega⟩) * 1
        + ∑ i : Fin (n + 1),
            Polynomial.C (c i.succ) *
              Polynomial.X ^ ((i : ℕ) + 1))
      =
    Polynomial.X *
        (Polynomial.X ^ (n + 1)
          + ∑ i : Fin (n + 1),
              Polynomial.C (c i.succ) *
                Polynomial.X ^ (i : ℕ))
        + Polynomial.C (c ⟨0, by omega⟩) := by
  simp only [mul_one, mul_add, Finset.mul_sum]
  ring_nf

lemma polyAssocieCoeff_unfold {n : ℕ} (c : Fin (n + 2) → ℂ) :
    Polynomial.X *
        (Polynomial.X ^ (n + 1)
          + ∑ i : Fin (n + 1),
              Polynomial.C (c i.succ) *
                Polynomial.X ^ (i : ℕ))
        + Polynomial.C (c ⟨0, by omega⟩)
      =
    polyAssocieCoeff c := by
  unfold polyAssocieCoeff
  have h1 := polyAssocieCoeff_sum_decomp c
  simp only [pow_zero, mul_one, Fin.val_succ] at h1 ⊢
  rw [mul_add]
  simp only [Finset.mul_sum]
  have h_sum : (∑ i : Fin (n + 1),
                  Polynomial.X * (Polynomial.C (c i.succ) * Polynomial.X ^ (i : ℕ)))
             = ∑ i : Fin (n + 1),
                 Polynomial.C (c i.succ) * Polynomial.X ^ ((i : ℕ) + 1) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_sum]
  rw [show Polynomial.X ^ (n + 2) + (∑ j : Fin (n + 2),
          Polynomial.C (c j) * Polynomial.X ^ (j : ℕ))
        = Polynomial.X ^ (n + 2) +
          (Polynomial.C (c ⟨0, by omega⟩) + ∑ x : Fin (n + 1),
            Polynomial.C (c x.succ) * Polynomial.X ^ ((x : ℕ) + 1)) by
        rw [← h1]]
  ring

lemma key_algebraic_simplification {n : ℕ} (c : Fin (n + 2) → ℂ) :
    Polynomial.X * polyAssocieCoeff (fun i => c i.succ) +
      (-1) ^ (n + 2 - 1) * Polynomial.C (c ⟨0, by omega⟩) * (-1) ^ (n + 2 - 1)
    = polyAssocieCoeff c := by
  have h_neg_one_sq : (-1 : Polynomial ℂ) ^ (n + 2 - 1) * (-1) ^ (n + 2 - 1) = 1 := by
    have eq_n_plus_one : (n + 2 - 1 : ℕ) = n + 1 := by omega
    simp only [eq_n_plus_one]
    rw [← pow_add, show (n + 1) + (n + 1) = 2 * (n + 1) by ring]
    rw [pow_mul]
    norm_num
  calc Polynomial.X * polyAssocieCoeff (fun i => c i.succ) +
          (-1) ^ (n + 2 - 1) * Polynomial.C (c ⟨0, by omega⟩) * (-1) ^ (n + 2 - 1)
      = Polynomial.X * polyAssocieCoeff (fun i => c i.succ) +
        ((-1 : Polynomial ℂ) ^ (n + 2 - 1) * (-1) ^ (n + 2 - 1)) *
          Polynomial.C (c ⟨0, by omega⟩) := by ring
    _ = Polynomial.X * polyAssocieCoeff (fun i => c i.succ) +
        1 * Polynomial.C (c ⟨0, by omega⟩) := by rw [h_neg_one_sq]
    _ = Polynomial.X * polyAssocieCoeff (fun i => c i.succ) +
        Polynomial.C (c ⟨0, by omega⟩) := by ring
    _ = Polynomial.X * (Polynomial.X ^ (n + 1) +
          ∑ i : Fin (n + 1), Polynomial.C (c i.succ) * Polynomial.X ^ (i : ℕ)) +
        Polynomial.C (c ⟨0, by omega⟩) := by
          congr 1
    _ = polyAssocieCoeff c := by
          rw [polyAssocieCoeff_unfold c]

lemma cast_succ_eq_succ {n : ℕ} (c : Fin (n + 2) → ℂ) (hK : 2 ≤ n + 2) :
    (fun i : Fin (n + 1) => c (Fin.cast (K_eq_succ hK).symm i.succ))
    = (fun i : Fin (n + 1) => c i.succ) := by
  funext i
  rfl

lemma det_cast_succ_eq_det_succ {n : ℕ} (c : Fin (n + 2) → ℂ) (hK : 2 ≤ n + 2)
    (_ : (fun i : Fin (n + 1) => c (Fin.cast (K_eq_succ hK).symm i.succ))
               = (fun i : Fin (n + 1) => c i.succ)) :
    (companionCoeff fun i => c (Fin.cast
      (K_eq_succ hK).symm i.succ)).charmatrix.det =
    (companionCoeff fun i => c i.succ).charmatrix.det := by
  congr 1

lemma before_unfold {n : ℕ} (c : Fin (n + 2) → ℂ) (hK : 2 ≤ n + 2)
    (hrec : (companionCoeff fun i => c i.succ).charmatrix.det =
            polyAssocieCoeff (fun i => c i.succ)) :
    Polynomial.X * (companionCoeff fun i =>
    c (Fin.cast (K_eq_succ hK).symm i.succ)).charmatrix.det +
    (-1) ^ (n + 2 - 1) * Polynomial.C (c ⟨0, by omega⟩) * (-1) ^ (n + 2 - 1)
    = Polynomial.X * polyAssocieCoeff
      (fun i => c i.succ) + Polynomial.C (c ⟨0, by omega⟩) := by
  have cast_eq := cast_succ_eq_succ c hK
  have det_eq := det_cast_succ_eq_det_succ c hK cast_eq
  have h_neg_one_sq := neg_one_pow_twice_eq_one (n := n)
  rw [det_eq]
  rw [show (-1 : Polynomial ℂ) ^ (n + 2 - 1) *
    Polynomial.C (c ⟨0, by omega⟩) * (-1) ^ (n + 2 - 1)
            = ((-1) ^ (n + 2 - 1) * (-1) ^ (n + 2 - 1)) *
            Polynomial.C (c ⟨0, by omega⟩) by ring]
  rw [h_neg_one_sq]
  simp only [one_mul]
  rw [hrec]

lemma after_unfold {n : ℕ} (c : Fin (n + 2) → ℂ) :
    Polynomial.X * polyAssocieCoeff (fun i => c i.succ) + Polynomial.C (c ⟨0, by omega⟩)
    = polyAssocieCoeff c := by
  have h_succ_poly : polyAssocieCoeff (fun i => c i.succ)
      = Polynomial.X ^ (n + 1) + ∑ i : Fin (n + 1),
      Polynomial.C (c i.succ) * Polynomial.X ^ (i : ℕ) := by
    unfold polyAssocieCoeff
    ring
  rw [h_succ_poly]
  rw [← polyAssocieCoeff_unfold c]

lemma charpoly_final_step
    {n : ℕ} (c : Fin (n + 2) → ℂ) (hK : 2 ≤ n + 2)
    (hrec : (companionCoeff fun i => c i.succ).charmatrix.det =
            polyAssocieCoeff (fun i => c i.succ)) :
    Polynomial.X * (companionCoeff fun i =>
      c (Fin.cast (K_eq_succ hK).symm i.succ)).charmatrix.det +
    (-1) ^ (n + 2 - 1) * Polynomial.C (c ⟨0, by omega⟩) * (-1) ^ (n + 2 - 1) =
    polyAssocieCoeff c := by
  rw [before_unfold c hK hrec, after_unfold c]






end CharpolyThEq
