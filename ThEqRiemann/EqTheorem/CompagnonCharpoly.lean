import mathlib
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.Charpoly

/-! -/
namespace CompagnonCharpolyThEq

open Set Complex Matrix DefinitionsThEq CharpolyThEq

theorem companionCoeff_charpoly
    {K : ℕ} (c : Fin K → ℂ) :
    Matrix.charpoly (companionCoeff c) = polyAssocieCoeff c := by
  induction K using Nat.strong_induction_on with
  | _ K ih =>
    match K, ih with
    | 0, _ => exact companionCoeff_charpoly_zero c
    | 1, _ => exact companionCoeff_charpoly_one c
    | (n+2), ih =>
        have hK : 2 ≤ n + 2 := by omega
        rw [Matrix.charpoly]
        rw [step_charmatrix_det_expansion hK c]
        rw [step_sum_cofactor_reduce hK c]
        simp only [pow_zero, one_mul]
        have h_zero_zero :
            Matrix.charmatrix (companionCoeff c)
            ⟨0, by omega⟩ ⟨0, by omega⟩ = Polynomial.X :=
          charmatrix_companionCoeff_row_zero_diag hK c
        rw [h_zero_zero]
        rw [companionCoeff_charpoly_minor_zero_step hK c]
        have h_last := step_charmatrix_row_zero_last_col hK c
        rw [h_last]
        have h_minor_power := step_minor_last_column_det_neg_one_pow hK c
        rw [h_minor_power]
        have hrec : Matrix.charpoly (companionCoeff (fun i => c i.succ))
                  = polyAssocieCoeff (fun i => c i.succ) :=
          ih (n + 1) (by omega) (fun i => c i.succ)
        rw [Matrix.charpoly] at hrec
        rw [charpoly_final_step c hK hrec]

lemma companion'_eq_companionCoeff {K : ℕ} (lam : Fin K → ℂ) :
    companion' lam = companionCoeff (fun i => (polyAssocie lam).coeff (i : ℕ)) := by
  funext i j
  simp [companion', companionCoeff]

lemma polyAssocie_monic {K : ℕ} (lam : Fin K → ℂ) :
    (polyAssocie lam).Monic := by
  unfold polyAssocie
  exact Polynomial.monic_prod_of_monic _ _ (by
    intro i hi
    exact Polynomial.monic_X_sub_C _)

lemma polyAssocie_natDegree {K : ℕ} (lam : Fin K → ℂ) :
    (polyAssocie lam).natDegree = K := by
  unfold polyAssocie
  rw [Polynomial.natDegree_prod_of_monic]
  · simp []
  · intro i hi
    exact Polynomial.monic_X_sub_C _

lemma polyAssocie_eq_X_pow_add_coeff_sum {K : ℕ} (lam : Fin K → ℂ) :
    polyAssocie lam =
      Polynomial.X ^ K +
        ∑ j : Fin K,
          Polynomial.C ((polyAssocie lam).coeff (j : ℕ)) *
            Polynomial.X ^ (j : ℕ) := by
  calc
    polyAssocie lam = Polynomial.X ^ K +
        ∑ j ∈ Finset.range K,
          Polynomial.C
          ((polyAssocie lam).coeff j) * Polynomial.X ^ j := by
      simpa [polyAssocie_natDegree lam] using
        (polyAssocie_monic lam).as_sum
    _ = Polynomial.X ^ K +
        ∑ j : Fin K,
          Polynomial.C ((polyAssocie lam).coeff (j : ℕ)) *
            Polynomial.X ^ (j : ℕ) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun j => Polynomial.C
          ((polyAssocie lam).coeff j) * Polynomial.X ^ j) K]

lemma polyAssocie_eq_polyAssocieCoeff_of_coeff
    {K : ℕ} (lam : Fin K → ℂ) :
    polyAssocie lam = polyAssocieCoeff (fun (i : Fin K) =>
      (polyAssocie lam).coeff (i : ℕ)) := by
  unfold polyAssocieCoeff
  exact polyAssocie_eq_X_pow_add_coeff_sum lam


theorem companion'_charpoly {K : ℕ} (lam : Fin K → ℂ) :
    Matrix.charpoly (companion' lam) = polyAssocie lam := by
  calc Matrix.charpoly (companion' lam)
    _ = Matrix.charpoly (companionCoeff
      (fun i => (polyAssocie lam).coeff (i : ℕ))) := by
        rw [companion'_eq_companionCoeff]
    _ = polyAssocieCoeff (fun i => (polyAssocie lam).coeff (i : ℕ)) := by
        rw [companionCoeff_charpoly]
    _ = polyAssocie lam := by
        exact (polyAssocie_eq_polyAssocieCoeff_of_coeff lam).symm


-------------------------------------------------------------------------------------

lemma polyAssocie_eval_root {K : ℕ} (lam : Fin K → ℂ) (r : Fin K) :
    (polyAssocie lam).eval (lam r) = 0 := by
  unfold polyAssocie
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  simp

lemma root_power_relation {K : ℕ} (lam : Fin K → ℂ) (r : Fin K) :
    (lam r) ^ K +
      ∑ j : Fin K,
        (polyAssocie lam).coeff (j : ℕ) * (lam r) ^ (j : ℕ) = 0 := by
  have h := polyAssocie_eval_root lam r
  rw [polyAssocie_eq_polyAssocieCoeff_of_coeff] at h
  unfold polyAssocieCoeff at h
  rw [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X] at h
  exact h

lemma root_power_relation_mul_aux {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℂ)
    (k : ℕ) (r : Fin K) :
    w r * (lam r) ^ (K + k) +
      ∑ i : Fin K,
        (polyAssocie lam).coeff (i : ℕ) * (lam r) ^
        (i : ℕ) * (w r * (lam r) ^ k) = 0 := by
  have h := root_power_relation lam r
  have h2 := congrArg (fun z : ℂ => z * (w r * (lam r) ^ k)) h
  simp only [zero_mul] at h2
  rw [add_mul, Finset.sum_mul] at h2
  rw [show (lam r) ^ K * (w r * (lam r) ^ k) = w r * (lam r) ^ (K + k) by
        rw [pow_add]; ring] at h2
  exact h2

lemma root_power_relation_term_rewrite {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℂ)
    (k : ℕ) (r : Fin K) (j : Fin K) :
    (polyAssocie lam).coeff (j : ℕ) * (lam r) ^ (j : ℕ) * (w r * (lam r) ^ k)
      = (polyAssocie lam).coeff (j : ℕ) * (w r * (lam r) ^ ((j : ℕ) + k)) := by
  rw [pow_add]
  ring

lemma root_power_relation_sum_rewrite
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℂ)
    (k : ℕ) (r : Fin K) :
    (∑ i : Fin K, (polyAssocie lam).coeff (i : ℕ) *
    (lam r) ^ (i : ℕ) * (w r * (lam r) ^ k))
      = ∑ i : Fin K, (polyAssocie lam).coeff
      (i : ℕ) * (w r * (lam r) ^ ((i : ℕ) + k)) :=
  Finset.sum_congr rfl (fun j _ => root_power_relation_term_rewrite lam w k r j)

lemma root_power_relation_shifted {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℂ)
    (k : ℕ) (r : Fin K) :
    w r * (lam r) ^ (K + k) +
      ∑ j : Fin K,
        (polyAssocie lam).coeff (j : ℕ) *
          (w r * (lam r) ^ ((j : ℕ) + k)) = 0 := by
  rw [← root_power_relation_sum_rewrite lam w k r]
  exact root_power_relation_mul_aux lam w k r

lemma sum_root_power_relation_shifted
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℂ) (k : ℕ) :
    (∑ r : Fin K, w r * (lam r) ^ (K + k)) +
      ∑ j : Fin K,
        (polyAssocie lam).coeff (j : ℕ) *
          (∑ r : Fin K, w r * (lam r) ^ ((j : ℕ) + k)) = 0 := by
  have h := fun r => root_power_relation_shifted lam w k r
  have hsum : ∑ r : Fin K,
      (w r * (lam r) ^ (K + k) +
        ∑ j : Fin K,
          (polyAssocie lam).coeff (j : ℕ) * (w r * (lam r) ^ ((j : ℕ) + k))) = 0 := by
    simp [h]
  rw [Finset.sum_add_distrib] at hsum
  rw [← hsum]
  congr 1
  rw [Finset.sum_comm' (by intro r j; trivial)]
  simp [Finset.mul_sum]

lemma moment_recurrence {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℂ) (k : ℕ) :
    (∑ r : Fin K, w r * (lam r) ^ (K + k)) =
      ∑ j : Fin K,
        (-(polyAssocie lam).coeff (j : ℕ)) *
          (∑ r : Fin K, w r * (lam r) ^ ((j : ℕ) + k)) := by
    have h := sum_root_power_relation_shifted lam w k
    have heq : (∑ r : Fin K, w r * (lam r) ^ (K + k)) =
        - ∑ j : Fin K, (polyAssocie lam).coeff (j:ℕ) *
            (∑ r : Fin K, w r * (lam r) ^ ((j:ℕ) + k)) := by
      linear_combination h
    rw [heq, ← Finset.sum_neg_distrib]
    congr 1
    funext j
    ring

lemma companion_other_col_eq_single {K : ℕ} (lam : Fin K → ℂ) (j : Fin K)
    (hj : (j : ℕ) ≠ K - 1) (m : Fin K) :
    companion' lam m j =
      if (m : ℕ) = (j : ℕ) + 1 then 1 else 0 := by
  unfold companion'
  by_cases h_outer : (m : ℕ) = (j : ℕ) + 1 ∧ (j : ℕ) < K - 1
  · simp [h_outer]
  · by_cases h_inner : (j : ℕ) = K - 1
    · exact absurd h_inner hj
    · by_cases hm : (m : ℕ) = (j : ℕ) + 1
      · exfalso
        have : (j : ℕ) < K := j.2
        omega
      · simp [hm, h_inner]

lemma sum_hankel0_companion_other_col {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (i j : Fin K) (hj : (j : ℕ) ≠ K - 1) (hjp1 : (j : ℕ) + 1 < K) :
    ∑ m : Fin K, hankel0 lam w i m * companion' lam m j
      = hankel0 lam w i ⟨(j : ℕ) + 1, hjp1⟩ := by
  rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hjp1⟩ : Fin K)]
  · have h_companion : companion' lam ⟨(j : ℕ) + 1, hjp1⟩ j = 1 := by
      rw [companion_other_col_eq_single lam j hj ⟨(j : ℕ) + 1, hjp1⟩]
      simp
    simp [h_companion]
  · intro m _ hne
    have hm : (m : ℕ) ≠ (j : ℕ) + 1 := fun h => hne (Fin.ext h)
    rw [companion_other_col_eq_single lam j hj m]
    simp [hm]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma lt_of_ne_last_index {K : ℕ} (j : Fin K) (hj : (j : ℕ) ≠ K - 1) :
    (j : ℕ) + 1 < K := by
  have hjK := j.2
  omega

lemma hankel0_succ_eq_moment {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (i j : Fin K) (hjp1 : (j : ℕ) + 1 < K) :
    hankel0 lam w i ⟨(j : ℕ) + 1, hjp1⟩ = momentsHankel lam w ((i : ℕ) + (j : ℕ) + 1) := by
  unfold hankel0
  congr 1

lemma hankel1_eq_moment {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (i j : Fin K) :
    hankel1 lam w i j = momentsHankel lam w ((i : ℕ) + (j : ℕ) + 1) := by
  rfl

lemma hankel_companion_other_col {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (i j : Fin K) (hj : (j : ℕ) ≠ K - 1) :
    hankel1 lam w i j = ∑ m : Fin K, hankel0 lam w i m * companion' lam m j := by
  have hjp1 := lt_of_ne_last_index j hj
  rw [sum_hankel0_companion_other_col lam w i j hj hjp1,
      hankel0_succ_eq_moment lam w i j hjp1,
      hankel1_eq_moment lam w i j]

lemma companion_last_col_eq {K : ℕ} (lam : Fin K → ℂ) (m j : Fin K)
    (hj : (j : ℕ) = K - 1) :
    companion' lam m j = -(polyAssocie lam).coeff (m : ℕ) := by
  unfold companion'
  simp [hj]

lemma momentsHankel_unfold {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (k : ℕ) :
    momentsHankel lam w k = ∑ r : Fin K, (w r : ℂ) * (lam r) ^ k := by
  unfold momentsHankel
  rfl

lemma moment_recurrence_applied {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (k : ℕ) :
    ∑ r : Fin K, (w r : ℂ) * (lam r) ^ (K + k)
      = ∑ j : Fin K,
          (-(polyAssocie lam).coeff (j : ℕ)) *
            (∑ r : Fin K, (w r : ℂ) * (lam r) ^ ((j : ℕ) + k)) := by
  exact moment_recurrence lam (fun r => (w r : ℂ)) k

lemma moment_recurrence_rhs_rewrite {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (k : ℕ) :
    ∑ j : Fin K,
      (-(polyAssocie lam).coeff (j : ℕ)) *
        (∑ r : Fin K, (w r : ℂ) * (lam r) ^ ((j : ℕ) + k))
    = ∑ j : Fin K,
        (-(polyAssocie lam).coeff (j : ℕ)) * momentsHankel lam w ((j : ℕ) + k) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [momentsHankel_unfold]

lemma moment_recurrence_int_weights
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (k : ℕ) :
    momentsHankel lam w (K + k) =
      ∑ j : Fin K, (-(polyAssocie lam).coeff (j : ℕ)) *
      momentsHankel lam w ((j : ℕ) + k) := by
  rw [momentsHankel_unfold lam w (K + k)]
  rw [moment_recurrence_applied lam w k]
  rw [moment_recurrence_rhs_rewrite lam w k]

lemma hankel0_mul_neg_eq_neg_mul
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (i m : Fin K) :
    hankel0 lam w i m * (-(polyAssocie lam).coeff (m : ℕ))
      = -(hankel0 lam w i m * (polyAssocie lam).coeff (m : ℕ)) := by
  ring

lemma sum_neg_hankel0_mul
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (i : Fin K) :
    ∑ m : Fin K, -(hankel0 lam w i m *
      (polyAssocie lam).coeff (m : ℕ))
      = -(∑ m : Fin K, hankel0 lam w i m *
      (polyAssocie lam).coeff (m : ℕ)) := by
  simp [Finset.sum_neg_distrib]

lemma hankel0_sum_neg_coeff_eq_neg_sum
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (i : Fin K) :
    ∑ m : Fin K, hankel0 lam w i m * (-(polyAssocie lam).coeff (m : ℕ))
      = -(∑ m : Fin K, momentsHankel lam w ((i : ℕ) + (m : ℕ)) *
        (polyAssocie lam).coeff (m : ℕ)) := by
  have step1 : ∑ m : Fin K, hankel0 lam w i m *
            (-(polyAssocie lam).coeff (m : ℕ))
             = ∑ m : Fin K, -(hankel0 lam w i m *
             (polyAssocie lam).coeff (m : ℕ)) := by
    apply Finset.sum_congr rfl
    intro m _
    exact hankel0_mul_neg_eq_neg_mul lam w i m
  rw [step1]
  rw [sum_neg_hankel0_mul lam w i]
  congr 1

lemma neg_sum_fintype_eq_sum_neg
    {ι β : Type*} [Fintype ι] [AddCommGroup β] (f : ι → β) :
    -(∑ x, f x) = ∑ x, -(f x) := by
  rw [← Finset.sum_neg_distrib]

lemma neg_sum_momentsHankel_mul_fin_cast
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (i : ℕ) (f : ℕ → ℂ) :
    -(∑ m : Fin K, momentsHankel lam w
      (i + (m : ℕ)) * f (m : ℕ))
      = ∑ m : Fin K, -(momentsHankel lam w
        (i + (m : ℕ)) * f (m : ℕ)) := by
  have : (fun m : Fin K => momentsHankel
          lam w (i + (m : ℕ)) * f (m : ℕ))
        = (fun m : Fin K => momentsHankel lam w
            (i + (m : ℕ)) * f (m : ℕ)) := rfl
  exact neg_sum_fintype_eq_sum_neg (fun m : Fin K =>
    momentsHankel lam w (i + (m : ℕ)) * f (m : ℕ))

lemma neg_sum_momentsHankel_mul_polyAssocie_coeff
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (i : Fin K) :
    -(∑ m : Fin K, momentsHankel lam w ((i : ℕ) + (m : ℕ)) *
      (polyAssocie lam).coeff (m : ℕ))
      = ∑ m : Fin K, -(momentsHankel lam w ((i : ℕ) + (m : ℕ)) *
        (polyAssocie lam).coeff (m : ℕ)) := by
  exact neg_sum_momentsHankel_mul_fin_cast
    lam w (i : ℕ) (polyAssocie lam).coeff


lemma hankel0_coeff_product_eq_moment_recurrence
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (i : Fin K) :
    ∑ m : Fin K, hankel0 lam w i m * (-(polyAssocie lam).coeff (m : ℕ))
      = momentsHankel lam w ((i : ℕ) + K) := by
  rw [hankel0_sum_neg_coeff_eq_neg_sum lam w i]
  have h_recurrence := moment_recurrence_int_weights lam w (i : ℕ)
  rw [show momentsHankel lam w ((i : ℕ) + K) =
    momentsHankel lam w (K + (i : ℕ)) by ring_nf]
  rw [h_recurrence]
  rw [neg_sum_momentsHankel_mul_polyAssocie_coeff lam w i]
  apply Finset.sum_congr rfl
  intro m _
  ring_nf

lemma hankel_fin_last_index {K : ℕ} (i : Fin K) :
    ∃ _ : K - 1 < K, True := by
  have hKpos : 0 < K := Fin.pos_iff_nonempty.mpr ⟨i⟩
  use by omega

lemma fin_index_gives_pos {K : ℕ} (i : Fin K) : 0 < K :=
  Fin.pos_iff_nonempty.mpr ⟨i⟩

noncomputable def last_fin_index {K : ℕ} (hK : 0 < K) : Fin K :=
  ⟨K - 1, by omega⟩

lemma last_fin_cast {K : ℕ} (hK : 0 < K) :
    (last_fin_index hK : ℕ) = K - 1 := by
  unfold last_fin_index
  simp []

lemma fin_add_last_arithmetic {K : ℕ} (i : Fin K) (hK : 0 < K) :
    (i : ℕ) + (K - 1) + 1 = (i : ℕ) + K := by
  omega


lemma hankel1_last_col_is_moment {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (i : Fin K) :
    hankel1 lam w i (last_fin_index (fin_index_gives_pos i)) =
    momentsHankel lam w ((i : ℕ) + K) := by
  have hK : 0 < K := fin_index_gives_pos i
  unfold hankel1
  rw [last_fin_cast hK]
  rw [fin_add_last_arithmetic i hK]

lemma sum_neg_mul {K : ℕ} (coeff moment : Fin K → ℂ) :
    ∑ j : Fin K, (-coeff j) * moment j =
    -(∑ j : Fin K, coeff j * moment j) := by
  simp [Finset.sum_neg_distrib]


--------------------------------------------------------------------------

lemma moment_recurrence_with_char_poly {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (k : ℕ) :
    momentsHankel lam w (K + k) =
      ∑ j : Fin K, charPolyCoeff lam j * momentsHankel lam w ((j : ℕ) + k) := by
  have h := moment_recurrence_int_weights lam w k
  rw [sum_neg_mul] at h
  have hc : ∀ j : Fin K, charPolyCoeff lam j = -(polyAssocie lam).coeff (j : ℕ) := by
    intro j
    rfl
  simp only [hc]
  rw [h, ← Finset.sum_neg_distrib]
  congr 1
  funext j
  rw [neg_mul]

lemma moment_recurrence_int_weights_pos_coeff {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (k : ℕ) :
    momentsHankel lam w (K + k) +
      ∑ j : Fin K, (polyAssocie lam).coeff (j : ℕ) * momentsHankel lam w ((j : ℕ) + k) = 0 := by
  have h := moment_recurrence_int_weights lam w k
  rw [sum_neg_mul] at h
  rw [h]
  ring

lemma hankel1_mk_last_is_moment {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (i : Fin K) (hK : 0 < K) :
    hankel1 lam w i ⟨K - 1, by omega⟩ = momentsHankel lam w ((i : ℕ) + K) := by
  have h_eq : (⟨K - 1, by omega⟩ : Fin K) = last_fin_index (fin_index_gives_pos i) := by
    apply Fin.ext
    simp [last_fin_index]
  rw [h_eq]
  exact hankel1_last_col_is_moment lam w i

lemma last_col_sum_as_coefficients {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (i : Fin K) (hK : 0 < K) :
    ∑ m : Fin K, hankel0 lam w i m * companion' lam m ⟨K - 1, by omega⟩
      = -(∑ m : Fin K, hankel0 lam w i m * (polyAssocie lam).coeff (m : ℕ)) := by
  rw [Finset.sum_congr rfl (fun m _ => by
    rw [companion_last_col_eq lam m ⟨K - 1, by omega⟩ (by norm_num)])]
  simp only [mul_neg]
  rw [Finset.sum_neg_distrib]

lemma hankel_companion_last_col {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (i j : Fin K) (hj : (j : ℕ) = K - 1) :
    hankel1 lam w i j = ∑ m : Fin K, hankel0 lam w i m * companion' lam m j := by
  have hK : 0 < K := Nat.pos_of_ne_zero (fun h => by simp [h] at hj; omega)
  have hj_eq : j = ⟨K - 1, by omega⟩ := Fin.ext hj
  rw [hj_eq]
  rw [hankel1_mk_last_is_moment lam w i hK]
  rw [last_col_sum_as_coefficients lam w i hK]
  rw [← hankel0_coeff_product_eq_moment_recurrence lam w i]
  simp [mul_neg, Finset.sum_neg_distrib]

theorem hankel1_eq_hankel0_mul_companion {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) :
    hankel1 lam w = hankel0 lam w * companion' lam := by
  funext i j
  rw [Matrix.mul_apply]
  by_cases hj : (j : ℕ) = K - 1
  · exact hankel_companion_last_col lam w i j hj
  · exact hankel_companion_other_col lam w i j hj


end CompagnonCharpolyThEq
