import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.ComplementRiemann.DecaleZeroProperty
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.RiemannProof.XiEntiereProp

/-! -/
namespace RiemannObtentionHyp

open Set Complex
open RiemannDef DefinitionsThEq DecaleZeroProp

theorem exclusion_cadre_spectral'
    {K : ℕ} (zs : Fin K → ℂ) (m : Fin K → ℕ)
    (hm : ∀ j, 0 < m j)
    (hinj : Function.Injective (fun j => (-Complex.I) * zs j))
    (hsym : ∀ j, ∃ k, zs k = -(starRingEnd ℂ) (zs j)) :
    let lam : Fin K → ℂ := fun j => (-Complex.I) * zs j
    let w : Fin K → ℤ := fun j => (m j : ℤ)
    IsUnit (hankel0 lam w).det ∧
    spectrum ℂ (operateurM lam w) = Set.range lam ∧
    (∀ μ ∈ spectrum ℂ (operateurM lam w),
        (starRingEnd ℂ) μ ∈ spectrum ℂ (operateurM lam w)) ∧
    (∀ j, (zs j).re ≠ 0 →
        ∃ k, k ≠ j ∧ lam k = (starRingEnd ℂ) (lam j)) :=
  exclusion_cadre_spectral zs m hm hinj hsym

lemma eq_succ_of_norm_eq
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i < j)
    (hnorm : ‖γ i‖ = ‖γ j‖) :
    j = i + 1 ∧ γ j = starRingEnd ℂ (γ i) := by
  have hi1_le_j : i + 1 ≤ j := Nat.succ_le_of_lt hij
  have h_le1 : ‖γ i‖ ≤ ‖γ (i + 1)‖ :=
    hEnum.mono_norm i (i + 1) hi (Nat.le_succ i)
  have h_le2 : ‖γ (i + 1)‖ ≤ ‖γ j‖ :=
    hEnum.mono_norm (i + 1) j (by omega) hi1_le_j
  have hnorm_i1 : ‖γ (i + 1)‖ = ‖γ i‖ := by linarith
  have hpal := hEnum.palier_strict i hi hnorm_i1
  have hj_eq : j = i + 1 := by
    by_contra hne
    have hi2_le_j : i + 2 ≤ j := by omega
    have h_le3 : ‖γ (i + 1)‖ ≤ ‖γ (i + 2)‖ :=
      hEnum.mono_norm (i + 1) (i + 2) (by omega) (by omega)
    have h_le4 : ‖γ (i + 2)‖ ≤ ‖γ j‖ :=
      hEnum.mono_norm (i + 2) j (by omega) hi2_le_j
    have hnorm_i2 : ‖γ (i + 2)‖ = ‖γ i‖ := by linarith
    exact hpal.2 hnorm_i2
  refine ⟨hj_eq, ?_⟩
  rw [hj_eq]
  exact hpal.1

lemma adj_and_conj_of_norm_eq
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hne : i ≠ j)
    (hnorm : ‖γ i‖ = ‖γ j‖) :
    (j = i + 1 ∨ i = j + 1) ∧ γ j = starRingEnd ℂ (γ i) := by
  rcases lt_or_gt_of_ne hne with hij | hji
  · obtain ⟨hj_eq, hconj⟩ := eq_succ_of_norm_eq hEnum hi hij hnorm
    exact ⟨Or.inl hj_eq, hconj⟩
  · obtain ⟨hi_eq, hconj⟩ := eq_succ_of_norm_eq hEnum hj hji hnorm.symm
    refine ⟨Or.inr hi_eq, ?_⟩
    have hconj' := congrArg (starRingEnd ℂ) hconj
    simp only [RingHomCompTriple.comp_apply, RingHom.id_apply] at hconj'
    exact hconj'.symm

theorem paliers_stricts_of_enumeration
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m) :
    PaliersStrictsXiRiemann := by
  intro z w hz hw hzw hnorm
  obtain ⟨i, hi, rfl⟩ := hEnum.exhaustive z hz
  obtain ⟨j, hj, rfl⟩ := hEnum.exhaustive w hw
  have hne : i ≠ j := by
    intro h_eq
    apply hzw
    rw [h_eq]
  exact (adj_and_conj_of_norm_eq hEnum hi hj hne hnorm).2

lemma conj_index_eq_succ_or_pred
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k)
    (him : (γ n).im ≠ 0)
    (hconj : γ k = starRingEnd ℂ (γ n)) :
    (k = n + 1 ∨ k = n - 1) ∧ m k = m n := by
  have hne : n ≠ k := by
    intro h_eq
    have hconj' := hconj
    rw [← h_eq] at hconj'
    have him_eq := congrArg Complex.im hconj'
    simp only [Complex.conj_im] at him_eq
    have him_zero : (γ n).im = 0 := by
      linarith
    exact him him_zero
  have hnorm : ‖γ n‖ = ‖γ k‖ := by
    rw [hconj, Complex.norm_conj]
  have hadj := (adj_and_conj_of_norm_eq hEnum hn hk hne hnorm).1
  have hmult : m k = m n := hEnum.conj_mult n k hn hk hconj
  refine ⟨?_, hmult⟩
  rcases hadj with h_succ | h_pred
  · exact Or.inl h_succ
  · right
    omega


open ComplexConjugate XiEntiereRiemann in
lemma XiRiemann_conj_symm' (z : ℂ) :
    XiRiemann (conj z) = conj (XiRiemann (-z)) := by
  unfold XiRiemann RiemannDef.xiDecale
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  have harg : (1 / 2 : ℂ) + I * conj z = conj ((1 / 2 : ℂ) + I * (-z)) := by
    simp only [map_add, map_mul, map_neg, map_div₀, map_one, Complex.conj_I, h2]
    ring
  rw [harg, xiEntiere_conj]

lemma exists_conj_of_im_ne_zero
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (_hsym : ∀ n, 1 ≤ n → ∃ k, 1 ≤ k ∧ γ k = -(starRingEnd ℂ) (γ n))
    (n : ℕ) (hn : 1 ≤ n) (_him : (γ n).im ≠ 0) :
    ∃ k, 1 ≤ k ∧ γ k = starRingEnd ℂ (γ n) := by
  have h_zero_conj : XiRiemann (starRingEnd ℂ (γ n)) = 0 := by
    have h_zero_n : XiRiemann (γ n) = 0 := hEnum.zero_mem n hn
    have h_even : ∀ z : ℂ, XiRiemann (-z) = XiRiemann z := by
      intro z
      change xiEntiere (1 / 2 + Complex.I * (-z)) = xiEntiere (1 / 2 + Complex.I * z)
      have h_id : (1 / 2 : ℂ) + Complex.I * (-z) = 1 - (1 / 2 + Complex.I * z) := by
        ring
      rw [h_id, xiEntiere_one_sub]
    rw [XiRiemann_conj_symm']
    rw [h_even (γ n)]
    rw [h_zero_n]
    exact map_zero (starRingEnd ℂ)
  rcases hEnum.exhaustive (starRingEnd ℂ (γ n)) h_zero_conj with ⟨k, hk_ge_one, hk_eq⟩
  exact ⟨k, hk_ge_one, hk_eq⟩

lemma open_pair_of_prev_ne_conj
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hsym : ∀ n, 1 ≤ n → ∃ k, 1 ≤ k ∧ γ k = -(starRingEnd ℂ) (γ n))
    {n : ℕ} (hn : 3 ≤ n) (him : (γ n).im ≠ 0)
    (hprev : γ (n - 1) ≠ starRingEnd ℂ (γ n)) :
    γ (n + 1) = starRingEnd ℂ (γ n) ∧
    m (n + 1) = m n ∧
    γ (n - 1) ≠ starRingEnd ℂ (γ n) := by
  obtain ⟨k, hk, hconj⟩ := exists_conj_of_im_ne_zero γ m hEnum hsym n (by omega) him
  obtain ⟨hk_cases, hmult⟩ := conj_index_eq_succ_or_pred hEnum (by omega) hk him hconj
  rcases hk_cases with rfl | rfl
  · exact ⟨hconj, hmult, hprev⟩
  · exact False.elim (hprev hconj)

lemma conj_symm_of_eq {γ : ℕ → ℂ} {a b : ℕ}
    (h : γ b = starRingEnd ℂ (γ a)) :
    γ a = starRingEnd ℂ (γ b) := by
  rw [h]
  exact (star_star (γ a)).symm

lemma no_double_conj_partner
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {n a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (ha_conj : γ a = starRingEnd ℂ (γ n))
    (hb_conj : γ b = starRingEnd ℂ (γ n)) :
    a = b := by
  have h_eq : γ a = γ b := by rw [ha_conj, hb_conj]
  exact hEnum.injective a b ha hb h_eq

lemma zero_reel_not_eq_neg_of_norm_eq
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab_ne : b ≠ a)
    (ha_real : starRingEnd ℂ (γ a) = γ a)
    (ha_nz : γ a ≠ 0)
    (hnorm : ‖γ b‖ = ‖γ a‖)
    (hopp : γ b = -γ a) : False := by
  have hconj := (adj_and_conj_of_norm_eq hEnum hb ha hab_ne hnorm).2
  have hconj' : γ b = starRingEnd ℂ (γ a) := conj_symm_of_eq hconj
  rw [ha_real] at hconj'
  rw [hconj'] at hopp
  have h_zero : γ a = 0 := by
    have h2 : (2 : ℂ) * γ a = 0 := by
      linear_combination hopp
    exact mul_eq_zero.mp h2 |>.resolve_left two_ne_zero
  exact ha_nz h_zero

lemma not_conj_of_im_zero_and_im_ne_zero
    {γ : ℕ → ℂ} {a b : ℕ}
    (ha : (γ a).im = 0)
    (hb : (γ b).im ≠ 0)
    (hconj : γ a = starRingEnd ℂ (γ b)) : False := by
  have him := congrArg Complex.im hconj
  simp only [Complex.conj_im] at him
  rw [ha] at him
  have hb_zero : (γ b).im = 0 := by linarith
  exact hb hb_zero

lemma not_conj_both_pred_and_succ
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {n : ℕ} (hn : 2 ≤ n)
    (hprev : γ (n - 1) = starRingEnd ℂ (γ n))
    (hsucc : γ (n + 1) = starRingEnd ℂ (γ n)) : False := by
  have h_eq : γ (n - 1) = γ (n + 1) := by
    rw [hprev, hsucc]
  have h_idx : n - 1 = n + 1 :=
    hEnum.injective (n - 1) (n + 1) (by omega) (by omega) h_eq
  omega

lemma im_pred_ne_zero_of_succ_ne_zero
    {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (_ : ZeroEnumeration XiRiemann γ m)
    (_ : ∀ n, ∃ k, γ k = -(starRingEnd ℂ) (γ n))
    (n₀ d : ℕ) (_ : 3 ≤ n₀)
    (him_succ : (γ (n₀ + d + 1)).im ≠ 0)
    (h_d_zero : (γ (n₀ + d)).im = 0)
    (k : ℕ) (hk_ge : 1 ≤ k)
    (hk_conj : γ k = starRingEnd ℂ (γ (n₀ + d + 1)))
    (hk_pred : k = n₀ + (d + 1) - 1) : False := by
  have hk_eq_d : k = n₀ + d := by omega
  rw [hk_eq_d] at hk_conj
  exact not_conj_of_im_zero_and_im_ne_zero h_d_zero him_succ hk_conj

lemma im_even_add_ne_zero
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (n₀ : ℕ) (hn₀ : 3 ≤ n₀) (him₀ : (γ n₀).im ≠ 0)
    (h_pas_reel : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = (starRingEnd ℂ) (γ n) → (γ (n + 1)).im ≠ 0)
    (d : ℕ) (heven : Even d)
    (ih : ∀ m_1 < d + 1,
      (Even m_1 → (γ (n₀ + m_1)).im ≠ 0 →
        γ (n₀ + m_1 + 1) = starRingEnd ℂ (γ (n₀ + m_1)) ∧
        m (n₀ + m_1 + 1) = m (n₀ + m_1) ∧
        γ (n₀ + m_1 - 1) ≠ starRingEnd ℂ (γ (n₀ + m_1))) ∧
      (Odd m_1 → (γ (n₀ + m_1)).im ≠ 0 →
        γ (n₀ + m_1 - 1) = starRingEnd ℂ (γ (n₀ + m_1)))) :
    (γ (n₀ + d)).im ≠ 0 := by
  induction d using Nat.strong_induction_on with
  | h d ih_d =>
    rcases d with _ | d
    · simpa only [Nat.add_zero] using him₀
    · have hodd : Odd d := by
        obtain ⟨k, hk⟩ := heven
        refine ⟨k - 1, by omega⟩
      rcases d with _ | d_minus_one
      · obtain ⟨k, hk⟩ := hodd
        omega
      · have heven_prev : Even d_minus_one := by
          obtain ⟨k, hk⟩ := hodd
          refine ⟨k, by omega⟩
        have h_lt_d : d_minus_one < d_minus_one + 1 + 1 := by omega
        have ih_restricted : ∀ m_1 < d_minus_one + 1,
            (Even m_1 → (γ (n₀ + m_1)).im ≠ 0 →
              γ (n₀ + m_1 + 1) = starRingEnd ℂ (γ (n₀ + m_1)) ∧
              m (n₀ + m_1 + 1) = m (n₀ + m_1) ∧
              γ (n₀ + m_1 - 1) ≠ starRingEnd ℂ (γ (n₀ + m_1))) ∧
            (Odd m_1 → (γ (n₀ + m_1)).im ≠ 0 →
              γ (n₀ + m_1 - 1) = starRingEnd ℂ (γ (n₀ + m_1))) :=
          fun m_1 hm_1 => ih m_1 (by omega)
        have him_prev : (γ (n₀ + d_minus_one)).im ≠ 0 :=
          ih_d d_minus_one h_lt_d heven_prev ih_restricted
        have h_open : γ (n₀ + d_minus_one + 1) = starRingEnd ℂ (γ (n₀ + d_minus_one)) :=
          ((ih d_minus_one (by omega)).1 heven_prev him_prev).1
        have him_odd : (γ (n₀ + d_minus_one + 1)).im ≠ 0 := by
          have him_eq := congrArg Complex.im h_open
          simp only [Complex.conj_im] at him_eq
          intro h_zero
          rw [h_zero] at him_eq
          have : (γ (n₀ + d_minus_one)).im = 0 := by linarith
          exact him_prev this
        have h_closed : γ (n₀ + d_minus_one + 1 - 1) =
            starRingEnd ℂ (γ (n₀ + d_minus_one + 1)) := by
          have h_sub : n₀ + d_minus_one + 1 - 1 = n₀ + d_minus_one := by omega
          rw [h_sub]
          exact conj_symm_of_eq h_open
        have h_next := h_pas_reel (n₀ + d_minus_one + 1) (by omega) him_odd h_closed
        have h_idx : n₀ + (d_minus_one + 1 + 1) = n₀ + d_minus_one + 1 + 1 := by omega
        rwa [h_idx]

lemma ordre_intra_palier_recurrence_strong
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hsym : ∀ n, 1 ≤ n → ∃ k, 1 ≤ k ∧ γ k = -(starRingEnd ℂ) (γ n))
    (h_pas_reel : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = (starRingEnd ℂ) (γ n) → (γ (n + 1)).im ≠ 0)
    (n₀ : ℕ) (hn₀ : 3 ≤ n₀) (him₀ : (γ n₀).im ≠ 0)
    (hmin : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0)
    (d : ℕ) :
    ((γ (n₀ + d)).im ≠ 0) ∧
    (Even d →
      γ (n₀ + d + 1) = starRingEnd ℂ (γ (n₀ + d)) ∧
      m (n₀ + d + 1) = m (n₀ + d) ∧
      γ (n₀ + d - 1) ≠ starRingEnd ℂ (γ (n₀ + d))) ∧
    (Odd d →
      γ (n₀ + d - 1) = starRingEnd ℂ (γ (n₀ + d))) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    rcases d with _ | d
    · simp only [Nat.add_zero]
      refine ⟨him₀, fun _ => ?_, fun hodd => False.elim (Nat.not_odd_zero hodd)⟩
      have hprev_ne : γ (n₀ - 1) ≠ starRingEnd ℂ (γ n₀) := by
        intro h_eq
        have h_im_zero : (γ (n₀ - 1)).im = 0 := hmin (n₀ - 1) (by omega) (by omega)
        exact not_conj_of_im_zero_and_im_ne_zero h_im_zero him₀ h_eq
      exact open_pair_of_prev_ne_conj γ m hEnum hsym (by omega) him₀ hprev_ne
    · rcases Nat.even_or_odd d with heven | hodd
      · have h_lt : d < d + 1 := Nat.lt_succ_self d
        have h_ih_d := ih d h_lt
        have him_d : (γ (n₀ + d)).im ≠ 0 := h_ih_d.1
        have h_open := h_ih_d.2.1 heven
        have h_succ_eq := h_open.1
        have h_idx_eq : n₀ + (d + 1) = n₀ + d + 1 := by omega
        have him_succ : (γ (n₀ + (d + 1))).im ≠ 0 := by
          have him_eq := congrArg Complex.im h_succ_eq
          simp only [Complex.conj_im] at him_eq
          intro h_zero
          rw [h_idx_eq] at h_zero
          rw [h_zero] at him_eq
          have h_im_d_zero : (γ (n₀ + d)).im = 0 := by
            linarith
          exact him_d h_im_d_zero
        refine ⟨him_succ, fun heven_succ => False.elim ?_, fun _ => ?_⟩
        · obtain ⟨k, hk⟩ := heven
          obtain ⟨l, hl⟩ := heven_succ
          omega
        · have h_id : n₀ + (d + 1) - 1 = n₀ + d := by omega
          rw [h_id, h_idx_eq]
          exact conj_symm_of_eq h_succ_eq
      · have h_lt : d < d + 1 := Nat.lt_succ_self d
        have h_ih_d := ih d h_lt
        have him_d : (γ (n₀ + d)).im ≠ 0 := h_ih_d.1
        have h_closed := h_ih_d.2.2 hodd
        have h_idx_eq : n₀ + (d + 1) = n₀ + d + 1 := by omega
        have him_succ : (γ (n₀ + (d + 1))).im ≠ 0 := by
          rw [h_idx_eq]
          exact h_pas_reel (n₀ + d) (by omega) him_d h_closed
        refine ⟨him_succ, fun _ => ?_, fun hodd_succ => False.elim ?_⟩
        · have hprev_ne : γ (n₀ + (d + 1) - 1) ≠ starRingEnd ℂ (γ (n₀ + (d + 1))) := by
            have h_id : n₀ + (d + 1) - 1 = n₀ + d := by omega
            rw [h_id, h_idx_eq]
            intro h_contra
            have h_symm := conj_symm_of_eq h_contra
            exact not_conj_both_pred_and_succ hEnum (by omega) h_closed h_symm
          have hn_succ_ge : 3 ≤ n₀ + (d + 1) := by omega
          exact open_pair_of_prev_ne_conj γ m hEnum hsym hn_succ_ge him_succ hprev_ne
        · obtain ⟨k, hk⟩ := hodd
          obtain ⟨l, hl⟩ := hodd_succ
          omega

theorem ordre_spectral_de_enumeration
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hsym : ∀ n, 1 ≤ n → ∃ k, 1 ≤ k ∧ γ k = -(starRingEnd ℂ) (γ n)) :
    OrdreSpectralIntraPalier γ m := by
  have h_pas_reel : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = (starRingEnd ℂ) (γ n) → (γ (n + 1)).im ≠ 0 := by
    intro n hn him hconj_prev h_reel_succ
    have h_self_conj : starRingEnd ℂ (γ (n + 1)) = γ (n + 1) := by
      apply Complex.ext
      · simp only [Complex.conj_re]
      · simp only [Complex.conj_im]
        rw [h_reel_succ]
        ring
    have hn1_ge_one : 1 ≤ n - 1 := by omega
    have hnorm_pair : ‖γ n‖ = ‖γ (n - 1)‖ := by
      have h := congrArg norm hconj_prev
      rw [Complex.norm_conj] at h
      exact h.symm
    have h_palier := hEnum.palier_strict (n - 1) hn1_ge_one
    have hn_sub_add : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    have hn_sub_add2 : n - 1 + 2 = n + 1 := by omega
    rw [hn_sub_add] at h_palier
    have h_diff_norm : ‖γ (n + 1)‖ ≠ ‖γ (n - 1)‖ := by
      have h_pal := (h_palier hnorm_pair).2
      rwa [hn_sub_add2] at h_pal
    have h_le_prev : ‖γ (n - 1)‖ ≤ ‖γ (n + 1)‖ :=
      hEnum.mono_norm (n - 1) (n + 1) hn1_ge_one (by omega)
    have h_lt_norm : ‖γ (n - 1)‖ < ‖γ (n + 1)‖ :=
      lt_of_le_of_ne h_le_prev h_diff_norm.symm
    have h_lt_norm_n : ‖γ n‖ < ‖γ (n + 1)‖ := by
      rwa [hnorm_pair]
    have h_norm_pos : 0 < ‖γ (n + 1)‖ := by
      have h_norm_n_pos : 0 < ‖γ n‖ := by
        have : γ n ≠ 0 := by
          intro h_zero
          have : (γ n).im = 0 := by rw [h_zero, Complex.zero_im]
          exact him this
        exact norm_pos_iff.mpr this
      exact lt_trans h_norm_n_pos h_lt_norm_n
    have hk_ne_zero : γ (n + 1) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h_norm_pos
      exact lt_irrefl 0 h_norm_pos
    have h_zero_neg : XiRiemann (-γ (n + 1)) = 0 := by
      have h_even : ∀ z : ℂ, XiRiemann (-z) = XiRiemann z := by
        intro z
        change xiEntiere (1 / 2 + Complex.I * (-z)) = xiEntiere (1 / 2 + Complex.I * z)
        have h_id : (1 / 2 : ℂ) + Complex.I * (-z) = 1 - (1 / 2 + Complex.I * z) := by ring
        rw [h_id, xiEntiere_one_sub]
      rw [h_even]
      exact hEnum.zero_mem (n + 1) (by omega)
    rcases hEnum.exhaustive (-γ (n + 1)) h_zero_neg with ⟨k, hk_ge_one, hk⟩
    have h_norm_k : ‖γ k‖ = ‖γ (n + 1)‖ := by
      rw [hk, norm_neg]
    by_cases h_kn : k = n + 1
    · rw [h_kn] at hk
      have h_contra : γ (n + 1) = 0 := by
        linear_combination hk / 2
      exact hk_ne_zero h_contra
    · exact zero_reel_not_eq_neg_of_norm_eq hEnum (by omega)
            hk_ge_one h_kn h_self_conj hk_ne_zero h_norm_k hk
  refine ⟨?_, ?_, h_pas_reel⟩
  · intro n₀ n hn₀ hle him₀ hmin heven _
    have hd : n₀ + (n - n₀) = n := Nat.add_sub_of_le hle
    have hres := (ordre_intra_palier_recurrence_strong
        γ m hEnum hsym h_pas_reel n₀ hn₀ him₀ hmin (n - n₀)).2.1 heven
    rwa [hd] at hres
  · intro n₀ n hn₀ hle him₀ hmin hodd _
    have hd : n₀ + (n - n₀) = n := Nat.add_sub_of_le hle
    have hres := (ordre_intra_palier_recurrence_strong
        γ m hEnum hsym h_pas_reel n₀ hn₀ him₀ hmin (n - n₀)).2.2 hodd
    rwa [hd] at hres

lemma sym_of_zero_enumeration
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hsym : ∀ n, 1 ≤ n → ∃ k, 1 ≤ k ∧ γ k = -(starRingEnd ℂ) (γ n))
    (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ)
    (hEnum₀ : ZeroEnumeration XiRiemann γ₀ m₀) :
    ∀ n, 1 ≤ n → ∃ k, 1 ≤ k ∧ γ₀ k = -(starRingEnd ℂ) (γ₀ n) := by
  intro n hn
  have h_zero : XiRiemann (γ₀ n) = 0 := hEnum₀.zero_mem n hn
  rcases hEnum.exhaustive (γ₀ n) h_zero with ⟨j, hj_ge, hj_eq⟩
  rcases hsym j hj_ge with ⟨l, hl_ge, hl_eq⟩
  have h_zero_sym : XiRiemann (-(starRingEnd ℂ) (γ₀ n)) = 0 := by
    rw [← hj_eq, ← hl_eq]
    exact hEnum.zero_mem l hl_ge
  rcases hEnum₀.exhaustive (-(starRingEnd ℂ) (γ₀ n))
    h_zero_sym with ⟨k, hk_ge, hk_eq⟩
  exact ⟨k, hk_ge, hk_eq⟩

lemma m_eq_mAlign_of_enumeration
    (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ)
    (hEnum₀ : ZeroEnumeration XiRiemann γ₀ m₀)
    (hsym₀ : ∀ k, 1 ≤ k → ∃ l, 1 ≤ l ∧ γ₀ l = -(starRingEnd ℂ) (γ₀ k))
    (n : ℕ) (hn : 3 ≤ n) (him : (γ₀ n).im ≠ 0)
    (hmin : ∀ j, 1 ≤ j → j < n → (γ₀ j).im = 0) :
    m₀ = mAlign m₀ n := by
  have hOrdre := ordre_spectral_de_enumeration γ₀ m₀ hEnum₀ hsym₀
  funext j
  unfold mAlign seuilSpectral
  have hmax : max n 3 = n := Nat.max_eq_left hn
  rw [hmax]
  split_ifs with hlt
  · rfl
  · have hle : n ≤ j := by omega
    change m₀ j = m₀ (n + 2 * ((j - n) / 2))
    rcases Nat.even_or_odd (j - n) with heven | hodd
    · have h_eq_idx : n + 2 * ((j - n) / 2) = j := by
        obtain ⟨k, hk⟩ := heven
        omega
      rw [h_eq_idx]
    · obtain ⟨k, hk⟩ := hodd
      obtain ⟨p, hp_def⟩ : ∃ p, p = n + 2 * ((j - n) / 2) := ⟨_, rfl⟩
      have hj_eq : j = p + 1 := by omega
      have hp_even : Even (p - n) := ⟨(j - n) / 2, by omega⟩
      have hp_id : n + (p - n) = p := by omega
      have him_p : (γ₀ p).im ≠ 0 := by
        have h := (ordre_intra_palier_recurrence_strong γ₀ m₀ hEnum₀ hsym₀
          hOrdre.pas_reel_apres_paire n hn him hmin (p - n)).1
        rw [hp_id] at h
        exact h
      have h_mult := (hOrdre.paire_ouverte n p hn (by omega)
        him hmin hp_even him_p).2.1
      rw [← hp_def, hj_eq, h_mult]

lemma seuilSpectral_eq_of_le {n : ℕ} (hn : 3 ≤ n) : seuilSpectral n = n := by
  unfold seuilSpectral
  exact Nat.max_eq_left hn

lemma gammaAlign_of_lt {γ : ℕ → ℂ} {n j : ℕ} (hn : 3 ≤ n) (hj : j < n) :
    gammaAlign γ n j = ((γ j).re : ℂ) := by
  have h := seuilSpectral_eq_of_le hn
  unfold gammaAlign
  rw [h]
  simp [hj]

lemma gammaAlign_of_even {γ : ℕ → ℂ} {n j : ℕ} (hn : 3 ≤ n) (hj : n ≤ j)
    (hmod : (j - n) % 2 = 0) :
    gammaAlign γ n j = poleBlocSup γ n ((j - n) / 2) := by
  have h := seuilSpectral_eq_of_le hn
  unfold gammaAlign
  rw [h]
  have hnlt : ¬ j < n := by omega
  simp [hnlt, hmod]

lemma gammaAlign_of_odd {γ : ℕ → ℂ} {n j : ℕ} (hn : 3 ≤ n) (hj : n ≤ j)
    (hmod : (j - n) % 2 ≠ 0) :
    gammaAlign γ n j = (starRingEnd ℂ) (poleBlocSup γ n ((j - n) / 2)) := by
  have h := seuilSpectral_eq_of_le hn
  unfold gammaAlign
  rw [h]
  have hnlt : ¬ j < n := by omega
  simp [hnlt, hmod]

lemma indice_pair_arith {n j : ℕ} (hj : n ≤ j) :
    n ≤ n + 2 * ((j - n) / 2) ∧ n + 2 * ((j - n) / 2) ≤ j
      ∧ Even (n + 2 * ((j - n) / 2) - n) := by
  refine ⟨by omega, by omega, ⟨(j - n) / 2, by omega⟩⟩

lemma j_eq_p_of_even {n j : ℕ} (hj : n ≤ j) (hmod : (j - n) % 2 = 0) :
    j = n + 2 * ((j - n) / 2) := by omega

lemma j_eq_p_succ_of_odd {n j : ℕ} (hj : n ≤ j) (hmod : (j - n) % 2 ≠ 0) :
    j = n + 2 * ((j - n) / 2) + 1 := by omega

lemma im_ne_zero_apres_seuil
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hsym : ∀ k, 1 ≤ k → ∃ l, 1 ≤ l ∧ γ l = -(starRingEnd ℂ) (γ k))
    (n : ℕ) (hn : 3 ≤ n) (him : (γ n).im ≠ 0)
    (hmin : ∀ j, 1 ≤ j → j < n → (γ j).im = 0) (d : ℕ) :
    (γ (n + d)).im ≠ 0 := by
  have hOrdre := ordre_spectral_de_enumeration γ m hEnum hsym
  exact (ordre_intra_palier_recurrence_strong γ m hEnum hsym
    hOrdre.pas_reel_apres_paire n hn him hmin d).1

lemma im_ne_zero_of_ge
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hsym : ∀ k, 1 ≤ k → ∃ l, 1 ≤ l ∧ γ l = -(starRingEnd ℂ) (γ k))
    (n : ℕ) (hn : 3 ≤ n) (him : (γ n).im ≠ 0)
    (hmin : ∀ j, 1 ≤ j → j < n → (γ j).im = 0) {p : ℕ} (hp : n ≤ p) :
    (γ p).im ≠ 0 := by
  have h := im_ne_zero_apres_seuil γ m hEnum hsym n hn him hmin (p - n)
  have hid : n + (p - n) = p := by omega
  rw [hid] at h
  exact h

lemma conj_suivant_de_pair
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hsym : ∀ k, 1 ≤ k → ∃ l, 1 ≤ l ∧ γ l = -(starRingEnd ℂ) (γ k))
    (n : ℕ) (hn : 3 ≤ n) (him : (γ n).im ≠ 0)
    (hmin : ∀ j, 1 ≤ j → j < n → (γ j).im = 0) {p : ℕ} (hp : n ≤ p)
    (hpair : Even (p - n)) :
    γ (p + 1) = (starRingEnd ℂ) (γ p) := by
  have hOrdre := ordre_spectral_de_enumeration γ m hEnum hsym
  have him_p := im_ne_zero_of_ge γ m hEnum hsym n hn him hmin hp
  exact (hOrdre.paire_ouverte n p hn hp him hmin hpair him_p).1

lemma eq_re_of_im_zero {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [h]

lemma eq_gammaAlign_zero {γ : ℕ → ℂ} {n : ℕ} (hn : 3 ≤ n)
    (h0 : (γ 0).im = 0) : γ 0 = gammaAlign γ n 0 := by
  rw [gammaAlign_of_lt hn (by omega)]
  exact eq_re_of_im_zero h0

lemma eq_gammaAlign_avant_seuil {γ : ℕ → ℂ} {n j : ℕ} (hn : 3 ≤ n) (hj : j < n)
    (him : (γ j).im = 0) : γ j = gammaAlign γ n j := by
  rw [gammaAlign_of_lt hn hj]
  exact eq_re_of_im_zero him

lemma poleBlocSup_im_pos (γ : ℕ → ℂ) (n k : ℕ) :
    0 < (poleBlocSup γ n k).im := by
  unfold poleBlocSup
  simp only []
  positivity

lemma poleBlocSup_re (γ : ℕ → ℂ) (n k : ℕ) :
    (poleBlocSup γ n k).re = (k : ℝ) := by
  unfold poleBlocSup
  rfl

lemma gamma_eq_gammaAlign_avant {γ₀ : ℕ → ℂ} {n j : ℕ} (hn : 3 ≤ n)
    (hj1 : 1 ≤ j) (hjn : j < n) (hmin : ∀ i, 1 ≤ i → i < n → (γ₀ i).im = 0) :
    γ₀ j = gammaAlign γ₀ n j :=
  eq_gammaAlign_avant_seuil hn hjn (hmin j hj1 hjn)

lemma gammaAlign_pair_eq {γ₀ : ℕ → ℂ} {n j : ℕ} (hn : 3 ≤ n) (hj : n ≤ j)
    (hmod : (j - n) % 2 = 0) :
    gammaAlign γ₀ n j = poleBlocSup γ₀ n ((j - n) / 2) :=
  gammaAlign_of_even hn hj hmod

lemma gammaAlign_impair_eq {γ₀ : ℕ → ℂ} {n j : ℕ} (hn : 3 ≤ n) (hj : n ≤ j)
    (hmod : (j - n) % 2 ≠ 0) :
    gammaAlign γ₀ n j = (starRingEnd ℂ) (poleBlocSup γ₀ n ((j - n) / 2)) :=
  gammaAlign_of_odd hn hj hmod

lemma gammaAlign_succ_conj {γ₀ : ℕ → ℂ} {n p : ℕ} (hn : 3 ≤ n)
    (hp : n ≤ p) (hpair : (p - n) % 2 = 0) :
    gammaAlign γ₀ n (p + 1) = (starRingEnd ℂ) (gammaAlign γ₀ n p) := by
  have hp1 : n ≤ p + 1 := by omega
  have hmod1 : (p + 1 - n) % 2 ≠ 0 := by omega
  rw [gammaAlign_impair_eq hn hp1 hmod1, gammaAlign_pair_eq hn hp hpair]
  have hdiv : (p + 1 - n) / 2 = (p - n) / 2 := by omega
  rw [hdiv]

lemma im_premier_zero_nul (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m) : (γ 1).im = 0 :=
  hEnum.real_one

lemma obtention_hypothesis
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hsym : ∀ n, 1 ≤ n → ∃ k, 1 ≤ k ∧ γ k = -(starRingEnd ℂ) (γ n)) :
    PaliersStrictsXiRiemann ∧
    ∀ (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ₀ m₀ →
      ∃ σ : Equiv.Perm ℕ,
        (∀ n < 3, σ n = n) ∧
        (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
        (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
          (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
          (∀ j, 1 ≤ j → j < n → (γ₀ ∘ σ) j = gammaAlign (γ₀ ∘ σ) n j) ∧
          (∀ p, n ≤ p → (p - n) % 2 = 0 →
            gammaAlign (γ₀ ∘ σ) n (p + 1) =
              (starRingEnd ℂ) (gammaAlign (γ₀ ∘ σ) n p)) ∧
          (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n) := by
  refine ⟨paliers_stricts_of_enumeration γ m hEnum, ?_⟩
  intro γ₀ m₀ hEnum₀
  use Equiv.refl ℕ
  refine ⟨?_, ?_, ?_⟩
  · intro n _
    rfl
  · intro n _
    rfl
  · intro n hn him hmin
    simp only [Equiv.coe_refl, Function.comp_id] at him hmin ⊢
    have hsym₀ := sym_of_zero_enumeration γ m hEnum hsym γ₀ m₀ hEnum₀
    refine ⟨?_, ?_, ?_⟩
    · intro j hj1 hjn
      exact gamma_eq_gammaAlign_avant hn hj1 hjn hmin
    · intro p hp hpair
      exact gammaAlign_succ_conj hn hp hpair
    · exact (m_eq_mAlign_of_enumeration γ₀ m₀ hEnum₀ hsym₀ n hn him hmin)



end RiemannObtentionHyp
