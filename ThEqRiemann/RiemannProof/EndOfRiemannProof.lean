import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.ComplementRiemann.InvarianceIntegralMobius

/-! -/
namespace EndRiemannProof

open Set Complex Finset Matrix Polynomial
open BigOperators ComplexConjugate
open RiemannDef InvaranceIntMobius


theorem CaractIntegraleDeuxPremiersZerosEtConjugaison
    (γ₀ : ℂ) (m₀ : ℕ) (hm₀ : 0 < m₀) :
    let z₀ : ℂ := Complex.I * γ₀
    let I₁ : ℂ := -2 * Complex.I * Real.pi * (m₀ : ℂ) * conj z₀
    let I₂ : ℂ := 2 * Complex.I * Real.pi * (m₀ : ℂ) * z₀
    let Delta₀ : ℂ := I₁ - I₂
    let Sigma₀ : ℂ := I₁ + I₂
    (I₁ = -2 * Real.pi * (m₀ : ℂ) * conj γ₀ ∧
     I₂ = -2 * Real.pi * (m₀ : ℂ) * γ₀) ∧
    ((γ₀.im = 0 ↔ conj γ₀ = γ₀) ∧
     (γ₀.im = 0 ↔ Delta₀ = 0)) ∧
    (γ₀.im = 0 → γ₀ = -Sigma₀ / (4 * Real.pi * (m₀ : ℂ)) ∧
                 γ₀ = -I₂ / (2 * Real.pi * (m₀ : ℂ))) ∧
    ‖conj γ₀‖ = ‖γ₀‖ := by
  intro z₀ I₁ I₂ Delta₀ Sigma₀
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  have hpi_ne : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hm_ne : (m₀ : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hm₀)
  have hI₁_val : I₁ = -2 * Real.pi * (m₀ : ℂ) * conj γ₀ := by
    dsimp [I₁, z₀]
    simp only [map_mul, Complex.conj_I]
    calc -2 * Complex.I * Real.pi * (m₀ : ℂ) * (-Complex.I * conj γ₀)
        = 2 * Real.pi * (m₀ : ℂ) * conj γ₀ * (Complex.I ^ 2) := by ring
      _ = 2 * Real.pi * (m₀ : ℂ) * conj γ₀ * (-1) := by rw [hI2]
      _ = -2 * Real.pi * (m₀ : ℂ) * conj γ₀ := by ring
  have hI₂_val : I₂ = -2 * Real.pi * (m₀ : ℂ) * γ₀ := by
    dsimp [I₂, z₀]
    linear_combination (2 * (Real.pi : ℂ) * (m₀ : ℂ) * γ₀) * hI2
  refine ⟨⟨hI₁_val, hI₂_val⟩, ⟨?_, ?_⟩, ?_, Complex.norm_conj γ₀⟩
  · exact Complex.conj_eq_iff_im.symm
  · rw [← Complex.conj_eq_iff_im]
    dsimp [Delta₀]
    rw [hI₁_val, hI₂_val]
    constructor
    · intro hconj
      rw [hconj]
      ring
    · intro hsub
      have hfac : (-2 * (Real.pi : ℂ) * (m₀ : ℂ)) * (conj γ₀ - γ₀) = 0 := by
        linear_combination hsub
      rcases mul_eq_zero.mp hfac with hcoef | hdiff
      · exfalso
        have h2 : (-2 : ℂ) ≠ 0 := by norm_num
        exact mul_ne_zero (mul_ne_zero h2 hpi_ne) hm_ne hcoef
      · exact sub_eq_zero.mp hdiff
  · intro him
    have hconj : conj γ₀ = γ₀ := Complex.conj_eq_iff_im.mpr him
    have hSigma_val : Sigma₀ = -4 * Real.pi * (m₀ : ℂ) * γ₀ := by
      dsimp [Sigma₀]
      rw [hI₁_val, hI₂_val, hconj]
      ring
    have h4_ne : (4 * (Real.pi : ℂ) * (m₀ : ℂ)) ≠ 0 := by
      have h4 : (4 : ℂ) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero h4 hpi_ne) hm_ne
    have h2_ne : (2 * (Real.pi : ℂ) * (m₀ : ℂ)) ≠ 0 := by
      have h2 : (2 : ℂ) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero h2 hpi_ne) hm_ne
    constructor
    · rw [hSigma_val]
      field_simp [h4_ne]
    · rw [hI₂_val]
      field_simp [h2_ne]


lemma conj_of_norm_eq
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j)
    (hnorm : ‖γ i‖ = ‖γ j‖) :
    γ j = starRingEnd ℂ (γ i) := by
  have h_lt : ∀ a b, 1 ≤ a → a < b → ‖γ a‖ = ‖γ b‖ → γ b = starRingEnd ℂ (γ a) := by
    intro a b ha hab h_eq
    have h_step : ‖γ (a + 1)‖ = ‖γ a‖ := le_antisymm
      (by rw [h_eq]; exact hEnum.mono_norm (a + 1) b (by omega) (by omega))
      (hEnum.mono_norm a (a + 1) ha (by omega))
    have h_pal := hEnum.palier_strict a ha h_step
    by_cases h_ba : b = a + 1
    · subst h_ba; exact h_pal.1
    · exfalso
      apply h_pal.2
      exact le_antisymm
        (by rw [h_eq]; exact hEnum.mono_norm (a + 2) b (by omega) (by omega))
        (hEnum.mono_norm a (a + 2) ha (by omega))
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact h_lt i j hi hlt hnorm
  · exact (hij rfl).elim
  · have h_symm := h_lt j i hj hgt hnorm.symm
    rw [h_symm, RingHomCompTriple.comp_apply, RingHom.id_apply]

lemma SwapZeroEnumerationMemeModule
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q)
    (hnorm : ‖γ p‖ = ‖γ q‖) :
    ZeroEnumeration Xi (fun n => γ (Equiv.swap p q n)) (fun n => m (Equiv.swap p q n)) := by
  have h_ge_one : ∀ n, 1 ≤ n → 1 ≤ Equiv.swap p q n := by
    intro n hn
    by_cases hnp : n = p
    · subst hnp; simp [Equiv.swap_apply_left]; omega
    · by_cases hnq : n = q
      · subst hnq; simp [Equiv.swap_apply_right]; omega
      · rw [Equiv.swap_apply_of_ne_of_ne hnp hnq]; exact hn
  have h_norm_eq : ∀ n, ‖γ (Equiv.swap p q n)‖ = ‖γ n‖ := by
    intro n
    by_cases hnp : n = p
    · subst hnp; simp [Equiv.swap_apply_left, hnorm]
    · by_cases hnq : n = q
      · subst hnq; simp [Equiv.swap_apply_right, hnorm]
      · rw [Equiv.swap_apply_of_ne_of_ne hnp hnq]
  refine
    { zero_mem := fun n hn => hEnum.zero_mem _ (h_ge_one n hn)
      injective := fun i j hi hj hγ_eq =>
        (Equiv.swap p q).injective
          (hEnum.injective _ _ (h_ge_one i hi) (h_ge_one j hj) hγ_eq)
      exhaustive := fun z hz => by
        obtain ⟨n₀, hn₀, hγn₀⟩ := hEnum.exhaustive z hz
        refine ⟨Equiv.swap p q n₀, h_ge_one n₀ hn₀, ?_⟩
        simp [hγn₀]
      mono_norm := fun i j hi hij => by
        rw [h_norm_eq i, h_norm_eq j]
        exact hEnum.mono_norm i j hi hij
      palier_strict := fun n hn h_eq => by
        have h_eq' : ‖γ (n + 1)‖ = ‖γ n‖ := by
          rwa [h_norm_eq (n + 1), h_norm_eq n] at h_eq
        refine ⟨?_, ?_⟩
        · exact conj_of_norm_eq hEnum
            (h_ge_one n hn)
            (h_ge_one (n + 1) (by omega))
            (fun h => by have := (Equiv.swap p q).injective h; omega)
            h_eq.symm
        · rw [h_norm_eq (n + 2), h_norm_eq n]
          exact (hEnum.palier_strict n hn h_eq').2
      mult_pos := fun n hn => hEnum.mult_pos _ (h_ge_one n hn)
      real_one := by
        have h1p : 1 ≠ p := by omega
        have h1q : 1 ≠ q := by omega
        rw [Equiv.swap_apply_of_ne_of_ne h1p h1q]
        exact hEnum.real_one
      real_two := by
        have h2p : 2 ≠ p := by omega
        have h2q : 2 ≠ q := by omega
        rw [Equiv.swap_apply_of_ne_of_ne h2p h2q]
        exact hEnum.real_two
      conj_mult := fun i j hi hj hconj =>
        hEnum.conj_mult (Equiv.swap p q i) (Equiv.swap p q j)
          (h_ge_one i hi) (h_ge_one j hj) hconj }

lemma PermZeroEnumerationMemeModule
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    (σ : Equiv.Perm ℕ)
    (hfix : ∀ n < 3, σ n = n)
    (hnorm : ∀ n, 1 ≤ n → ‖γ (σ n)‖ = ‖γ n‖) :
    ZeroEnumeration Xi (γ ∘ σ) (m ∘ σ) := by
  have h_ge_one : ∀ n, 1 ≤ n → 1 ≤ σ n := by
    intro n hn
    by_contra hlt
    push Not at hlt
    have hσ0 : σ n = 0 := Nat.lt_one_iff.mp hlt
    have h0 : σ 0 = 0 := hfix 0 (by omega)
    have hn0 : n = 0 := σ.injective (hσ0.trans h0.symm)
    omega
  have h_inv_ge_one : ∀ n, 1 ≤ n → 1 ≤ σ.symm n := by
    intro n hn
    by_contra hlt
    push Not at hlt
    have hσ0 : σ.symm n = 0 := Nat.lt_one_iff.mp hlt
    have hn0 : n = σ 0 := by rw [← hσ0, Equiv.apply_symm_apply]
    rw [hfix 0 (by omega)] at hn0
    omega
  refine
    { zero_mem := fun n hn => hEnum.zero_mem (σ n) (h_ge_one n hn)
      injective := fun i j hi hj h =>
        σ.injective (hEnum.injective (σ i) (σ j)
          (h_ge_one i hi) (h_ge_one j hj) h)
      exhaustive := fun z hz => by
        obtain ⟨n₀, hn₀, hγn₀⟩ := hEnum.exhaustive z hz
        refine ⟨σ.symm n₀, h_inv_ge_one n₀ hn₀, ?_⟩
        simp [Function.comp, hγn₀]
      mono_norm := fun i j hi hij => by
        have hj : 1 ≤ j := le_trans hi hij
        simp only [Function.comp_apply, hnorm i hi, hnorm j hj]
        exact hEnum.mono_norm i j hi hij
      palier_strict := fun n hn h_eq => by
        simp only [Function.comp_apply] at h_eq ⊢
        have h_eq' : ‖γ (n + 1)‖ = ‖γ n‖ := by
          rwa [hnorm (n + 1) (by omega), hnorm n hn] at h_eq
        refine ⟨?_, ?_⟩
        · exact conj_of_norm_eq hEnum
            (h_ge_one n hn)
            (h_ge_one (n + 1) (by omega))
            (fun h => by have := σ.injective h; omega)
            h_eq.symm
        · rw [hnorm (n + 2) (by omega), hnorm n hn]
          exact (hEnum.palier_strict n hn h_eq').2
      mult_pos := fun n hn => hEnum.mult_pos (σ n) (h_ge_one n hn)
      real_one := by
        simp only [Function.comp_apply, hfix 1 (by omega)]
        exact hEnum.real_one
      real_two := by
        simp only [Function.comp_apply, hfix 2 (by omega)]
        exact hEnum.real_two
      conj_mult := fun i j hi hj hconj =>
        hEnum.conj_mult (σ i) (σ j)
          (h_ge_one i hi) (h_ge_one j hj) hconj }



lemma PalierModuleConstant_convexe
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {i k j : ℕ} (hi : 1 ≤ i) (hik : i ≤ k) (hkj : k ≤ j)
    {r : ℝ} (hri : ‖γ i‖ = r) (hrj : ‖γ j‖ = r) :
    ‖γ k‖ = r := by
  have h1 : r ≤ ‖γ k‖ := by
    rw [← hri]
    exact hEnum.mono_norm i k hi hik
  have h2 : ‖γ k‖ ≤ r := by
    rw [← hrj]
    exact hEnum.mono_norm k j (le_trans hi hik) hkj
  linarith

lemma ConjCompatImpliqueHypothesePremierNonReel
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (_hEnum : ZeroEnumeration Xi γ m)
    (hCompat : ConjCompatible' γ m) :
    ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
      γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n := by
  intro n hn3 h_im_ne h_prev_real
  have hn1_ge : 1 ≤ n - 1 := by omega
  have hn1_lt : n - 1 < n := by omega
  have h_prev_im_zero : (γ (n - 1)).im = 0 := h_prev_real (n - 1) hn1_ge hn1_lt
  have h_not_conj : γ (n - 1) ≠ (starRingEnd ℂ) (γ n) := by
    intro h_eq
    have h_im_eq : (γ (n - 1)).im = ((starRingEnd ℂ) (γ n)).im :=
      congrArg Complex.im h_eq
    rw [h_prev_im_zero, Complex.conj_im, zero_eq_neg] at h_im_eq
    exact h_im_ne h_im_eq
  exact hCompat.conj_next n hn3 h_im_ne h_not_conj

theorem exists_zeroEnumeration_XiRiemann_compat_of_perm
    {γ₀ : ℕ → ℂ} {m₀ : ℕ → ℕ}
    (hEnum₀ : ZeroEnumeration XiRiemann γ₀ m₀)
    (σ : Equiv.Perm ℕ)
    (hfix : ∀ n < 3, σ n = n)
    (hnorm : ∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖)
    (hCompatσ : ConjCompatible' (γ₀ ∘ σ) (m₀ ∘ σ)) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧ ConjCompatible' γ m ∧
      (∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n) := by
  refine ⟨γ₀ ∘ σ, m₀ ∘ σ, ?_, hCompatσ, ?_⟩
  · exact PermZeroEnumerationMemeModule hEnum₀ σ hfix hnorm
  · exact ConjCompatImpliqueHypothesePremierNonReel
      (PermZeroEnumerationMemeModule hEnum₀ σ hfix hnorm) hCompatσ




--------------------------------------------------------------------

lemma sq_sub_conj_eq (z : ℂ) :
    (z - (starRingEnd ℂ) z) ^ 2 = ((-4 * z.im ^ 2 : ℝ) : ℂ) := by
  have hsub : z - (starRingEnd ℂ) z = 2 * (z.im : ℂ) * Complex.I := by
    have h := Complex.sub_conj z
    push_cast at h
    exact h
  rw [hsub]
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  push_cast
  linear_combination (4 * (z.im : ℂ) ^ 2) * hI2


lemma neg_four_mul_im_sq_neg {z : ℂ} (hz : z.im ≠ 0) :
    -4 * z.im ^ 2 < 0 := by
  have hsq : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
  linarith

lemma mul_sq_sub_conj_eq_real (x : ℝ) (z : ℂ) :
    ((x : ℂ) - (starRingEnd ℂ) z) ^ 2 * ((x : ℂ) - z) ^ 2 =
      ((((x - z.re) ^ 2 + z.im ^ 2) ^ 2 : ℝ) : ℂ) := by
  have hprod : ((x : ℂ) - (starRingEnd ℂ) z) * ((x : ℂ) - z) =
      (((x - z.re) ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [sq]
    · simp [sq]
      ring
  calc
    ((x : ℂ) - (starRingEnd ℂ) z) ^ 2 * ((x : ℂ) - z) ^ 2
        = (((x : ℂ) - (starRingEnd ℂ) z) * ((x : ℂ) - z)) ^ 2 := by ring
    _ = ((((x - z.re) ^ 2 + z.im ^ 2 : ℝ) : ℂ)) ^ 2 := by rw [hprod]
    _ = ((((x - z.re) ^ 2 + z.im ^ 2) ^ 2 : ℝ) : ℂ) := by push_cast; ring




lemma mul_sq_sub_conj_pos (x : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    0 < ((x - z.re) ^ 2 + z.im ^ 2) ^ 2 := by
  have him2 : 0 < z.im ^ 2 := sq_pos_of_ne_zero hz
  have hre2 : 0 ≤ (x - z.re) ^ 2 := sq_nonneg (x - z.re)
  have hsum : 0 < (x - z.re) ^ 2 + z.im ^ 2 := by linarith
  exact sq_pos_of_pos hsum

lemma mul_sq_sub_conj_re_pos {w z : ℂ} (hw : w.im = 0) (hz : z.im ≠ 0) :
    0 < (((w - (starRingEnd ℂ) z) ^ 2 * (w - z) ^ 2).re) := by
  have hw_eq : w = (w.re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hw]
  rw [hw_eq, mul_sq_sub_conj_eq_real w.re z, Complex.ofReal_re]
  exact mul_sq_sub_conj_pos w.re hz

theorem NegativiteDeterminantPaireComplete
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hConf : ConfigurationDegenereePaire γ m n)
    (P_cross : ℝ) (hP_cross : 0 < P_cross)
    (hVandermonde_pair :
      (Delta γ m n n).re =
        -4 * (m (n - 1) : ℝ) * (m n : ℝ) * (γ n).im ^ 2 *
          (Delta γ m (n - 2) (n - 2)).re * P_cross) :
    (Delta γ m n n).re < 0 := by
  rw [hVandermonde_pair]
  have hm_n : (0 : ℝ) < (m n : ℝ) := Nat.cast_pos.mpr hConf.mult_pos_n
  have hm_prev : (0 : ℝ) < (m (n - 1) : ℝ) := by
    rw [hConf.mult_eq]
    exact hm_n
  have him2 : 0 < (γ n).im ^ 2 := sq_pos_of_ne_zero hConf.im_ne_zero
  have hdet_prev : 0 < (Delta γ m (n - 2) (n - 2)).re := hConf.det_prev_pos
  have hpos_prod :
      0 < 4 * (m (n - 1) : ℝ) * (m n : ℝ) * (γ n).im ^ 2 *
            (Delta γ m (n - 2) (n - 2)).re * P_cross := by
    positivity
  linarith

lemma hankelDet_next_neg_of_real_step
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (h_det_n_neg : (Delta γ m n n).re < 0)
    (hm_next : 1 ≤ m (n + 1))
    (h_im_n : (γ n).im ≠ 0)
    (_h_im_next : (γ (n + 1)).im = 0)
    (R_prev : ℝ) (hR_prev : 0 < R_prev)
    (hTransition :
      (Delta γ m (n + 1) (n + 1)).re =
        (Delta γ m n n).re *
          ((m (n + 1) : ℝ) *
            (((γ (n + 1)).re - (γ n).re) ^ 2 + (γ n).im ^ 2) ^ 2 * R_prev)) :
    (Delta γ m (n + 1) (n + 1)).re < 0 := by
  rw [hTransition]
  have hm_pos : (0 : ℝ) < (m (n + 1) : ℝ) := Nat.cast_pos.mpr hm_next
  have h_pair_pos : 0 < (((γ (n + 1)).re - (γ n).re) ^ 2 + (γ n).im ^ 2) ^ 2 :=
    mul_sq_sub_conj_pos (γ (n + 1)).re h_im_n
  have hC_pos :
      0 < (m (n + 1) : ℝ) *
            (((γ (n + 1)).re - (γ n).re) ^ 2 + (γ n).im ^ 2) ^ 2 * R_prev :=
    mul_pos (mul_pos hm_pos h_pair_pos) hR_prev
  exact mul_neg_of_neg_of_pos h_det_n_neg hC_pos

theorem Propagation_DegenereProof_PreProof
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ)
    (hPos : ∀ n, n₀ ≤ n → 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = (starRingEnd ℂ) (γ n) →
      0 < (Delta γ m (n + 1) (n + 1)).re)
    (hTransitionNeg : ∀ n, n₀ ≤ n → 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = (starRingEnd ℂ) (γ n) →
      (γ (n + 1)).im = 0 →
      (Delta γ m (n + 1) (n + 1)).re < 0) :
    ∀ n, n₀ ≤ n → 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = (starRingEnd ℂ) (γ n) → (γ (n + 1)).im ≠ 0 := by
  intro n hn₀ h3 hne hprev h_im_next
  have h_det_pos : 0 < (Delta γ m (n + 1) (n + 1)).re :=
    hPos n hn₀ h3 hne hprev
  have h_det_neg : (Delta γ m (n + 1) (n + 1)).re < 0 :=
    hTransitionNeg n hn₀ h3 hne hprev h_im_next
  exact lt_irrefl _ (h_det_pos.trans h_det_neg)



---------------------------------------------------------------------

lemma ObstructionConjCompatibleNaif
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    (hNaif : ConjCompatible γ m) :
    ∀ n, 1 ≤ n → (γ n).im = 0 := by
  intro n hn1
  rcases eq_or_ne n 1 with rfl | hn_ne1
  · exact hEnum.real_one
  · rcases eq_or_ne n 2 with rfl | hn_ne2
    · exact hEnum.real_two
    · have hn3 : 3 ≤ n := by omega
      by_contra h_im_ne
      have h_step1 : γ (n + 1) = (starRingEnd ℂ) (γ n) :=
        hNaif.conj_next n hn3 h_im_ne
      have h_im_next : (γ (n + 1)).im ≠ 0 := by
        rw [h_step1, Complex.conj_im, neg_ne_zero]
        exact h_im_ne
      have hn1_ge3 : 3 ≤ n + 1 := by omega
      have h_step2 : γ (n + 2) = (starRingEnd ℂ) (γ (n + 1)) :=
        hNaif.conj_next (n + 1) hn1_ge3 h_im_next
      rw [h_step1, RingHomCompTriple.comp_apply, RingHom.id_apply] at h_step2
      have hn2_ge1 : 1 ≤ n + 2 := by omega
      have h_idx_eq : n + 2 = n :=
        hEnum.injective (n + 2) n hn2_ge1 hn1 h_step2
      omega

lemma Hn_eq_sum_rang_un (γ : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ) (p q : Fin N) :
    Hn γ m N p q =
      ∑ j ∈ Finset.Icc 1 N,
        (m j : ℂ) * vecteurMomentLocal γ j N p * vecteurMomentLocal γ j N q := by
  simp only [Hn, Matrix.of_apply, newton, vecteurMomentLocal]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pow_add]
  ring

lemma PariteBlocsConjuguesDepuisPremier
    {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hOrdre : OrdreSpectralIntraPalier γ m)
    {n₀ n : ℕ} (hn₀3 : 3 ≤ n₀) (hn₀n : n₀ ≤ n)
    (h_im_n₀ : (γ n₀).im ≠ 0)
    (h_first : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0)
    (h_im_n : (γ n).im ≠ 0) :
    (Even (n - n₀) →
      γ (n + 1) = (starRingEnd ℂ) (γ n) ∧
      m (n + 1) = m n ∧
      γ (n - 1) ≠ (starRingEnd ℂ) (γ n)) ∧
    (Odd (n - n₀) →
      γ (n - 1) = (starRingEnd ℂ) (γ n)) := by
  refine ⟨?_, ?_⟩
  · intro hEven
    exact hOrdre.paire_ouverte n₀ n hn₀3 hn₀n h_im_n₀ h_first hEven h_im_n
  · intro hOdd
    exact hOrdre.paire_fermee n₀ n hn₀3 hn₀n h_im_n₀ h_first hOdd h_im_n

theorem conjCompat'_of_first_preProof
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    (hconj : HconjFirst γ m)
    (hOrdre : OrdreSpectralIntraPalier γ m) :
    ConjCompatible' γ m := by
  refine ⟨?_⟩
  intro n hn3 h_im_n h_prev_ne_conj
  by_cases h_exists_before : ∃ j, 1 ≤ j ∧ j < n ∧ (γ j).im ≠ 0
  · classical
    have h_ex_nonreal : ∃ j, 1 ≤ j ∧ (γ j).im ≠ 0 := ⟨n, by omega, h_im_n⟩
    let n₀ := Nat.find h_ex_nonreal
    have hn₀_spec : 1 ≤ n₀ ∧ (γ n₀).im ≠ 0 := Nat.find_spec h_ex_nonreal
    have hn₀_ge1 : 1 ≤ n₀ := hn₀_spec.1
    have hn₀_im : (γ n₀).im ≠ 0 := hn₀_spec.2
    have hn₀_min : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0 := by
      intro j hj1 hjn₀
      by_contra hj_im
      exact Nat.find_min h_ex_nonreal hjn₀ ⟨hj1, hj_im⟩
    have hn₀_ge3 : 3 ≤ n₀ := by
      by_contra hlt3
      have h_cases : n₀ = 1 ∨ n₀ = 2 := by omega
      rcases h_cases with h1 | h2
      · rw [h1] at hn₀_im; exact hn₀_im hEnum.real_one
      · rw [h2] at hn₀_im; exact hn₀_im hEnum.real_two
    have hn₀_le_n : n₀ ≤ n := Nat.find_min' h_ex_nonreal ⟨by omega, h_im_n⟩
    have hParite := PariteBlocsConjuguesDepuisPremier
      hOrdre hn₀_ge3 hn₀_le_n hn₀_im hn₀_min h_im_n
    rcases Nat.even_or_odd (n - n₀) with hEven | hOdd
    · obtain ⟨h_next_conj, h_next_mult, _⟩ := hParite.1 hEven
      exact ⟨h_next_conj, h_next_mult⟩
    · exfalso
      have h_prev_eq : γ (n - 1) = (starRingEnd ℂ) (γ n) := hParite.2 hOdd
      exact h_prev_ne_conj h_prev_eq
  · push Not at h_exists_before
    exact hconj n hn3 h_im_n h_exists_before

-----------------------------------------------------------------------

lemma gammaAlign_im_eq_zero_of_lt (γ : ℕ → ℂ) (n₁ n : ℕ) (h : n < seuilSpectral n₁) :
    (gammaAlign γ n₁ n).im = 0 := by
  unfold gammaAlign
  rw [ite_eq_left h, Complex.ofReal_im]

lemma gammaAlign_im_ne_zero_of_ge (γ : ℕ → ℂ) (n₁ n : ℕ) (h : seuilSpectral n₁ ≤ n) :
    (gammaAlign γ n₁ n).im ≠ 0 := by
  unfold gammaAlign
  have hnot : ¬ (n < seuilSpectral n₁) := not_lt.mpr h
  rw [ite_eq_right hnot]
  dsimp only
  split_ifs with hmod
  · exact poleBlocSup_im_ne_zero γ n₁ ((n - seuilSpectral n₁) / 2)
  · rw [Complex.conj_im, neg_ne_zero]
    exact poleBlocSup_im_ne_zero γ n₁ ((n - seuilSpectral n₁) / 2)

lemma gammaAlign_im_ne_zero_iff (γ : ℕ → ℂ) (n₁ n : ℕ) :
    (gammaAlign γ n₁ n).im ≠ 0 ↔ seuilSpectral n₁ ≤ n := by
  constructor
  · intro him
    by_contra hlt
    push Not at hlt
    exact him (gammaAlign_im_eq_zero_of_lt γ n₁ n hlt)
  · exact gammaAlign_im_ne_zero_of_ge γ n₁ n

lemma gammaAlign_im_pos_of_even (γ : ℕ → ℂ) (n₁ n : ℕ)
    (h : seuilSpectral n₁ ≤ n) (heven : (n - seuilSpectral n₁) % 2 = 0) :
    0 < (gammaAlign γ n₁ n).im := by
  unfold gammaAlign
  have hnot : ¬ (n < seuilSpectral n₁) := not_lt.mpr h
  rw [ite_eq_right hnot]
  dsimp only
  rw [ite_eq_left heven]
  exact poleBlocSup_im_pos γ n₁ ((n - seuilSpectral n₁) / 2)

lemma gammaAlign_im_neg_of_odd (γ : ℕ → ℂ) (n₁ n : ℕ)
    (h : seuilSpectral n₁ ≤ n) (hodd : (n - seuilSpectral n₁) % 2 ≠ 0) :
    (gammaAlign γ n₁ n).im < 0 := by
  unfold gammaAlign
  have hnot : ¬ (n < seuilSpectral n₁) := not_lt.mpr h
  rw [ite_eq_right hnot]
  dsimp only
  rw [ite_eq_right hodd, Complex.conj_im]
  have hpos := poleBlocSup_im_pos γ n₁ ((n - seuilSpectral n₁) / 2)
  linarith

lemma eq_seuilSpectral_of_first_nonreal (γ : ℕ → ℂ) (n₁ n₀ : ℕ)
    (h_im_n₀ : (gammaAlign γ n₁ n₀).im ≠ 0)
    (h_first : ∀ j, 1 ≤ j → j < n₀ → (gammaAlign γ n₁ j).im = 0) :
    n₀ = seuilSpectral n₁ := by
  have h_le : seuilSpectral n₁ ≤ n₀ := (gammaAlign_im_ne_zero_iff γ n₁ n₀).mp h_im_n₀
  by_contra h_ne
  have h_lt : seuilSpectral n₁ < n₀ := lt_of_le_of_ne h_le (Ne.symm h_ne)
  have h_ge3 : 3 ≤ seuilSpectral n₁ := le_max_right n₁ 3
  have h_ge1 : 1 ≤ seuilSpectral n₁ := by omega
  have h_im_zero : (gammaAlign γ n₁ (seuilSpectral n₁)).im = 0 :=
    h_first (seuilSpectral n₁) h_ge1 h_lt
  have h_im_nz : (gammaAlign γ n₁ (seuilSpectral n₁)).im ≠ 0 :=
    gammaAlign_im_ne_zero_of_ge γ n₁ (seuilSpectral n₁) le_rfl
  exact h_im_nz h_im_zero

lemma div2_pred_add_one_eq {S n : ℕ} (hn : S < n) (heven : (n - S) % 2 = 0) :
    (n - 1 - S) / 2 + 1 = (n - S) / 2 := by
  omega

lemma not_conj_prev_of_even_gt_seuil
    (γ : ℕ → ℂ) (n₁ n : ℕ)
    (hn₀n : seuilSpectral n₁ ≤ n)
    (h_gt_S : seuilSpectral n₁ < n)
    (h_mod_even : (n - seuilSpectral n₁) % 2 = 0)
    (_ : ∀ k, 0 < (poleBlocSup γ n₁ k).im)
    (h_pole_inj : ∀ k₁ k₂, poleBlocSup γ n₁ k₁ = poleBlocSup γ n₁ k₂ → k₁ = k₂) :
    gammaAlign γ n₁ (n - 1) ≠ (starRingEnd ℂ) (gammaAlign γ n₁ n) := by
  intro h_eq_prev
  have h_prev_ge : seuilSpectral n₁ ≤ n - 1 := by omega
  have hnot_prev : ¬ (n - 1 < seuilSpectral n₁) := not_lt.mpr h_prev_ge
  have hnot_n : ¬ (n < seuilSpectral n₁) := not_lt.mpr hn₀n
  have h_prev_ne_zero : (n - 1 - seuilSpectral n₁) % 2 ≠ 0 := by omega
  have h_prev_val : gammaAlign γ n₁ (n - 1) =
      (starRingEnd ℂ) (poleBlocSup γ n₁ ((n - 1 - seuilSpectral n₁) / 2)) := by
    unfold gammaAlign
    rw [ite_eq_right hnot_prev]
    dsimp only
    rw [ite_eq_right h_prev_ne_zero]
  have h_n_val : gammaAlign γ n₁ n =
      poleBlocSup γ n₁ ((n - seuilSpectral n₁) / 2) := by
    unfold gammaAlign
    rw [ite_eq_right hnot_n]
    dsimp only
    rw [ite_eq_left h_mod_even]
  rw [h_prev_val, h_n_val] at h_eq_prev
  have h_pole_eq : poleBlocSup γ n₁ ((n - 1 - seuilSpectral n₁) / 2) =
      poleBlocSup γ n₁ ((n - seuilSpectral n₁) / 2) := by
    exact (starRingEnd ℂ).injective h_eq_prev
  have h_idx_eq : (n - 1 - seuilSpectral n₁) / 2 = (n - seuilSpectral n₁) / 2 :=
    h_pole_inj _ _ h_pole_eq
  omega


lemma not_conj_prev_of_even_gt_seuil_inj
    (γ : ℕ → ℂ) (n₁ n : ℕ)
    (hn₀n : seuilSpectral n₁ ≤ n)
    (h_gt_S : seuilSpectral n₁ < n)
    (h_mod_even : (n - seuilSpectral n₁) % 2 = 0)
    (h_inj : ∀ k₁ k₂, poleBlocSup γ n₁ k₁ = poleBlocSup γ n₁ k₂ → k₁ = k₂) :
    gammaAlign γ n₁ (n - 1) ≠ (starRingEnd ℂ) (gammaAlign γ n₁ n) := by
  intro h_eq_prev
  have h_prev_ge : seuilSpectral n₁ ≤ n - 1 := by omega
  have hnot_prev : ¬ (n - 1 < seuilSpectral n₁) := not_lt.mpr h_prev_ge
  have hnot_n : ¬ (n < seuilSpectral n₁) := not_lt.mpr hn₀n
  have h_prev_ne_zero : (n - 1 - seuilSpectral n₁) % 2 ≠ 0 := by omega
  have h_prev_val : gammaAlign γ n₁ (n - 1) =
      (starRingEnd ℂ) (poleBlocSup γ n₁ ((n - 1 - seuilSpectral n₁) / 2)) := by
    unfold gammaAlign
    rw [ite_eq_right hnot_prev]
    dsimp only
    rw [ite_eq_right h_prev_ne_zero]
  have h_n_val : gammaAlign γ n₁ n =
      poleBlocSup γ n₁ ((n - seuilSpectral n₁) / 2) := by
    unfold gammaAlign
    rw [ite_eq_right hnot_n]
    dsimp only
    rw [ite_eq_left h_mod_even]
  rw [h_prev_val, h_n_val] at h_eq_prev
  have h_pole_eq : poleBlocSup γ n₁ ((n - 1 - seuilSpectral n₁) / 2) =
      poleBlocSup γ n₁ ((n - seuilSpectral n₁) / 2) :=
    (starRingEnd ℂ).injective h_eq_prev
  have h_k_eq := h_inj _ _ h_pole_eq
  omega

lemma poleBlocSup_inj_of_im_eq
    (γ : ℕ → ℂ) (n₁ : ℕ)
    (h_pole_im : ∀ k, (poleBlocSup γ n₁ k).im = (k : ℝ) + 1) :
    ∀ k₁ k₂, poleBlocSup γ n₁ k₁ = poleBlocSup γ n₁ k₂ → k₁ = k₂ := by
  intro k₁ k₂ h
  have him := congrArg Complex.im h
  rw [h_pole_im k₁, h_pole_im k₂] at him
  have : (k₁ : ℝ) = (k₂ : ℝ) := by linarith
  exact_mod_cast this

lemma not_conj_prev_of_even_gt_seuil_im
    (γ : ℕ → ℂ) (n₁ n : ℕ)
    (hn₀n : seuilSpectral n₁ ≤ n)
    (h_gt_S : seuilSpectral n₁ < n)
    (h_mod_even : (n - seuilSpectral n₁) % 2 = 0)
    (h_pole_im : ∀ k, (poleBlocSup γ n₁ k).im = (k : ℝ) + 1) :
    gammaAlign γ n₁ (n - 1) ≠ (starRingEnd ℂ) (gammaAlign γ n₁ n) :=
  not_conj_prev_of_even_gt_seuil_inj γ n₁ n hn₀n h_gt_S h_mod_even
    (poleBlocSup_inj_of_im_eq γ n₁ h_pole_im)


lemma poleBlocSup_injective (γ : ℕ → ℂ) (n₁ : ℕ) :
    ∀ k₁ k₂, poleBlocSup γ n₁ k₁ = poleBlocSup γ n₁ k₂ → k₁ = k₂ := by
  intro k₁ k₂ h
  have h_re := congrArg Complex.re h
  simp only [poleBlocSup, Nat.cast_inj] at h_re
  exact h_re

theorem ordreSpectralIntraPalier_gammaAlign_preproof
    (γ : ℕ → ℂ)
    (m : ℕ → ℕ)
    (n₁ : ℕ) :
    OrdreSpectralIntraPalier (gammaAlign γ n₁) (mAlign m n₁) := by
  refine
    { paire_ouverte := ?_
      paire_fermee := ?_
      pas_reel_apres_paire := ?_ }
  · intro n₀ n _hn₀3 hn₀n h_im_n₀ h_first hEven _h_im_n
    have hn₀_eq : n₀ = seuilSpectral n₁ :=
      eq_seuilSpectral_of_first_nonreal γ n₁ n₀ h_im_n₀ h_first
    subst hn₀_eq
    have h_mod_even : (n - seuilSpectral n₁) % 2 = 0 := Nat.even_iff.mp hEven
    have h_n1_ge : seuilSpectral n₁ ≤ n + 1 := by omega
    have h_mod_odd : (n + 1 - seuilSpectral n₁) % 2 = 1 := by omega
    have h_div_eq : (n + 1 - seuilSpectral n₁) / 2 = (n - seuilSpectral n₁) / 2 := by omega
    refine ⟨?_, ?_, ?_⟩
    · unfold gammaAlign
      have hnot_n : ¬ (n < seuilSpectral n₁) := not_lt.mpr hn₀n
      have hnot_n1 : ¬ (n + 1 < seuilSpectral n₁) := not_lt.mpr h_n1_ge
      rw [ite_eq_right hnot_n1, ite_eq_right hnot_n]
      dsimp only
      have h_ne_zero : (n + 1 - seuilSpectral n₁) % 2 ≠ 0 := by omega
      rw [ite_eq_right h_ne_zero, ite_eq_left h_mod_even, h_div_eq]
    · unfold mAlign
      have hnot_n : ¬ (n < seuilSpectral n₁) := not_lt.mpr hn₀n
      have hnot_n1 : ¬ (n + 1 < seuilSpectral n₁) := not_lt.mpr h_n1_ge
      rw [ite_eq_right hnot_n1, ite_eq_right hnot_n]
      dsimp only
      rw [h_div_eq]
    · intro h_eq_prev
      rcases eq_or_lt_of_le hn₀n with h_eq_S | h_gt_S
      · have h_prev_lt : n - 1 < seuilSpectral n₁ := by omega
        have h_im_prev_zero : (gammaAlign γ n₁ (n - 1)).im = 0 :=
          gammaAlign_im_eq_zero_of_lt γ n₁ (n - 1) h_prev_lt
        have h_im_eq := congrArg Complex.im h_eq_prev
        have h_im_n_pos : 0 < (gammaAlign γ n₁ n).im :=
          gammaAlign_im_pos_of_even γ n₁ n hn₀n h_mod_even
        rw [h_im_prev_zero, Complex.conj_im] at h_im_eq
        linarith
      · exact not_conj_prev_of_even_gt_seuil_inj γ n₁ n hn₀n h_gt_S h_mod_even
          (poleBlocSup_injective γ n₁)
          h_eq_prev
  · intro n₀ n _hn₀3 hn₀n h_im_n₀ h_first hOdd _h_im_n
    have hn₀_eq : n₀ = seuilSpectral n₁ :=
      eq_seuilSpectral_of_first_nonreal γ n₁ n₀ h_im_n₀ h_first
    subst hn₀_eq
    have h_mod_odd : (n - seuilSpectral n₁) % 2 = 1 := Nat.odd_iff.mp hOdd
    have h_n_ne_zero : (n - seuilSpectral n₁) % 2 ≠ 0 := by omega
    have h_prev_ge : seuilSpectral n₁ ≤ n - 1 := by omega
    have h_prev_even : (n - 1 - seuilSpectral n₁) % 2 = 0 := by omega
    have h_div_eq : (n - 1 - seuilSpectral n₁) / 2 = (n - seuilSpectral n₁) / 2 := by omega
    have hnot_prev : ¬ (n - 1 < seuilSpectral n₁) := not_lt.mpr h_prev_ge
    have hnot_n : ¬ (n < seuilSpectral n₁) := not_lt.mpr hn₀n
    unfold gammaAlign
    rw [ite_eq_right hnot_prev, ite_eq_right hnot_n]
    dsimp only
    rw [ite_eq_left h_prev_even, ite_eq_right h_n_ne_zero, h_div_eq]
    exact (Complex.conj_conj (poleBlocSup γ n₁ ((n - seuilSpectral n₁) / 2))).symm
  · intro n _hn3 h_im_n _h_prev
    have h_ge : seuilSpectral n₁ ≤ n := (gammaAlign_im_ne_zero_iff γ n₁ n).mp h_im_n
    have h_ge_next : seuilSpectral n₁ ≤ n + 1 := by omega
    exact gammaAlign_im_ne_zero_of_ge γ n₁ (n + 1) h_ge_next

theorem ordreSpectralIntraPalier_gammaAlign
    (γ : ℕ → ℂ)
    (m : ℕ → ℕ)
    (n₁ : ℕ) :
    OrdreSpectralIntraPalier (gammaAlign γ n₁) (mAlign m n₁) :=
  ordreSpectralIntraPalier_gammaAlign_preproof γ m n₁


lemma conjCompat'_of_first_preproof
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hOrdre : OrdreSpectralIntraPalier γ m)
    (hconj : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n) :
    ConjCompatible' γ m :=
  conjCompat'_of_first_preProof hEnum hconj hOrdre

lemma conjCompat'_of_first_autre
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hAlign : ∀ n₁, 1 ≤ n₁ → (γ n₁).im ≠ 0 →
      gammaAlign γ n₁ = γ ∧ mAlign m n₁ = m)
    (hconj : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n) :
    ConjCompatible' γ m := by
  by_cases h_all_real : ∀ j ≥ 1, (γ j).im = 0
  · refine ⟨fun n hn hne _hprev => absurd (h_all_real n (by omega)) hne⟩
  · push Not at h_all_real
    obtain ⟨n₁, hn₁_ge, hn₁_im⟩ := h_all_real
    have hOrdreAlign : OrdreSpectralIntraPalier (gammaAlign γ n₁) (mAlign m n₁) :=
      ordreSpectralIntraPalier_gammaAlign γ m n₁
    obtain ⟨h_eq_γ, h_eq_m⟩ := hAlign n₁ hn₁_ge hn₁_im
    rw [h_eq_γ, h_eq_m] at hOrdreAlign
    exact conjCompat'_of_first_preProof hEnum hconj hOrdreAlign


end EndRiemannProof
