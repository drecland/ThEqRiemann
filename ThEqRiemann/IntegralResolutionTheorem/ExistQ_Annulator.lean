import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.IntegralProp
import ThEqRiemann.IntegralResolutionTheorem.DefPosHankelResInt
import ThEqRiemann.EqTheorem.Vandermonde
/-! -/
namespace ExistQ

open Matrix Complex
open scoped ComplexConjugate ComplexOrder
open ResDef


lemma hk_succ_eq_hankel (m : ℕ → ℝ) (N : ℕ) :
  hk m (N + 1) = hankel' m N := by
  rfl

lemma hk_posDef_of_le (m : ℕ → ℝ) {k N : ℕ} (hkN : k ≤ N)
    (h : (hk m N).PosDef) : (hk m k).PosDef := by
  have hsub : (hk m k) = (hk m N).submatrix (Fin.castLE hkN)
    (Fin.castLE hkN) := by
    ext i j
    simp [hk, Matrix.submatrix]
  rw [hsub]
  exact h.submatrix (Fin.castLE_injective hkN)

lemma hk_isUnit_det_of_posDef (m : ℕ → ℝ) (k : ℕ)
    (h : (hk m k).PosDef) : IsUnit (hk m k).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp h.isUnit

lemma hk_eq_map_hkR (m : ℕ → ℝ) (k : ℕ) :
    hk m k = (hkR m k).map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  simp [hk, hkR]

lemma hk_det_ne_zero (m : ℕ → ℝ) (k : ℕ) (h : (hk m k).PosDef) :
    (hk m k).det ≠ 0 := by
  have hu : IsUnit (hk m k) := h.isUnit
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu |>.ne_zero

lemma hk_mulVec_eq_zero (m : ℕ → ℝ) (k : ℕ) (h : (hk m k).PosDef)
    (x : Fin k → ℂ) (hx : (hk m k) *ᵥ x = 0) : x = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero (hk_det_ne_zero m k h) hx

lemma hkR_det_ne_zero (m : ℕ → ℝ) (k : ℕ) (h : (hk m k).PosDef) :
    (hkR m k).det ≠ 0 := by
  intro h0
  apply hk_det_ne_zero m k h
  have key : ((hkR m k).map (algebraMap ℝ ℂ)).det =
    algebraMap ℝ ℂ (hkR m k).det :=
    (RingHom.map_det (algebraMap ℝ ℂ) (hkR m k)).symm
  have hmap : hk m k = (hkR m k).map (algebraMap ℝ ℂ) := by
    ext i j
    simp [hk, hkR]
  rw [hmap, key, h0]
  simp

lemma hkR_posDef (m : ℕ → ℝ) (k : ℕ) (h : (hk m k).PosDef) :
    (hkR m k).PosDef := by
  refine ⟨?_, ?_⟩
  · ext i j
    simp [hkR, Matrix.conjTranspose_apply, add_comm]
  · intro x hx
    set x' : Fin k →₀ ℂ :=
      Finsupp.mapRange (fun r : ℝ => (r : ℂ)) (by simp) x with hx'
    have hx'0 : x' ≠ 0 := by
      intro h0
      apply hx
      ext i
      have := congrArg (fun f => f i) h0
      simpa [hx'] using this
    have hpos := h.2 hx'0
    have hq :
        (x'.sum fun i xi => x'.sum fun j xj => star xi * hk m k i j * xj)
          = ((x.sum fun i xi => x.sum fun j xj => star xi * hkR m k i j * xj : ℝ) : ℂ) := by
      have hxi : ∀ i, x' i = (x i : ℂ) := by
        intro i
        simp [hx']
      have h1 : ∀ i : Fin k,
          (x'.sum fun j xj => star (x' i) * hk m k i j * xj)
            = ∑ j : Fin k, star (x' i) * hk m k i j * x' j := by
        intro i
        exact Finsupp.sum_fintype x' (fun j xj => star (x' i) * hk m k i j * xj)
          (by intro j; simp)
      have h2 :
          (x'.sum fun i xi => x'.sum fun j xj => star xi * hk m k i j * xj)
            = ∑ i : Fin k, ∑ j : Fin k, star (x' i) * hk m k i j * x' j := by
        rw [Finsupp.sum_fintype x' _ (by intro i; simp)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact h1 i
      have h3 : ∀ i : Fin k,
          (x.sum fun j xj => star (x i) * hkR m k i j * xj)
            = ∑ j : Fin k, star (x i) * hkR m k i j * x j := by
        intro i
        exact Finsupp.sum_fintype x (fun j xj => star (x i) * hkR m k i j * xj)
          (by intro j; simp)
      have h4 :
          (x.sum fun i xi => x.sum fun j xj => star xi * hkR m k i j * xj)
            = ∑ i : Fin k, ∑ j : Fin k, star (x i) * hkR m k i j * x j := by
        rw [Finsupp.sum_fintype x _ (by intro i; simp)]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        exact h3 i
      rw [h2, h4]
      push_cast
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      simp [hxi, hk, hkR]
    rw [hq] at hpos
    simpa using hpos


lemma hkR_det_isUnit (m : ℕ → ℝ) (k : ℕ) (h : (hk m k).PosDef) :
    IsUnit (hkR m k).det := by
  have hR := hkR_posDef m k h
  exact isUnit_iff_ne_zero.mpr (ne_of_gt hR.det_pos)

lemma exists_unique_coeffs (m : ℕ → ℝ) (k : ℕ) (h : (hk m k).PosDef) :
    ∃! a : Fin k → ℝ, ∀ i : Fin k,
      ∑ j : Fin k, a j * m (i.val + j.val) = m (k + i.val) := by
  set b : Fin k → ℝ := fun i => m (k + i.val) with hb
  have hunit : IsUnit (hkR m k).det := hkR_det_isUnit m k h
  have hinvertible : IsUnit (hkR m k) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hunit
  have hsol : (hkR m k) *ᵥ ((hkR m k)⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hline : ∀ a : Fin k → ℝ,
      (hkR m k) *ᵥ a = b ↔
      ∀ i : Fin k, ∑ j : Fin k, a j * m (i.val + j.val) =
        m (k + i.val) := by
    intro a
    constructor
    · intro hmul i
      have := congrFun hmul i
      simp only [Matrix.mulVec, dotProduct,
        hkR, Matrix.of_apply, hb] at this
      simpa [mul_comm] using this
    · intro hall
      ext i
      have := hall i
      simp only [Matrix.mulVec, dotProduct, hkR, Matrix.of_apply, hb]
      simpa [mul_comm] using this
  refine ⟨(hkR m k)⁻¹ *ᵥ b, (hline _).mp hsol, ?_⟩
  intro a' ha'
  have h1 : (hkR m k) *ᵥ a' = b := (hline a').mpr ha'
  calc a' = (hkR m k)⁻¹ *ᵥ ((hkR m k) *ᵥ a') := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
          Matrix.one_mulVec]
    _ = (hkR m k)⁻¹ *ᵥ b := by rw [h1]

-----------------------------------------------------------------------

lemma rec_of_coeffs (m : ℕ → ℝ) (k : ℕ) (a : Fin k → ℝ)
    (ha : ∀ i : Fin k, ∑ j : Fin k, a j * m
    (i.val + j.val) = m (k + i.val))
    (n : ℕ) (hn : n < k) :
    m (n + k) = ∑ j : Fin k, a j * m (n + (j : ℕ)) := by
  have := ha ⟨n, hn⟩
  simpa [add_comm] using this.symm

lemma leading_coeff_ne_zero (m : ℕ → ℝ) (D : ℕ) (h : (hk m D).PosDef)
    (b : Fin (D + 1) → ℂ) (hb : b ≠ 0) (hker : (hk m (D + 1)) *ᵥ b = 0) :
    b (Fin.last D) ≠ 0 := by
  intro hlast
  apply hb
  set b' : Fin D → ℂ := fun i => b (Fin.castSucc i) with hb'
  have hrows : (hk m D) *ᵥ b' = 0 := by
    ext i
    have h1 := congrFun hker (Fin.castSucc i)
    rw [Matrix.mulVec, dotProduct] at h1 ⊢
    rw [Fin.sum_univ_castSucc, hlast, mul_zero, add_zero] at h1
    simpa [hk, hb'] using h1
  have hb'0 : b' = 0 := hk_mulVec_eq_zero m D h b' hrows
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using hlast
  · simpa [hb'] using congrFun hb'0 j

lemma exists_kernel_of_det_zero (m : ℕ → ℝ) (D : ℕ)
    (hdetR : (hkR m (D + 1)).det = 0) :
    ∃ b : Fin (D + 1) → ℝ, b ≠ 0 ∧ (hkR m (D + 1)) *ᵥ b = 0 :=
  Matrix.exists_mulVec_eq_zero_iff.mpr hdetR

lemma hkR_det_zero_of_hk (m : ℕ → ℝ) (k : ℕ) (h : (hk m k).det = 0) :
    (hkR m k).det = 0 := by
  have h1 : (Complex.ofRealHom (hkR m k).det) = (hk m k).det := by
    rw [hk_eq_map_hkR, RingHom.map_det]; rfl
  have h2 : Complex.ofRealHom (hkR m k).det = 0 := h1.trans h
  exact (map_eq_zero Complex.ofRealHom).mp h2


open MeasureTheory

lemma quad_form_eq_integral (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (D : ℕ) (b : Fin (D + 1) → ℝ) :
    ∑ i, ∑ j, b i * m (i.val + j.val) * b j
      = ∫ x in Set.Icc (0 : ℝ) 1, (∑ j : Fin (D + 1), b j * x ^ j.val) ^ 2 ∂μ := by
  obtain ⟨hfin, hmom⟩ := hμ
  have hint : ∀ n : ℕ, IntegrableOn (fun x : ℝ => x ^ n) (Set.Icc (0 : ℝ) 1) μ := by
    intro n
    have _ : IsFiniteMeasure μ := hfin.finite
    exact (continuous_pow n).continuousOn.integrableOn_compact isCompact_Icc
  have hexp : ∀ x : ℝ, (∑ j : Fin (D + 1), b j * x ^ j.val) ^ 2
      = ∑ i : Fin (D + 1), ∑ j : Fin (D + 1), b i * b j * x ^ (i.val + j.val) := by
    intro x
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [pow_add]; ring
  simp_rw [hexp]
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => ?_)]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_finsetSum _ (fun j _ => ?_)]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_const_mul, ← hmom]
      ring
    · exact ((hint _).const_mul _)
  · exact MeasureTheory.integrable_finsetSum _ (fun j _ => (hint _).const_mul _)

lemma poly_ae_zero (μ : Measure ℝ) [IsFiniteMeasure μ]
    (P : ℝ → ℝ) (_ : Continuous P)
    (hint : Integrable (fun x => (P x) ^ 2) μ)
    (h0 : ∫ x, (P x) ^ 2 ∂μ = 0) :
    ∀ᵐ x ∂μ, P x = 0 := by
  have hnn : 0 ≤ᵐ[μ] fun x => (P x) ^ 2 := Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp h0
  filter_upwards [this] with x hx
  exact pow_eq_zero_iff (two_ne_zero) |>.mp hx


lemma card_support_ge (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (D : ℕ)
    (hpos : (hk m D).PosDef) (S : Finset ℝ)
    (hS : μ ((S : Set ℝ)ᶜ) = 0) : D ≤ S.card := by
  by_contra hlt
  push Not at hlt
  set R : Polynomial ℝ := ∏ s ∈ S, (Polynomial.X - Polynomial.C s) with hR
  have hRne : R ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun s _ => Polynomial.X_sub_C_ne_zero s)
  have hdeg : R.natDegree < D := by
    rw [hR, Polynomial.natDegree_prod_of_monic _ _
      (fun s _ => Polynomial.monic_X_sub_C s)]
    simpa using hlt
  set c : Fin D → ℝ := fun i => R.coeff i.val with hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply hRne
    apply Polynomial.ext
    intro n
    by_cases hn : n < D
    · have := congrFun h0 ⟨n, hn⟩
      simpa [hc] using this
    · have : R.natDegree < n := lt_of_lt_of_le hdeg (not_lt.mp hn)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt this, Polynomial.coeff_zero]
  have heval : ∀ x : ℝ, R.eval x = ∑ i : Fin D, c i * x ^ i.val := by
    intro x
    rw [Polynomial.eval_eq_sum_range' hdeg]
    exact (Fin.sum_univ_eq_sum_range (fun i => R.coeff i * x ^ i) D).symm
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  have hquad := quad_form_eq_integral m μ hμ d c
  have hint0 : ∫ x in Set.Icc (0 : ℝ) 1,
      (∑ j : Fin (d + 1), c j * x ^ j.val) ^ 2 ∂μ = 0 := by
    have hae : ∀ᵐ x ∂μ, x ∈ (S : Set ℝ) := by
      rw [ae_iff]; exact hS
    refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hae] with x hx
    have hRx : R.eval x = 0 := by
      rw [hR, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_coe.mp hx) (by simp)
    rw [← heval x, hRx]; simp
  have hRpos := hkR_posDef m (d + 1) hpos
  have hlt0 : 0 < ∑ i, ∑ j, c i * m (i.val + j.val) * c j := by
    set x : Fin (d + 1) →₀ ℝ := Finsupp.equivFunOnFinite.symm c with hx
    have hx0 : x ≠ 0 := by
      intro h0
      apply hc0
      ext i
      have := congrArg (fun f : Fin (d + 1) →₀ ℝ => f i) h0
      simpa [hx] using this
    have h := hRpos.2 hx0
    rw [Finsupp.sum_fintype _ _ (fun i => by simp)] at h
    have hin : ∀ i : Fin (d + 1),
        (x.sum fun j xj => star (x i) * hkR m (d + 1) i j * xj)
          = ∑ j : Fin (d + 1), star (x i) * hkR m (d + 1) i j * x j := by
      intro i
      exact Finsupp.sum_fintype x
        (fun j xj => star (x i) * hkR m (d + 1) i j * xj)
        (fun j => by simp)
    simp only [hin] at h
    have hxc : ∀ i, x i = c i := fun i => by simp [hx]
    simp only [hxc, star_trivial, hkR, Matrix.of_apply] at h
    exact h
  rw [hquad, hint0] at hlt0
  exact lt_irrefl _ hlt0


lemma hk_mulVec_ofReal_eq_zero (m : ℕ → ℝ) (D : ℕ) (b : Fin (D + 1) → ℝ)
    (hbker : (hkR m (D + 1)) *ᵥ b = 0) :
    (hk m (D + 1)) *ᵥ (fun i => (b i : ℂ)) = 0 := by
  ext i
  have h1 := congrFun hbker i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1 ⊢
  have h2 : ((∑ j, hkR m (D + 1) i j * b j : ℝ) : ℂ) = 0 := by
    rw [h1]; simp
  push_cast at h2
  simpa [hk, hkR] using h2

lemma real_kernel_leading_ne_zero (m : ℕ → ℝ) (D : ℕ) (hpos : (hk m D).PosDef)
    (b : Fin (D + 1) → ℝ) (hb0 : b ≠ 0) (hbker : (hkR m (D + 1)) *ᵥ b = 0) :
    b (Fin.last D) ≠ 0 := by
  have hbC : (fun i => (b i : ℂ)) ≠ 0 := by
    intro h0; apply hb0; ext i
    have := congrFun h0 i
    simpa using this
  have := leading_coeff_ne_zero m D hpos _ hbC (hk_mulVec_ofReal_eq_zero m D b hbker)
  simpa using this

lemma polyOfVec_eval {D : ℕ} (b : Fin (D + 1) → ℝ) (x : ℝ) :
    (polyOfVec b).eval x = ∑ j : Fin (D + 1), b j * x ^ j.val := by
  simp [polyOfVec, Polynomial.eval_finsetSum]

lemma polyOfVec_coeff_last {D : ℕ} (b : Fin (D + 1) → ℝ) :
    (polyOfVec b).coeff D = b (Fin.last D) := by
  rw [polyOfVec, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single (Fin.last D)]
  · simp
  · intro j _ hj
    have : (j : ℕ) ≠ D := fun h => hj (Fin.ext (by simpa using h))
    simp [this.symm]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma polyOfVec_ne_zero {D : ℕ} (b : Fin (D + 1) → ℝ) (hb : b (Fin.last D) ≠ 0) :
    polyOfVec b ≠ 0 := by
  intro h0
  apply hb
  have h := polyOfVec_coeff_last b
  rw [h0, Polynomial.coeff_zero] at h
  exact h.symm

lemma polyOfVec_natDegree_le {D : ℕ} (b : Fin (D + 1) → ℝ) :
    (polyOfVec b).natDegree ≤ D := by
  rw [polyOfVec]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)


lemma atom_weight_pos (m : ℕ → ℝ) (μ : Measure ℝ) (hμ : IsIntegralResolution m μ)
    (D : ℕ) (hpos : (hk m D).PosDef) (S : Finset ℝ)
    (hSmeas : μ ((S : Set ℝ)ᶜ) = 0) (hScard : S.card = D) (s : ℝ) (hs : s ∈ S) :
    0 < (μ {s}).toReal := by
  have _ := hμ.1.finite
  have hne : μ {s} ≠ 0 := by
    intro h0
    have hS' : μ (((S.erase s : Finset ℝ) : Set ℝ)ᶜ) = 0 := by
      have hsub : (((S.erase s : Finset ℝ) : Set ℝ)ᶜ) ⊆ (S : Set ℝ)ᶜ ∪ {s} := by
        intro x hx
        by_cases hxs : x = s
        · right; exact hxs
        · left
          intro hxS
          exact hx (by simp [hxs, Finset.mem_coe.mp hxS])
      exact measure_mono_null hsub (measure_union_null hSmeas h0)
    have hcard := card_support_ge m μ hμ D hpos _ hS'
    rw [Finset.card_erase_of_mem hs] at hcard
    have hSpos : 0 < S.card := Finset.card_pos.mpr ⟨s, hs⟩
    omega
  exact ENNReal.toReal_pos hne (measure_ne_top μ _)

open IntProp in
lemma critical_order_support (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (D : ℕ) (_ : 1 ≤ D)
    (hpos : (hk m D).PosDef) (hdet : (hk m (D + 1)).det = 0) :
    ∃ (pts : Fin D → ℝ) (w : Fin D → ℝ),
      Function.Injective pts ∧ (∀ i, pts i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, 0 < w i) ∧ ∀ k, m k = ∑ i, w i * pts i ^ k := by
  have _ := hμ.1.finite
  obtain ⟨b, hb0, hbker⟩ :=
    exists_kernel_of_det_zero m D (hkR_det_zero_of_hk m (D + 1) hdet)
  have hquad : ∑ i, ∑ j, b i * m (i.val + j.val) * b j = 0 := by
    have : star b ⬝ᵥ (hkR m (D + 1)) *ᵥ b = 0 := by rw [hbker]; simp
    simpa [dotProduct, Matrix.mulVec, hkR, Finset.mul_sum, mul_assoc,
      mul_comm, mul_left_comm] using this
  have hint0 := quad_form_eq_integral m μ hμ D b
  rw [hquad] at hint0
  have hbD := real_kernel_leading_ne_zero m D hpos b hb0 hbker
  have hQne : polyOfVec b ≠ 0 := polyOfVec_ne_zero b hbD
  have hz : ∫ x in Set.Icc (0:ℝ) 1, ((polyOfVec b).eval x) ^ 2 ∂μ = 0 := by
    simp only [polyOfVec_eval]; exact hint0.symm
  have hae0 := poly_sq_ae_zero μ hμ.1 (polyOfVec b) hz
  set S : Finset ℝ :=
    (polyOfVec b).roots.toFinset.filter (fun x => x ∈ Set.Icc (0:ℝ) 1) with hS
  have hSmeas : μ ((S : Set ℝ)ᶜ) = 0 := measure_compl_roots_Icc μ hμ.1 _ hQne hae0
  have hScard : S.card = D :=
    le_antisymm (card_roots_Icc_le _ D (polyOfVec_natDegree_le b))
      (card_support_ge m μ hμ D hpos S hSmeas)
  have hSsub : (S : Set ℝ) ⊆ Set.Icc (0:ℝ) 1 := fun x hx =>
    (Finset.mem_filter.mp hx).2
  let e : Fin D ≃ S := (Fintype.equivFinOfCardEq (by simpa using hScard)).symm
  refine ⟨fun i => (e i : ℝ), fun i => (μ {(e i : ℝ)}).toReal, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact hSsub (e i).2
  · intro i
    exact atom_weight_pos m μ hμ D hpos S hSmeas hScard _ (e i).2
  · intro k
    rw [hμ.2 k, integral_pow_finite_support μ S hSsub hSmeas k]
    rw [← Finset.sum_coe_sort S]
    exact Fintype.sum_equiv e.symm _ _ (fun s => by simp [mul_comm])


lemma rec_of_atoms {r D : ℕ} (m : ℕ → ℝ) (pts w : Fin r → ℝ) (a : Fin D → ℝ)
    (hm : ∀ k, m k = ∑ i, w i * pts i ^ k)
    (hQ : ∀ i, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0) (n : ℕ) :
    m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ)) := by
  simp only [hm]
  have key : ∀ i, w i * pts i ^ (n + D)
      = ∑ j : Fin D, a j * (w i * pts i ^ (n + (j : ℕ))) := by
    intro i
    have h := hQ i
    have h' : pts i ^ D = ∑ j : Fin D, a j * pts i ^ (j : ℕ) := by linarith
    calc w i * pts i ^ (n + D)
        = w i * pts i ^ n * pts i ^ D := by ring
      _ = w i * pts i ^ n * ∑ j : Fin D, a j * pts i ^ (j : ℕ) := by rw [h']
      _ = ∑ j : Fin D, a j * (w i * pts i ^ (n + (j : ℕ))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          ring
  calc ∑ i, w i * pts i ^ (n + D)
      = ∑ i, ∑ j : Fin D, a j * (w i * pts i ^ (n + (j : ℕ))) :=
          Finset.sum_congr rfl (fun i _ => key i)
    _ = ∑ j : Fin D, ∑ i, a j * (w i * pts i ^ (n + (j : ℕ))) := Finset.sum_comm
    _ = ∑ j : Fin D, a j * ∑ i, w i * pts i ^ (n + (j : ℕ)) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [Finset.mul_sum]


open DefPosHankelRes in
lemma support_card_ge (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (N : ℕ)
    (hpos : (hk m (N + 1)).PosDef) :
    ¬ ∃ T : Finset ℝ, T.card ≤ N ∧ μ (Set.Icc (0 : ℝ) 1 \ (T : Set ℝ)) = 0 := by
  rintro ⟨T, hT, hμT⟩
  have hH : (hankel' m N).PosDef := by simpa [hk_succ_eq_hankel] using hpos
  have := (positivite_hankel_resolution m μ hμ N).2.mp hH
  -- Polynôme `P = ∏_{t ∈ T} (X - C t)` : non nul, de degré `T.card ≤ N`.
  set P : Polynomial ℂ := ∏ t ∈ T, (Polynomial.X - Polynomial.C ((t : ℝ) : ℂ)) with hP
  have hP0 : P ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun t _ => Polynomial.X_sub_C_ne_zero _)
  have hPdeg : P.natDegree ≤ N := by
    have : P.natDegree = T.card := by
      simp [hP]
    omega
  have hlt := this P hP0 hPdeg
  -- (a) T ⊆ zéros de P : chaque t ∈ T annule le facteur (X - C t).
  have hTZ : ∀ t ∈ T, Polynomial.eval ((t : ℝ) : ℂ) P = 0 := by
    intro t ht
    rw [hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero ht (by simp)
  -- (b) Icc 0 1 ⊆ (zéros ∩ Icc) ∪ (Icc \ T)
  have hsub : Set.Icc (0 : ℝ) 1 ⊆
      ({x : ℝ | Polynomial.eval ((x : ℝ) : ℂ) P = 0} ∩ Set.Icc (0 : ℝ) 1)
        ∪ (Set.Icc (0 : ℝ) 1 \ (T : Set ℝ)) := by
    intro x hx
    by_cases hxT : x ∈ (T : Set ℝ)
    · left
      exact ⟨hTZ x (Finset.mem_coe.mp hxT), hx⟩
    · right
      exact ⟨hx, hxT⟩
  -- (c) sous-additivité : μ (Icc) ≤ μ (zéros ∩ Icc) + 0
  have hle : μ (Set.Icc (0 : ℝ) 1) ≤
      μ ({x : ℝ | Polynomial.eval ((x : ℝ) : ℂ) P = 0} ∩ Set.Icc (0 : ℝ) 1) := by
    calc μ (Set.Icc (0 : ℝ) 1)
        ≤ μ (({x : ℝ | Polynomial.eval ((x : ℝ) : ℂ) P = 0} ∩ Set.Icc (0 : ℝ) 1)
            ∪ (Set.Icc (0 : ℝ) 1 \ (T : Set ℝ))) := measure_mono hsub
      _ ≤ μ ({x : ℝ | Polynomial.eval ((x : ℝ) : ℂ) P = 0} ∩ Set.Icc (0 : ℝ) 1)
            + μ (Set.Icc (0 : ℝ) 1 \ (T : Set ℝ)) := measure_union_le _ _
      _ = μ ({x : ℝ | Polynomial.eval ((x : ℝ) : ℂ) P = 0} ∩ Set.Icc (0 : ℝ) 1) := by
          rw [hμT, add_zero]
  exact absurd hlt (not_lt.mpr hle)


lemma atoms_root_and_rec (m : ℕ → ℝ) (D : ℕ) (pts w : Fin D → ℝ)
    (hw : ∀ i, 0 < w i)
    (hm : ∀ k, m k = ∑ i, w i * pts i ^ k)
    (a : Fin D → ℝ)
    (ha : ∀ i : Fin D, ∑ j : Fin D, a j * m (i.val + j.val) = m (D + i.val))
    (hV : ∀ v : Fin D → ℝ, (∀ l : Fin D, ∑ i, v i * pts i ^ (l : ℕ) = 0) → v = 0) :
    (∀ i : Fin D, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0) ∧
    (∀ n : ℕ, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ))) := by
  set q : Fin D → ℝ := fun i => pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) with hq
  have h1 : ∀ l : Fin D, ∑ i, (w i * q i) * pts i ^ (l : ℕ)
      = m (D + l) - ∑ j : Fin D, a j * m (l + j) := by
    intro l
    have hterm : ∀ i : Fin D, (w i * q i) * pts i ^ (l : ℕ)
        = w i * pts i ^ (D + (l : ℕ))
          - ∑ j : Fin D, a j * (w i * pts i ^ ((l : ℕ) + (j : ℕ))) := by
      intro i
      have e : ∑ j : Fin D, a j * (w i * pts i ^ ((l : ℕ) + (j : ℕ)))
          = (w i * pts i ^ (l : ℕ)) * ∑ j : Fin D, a j * pts i ^ (j : ℕ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [pow_add]; ring
      rw [e, hq]
      simp only
      rw [pow_add]; ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
    congr 1
    · rw [hm (D + (l : ℕ))]
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hm ((l : ℕ) + (j : ℕ)), Finset.mul_sum]
  have horth : ∀ l : Fin D, ∑ i, (w i * q i) * pts i ^ (l : ℕ) = 0 := by
    intro l
    rw [h1 l, ← ha l]
    simp
  have hvec : (fun i => w i * q i) = 0 := hV _ horth
  have hroot : ∀ i : Fin D, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0 := by
    intro i
    have h0 : w i * q i = 0 := congrFun hvec i
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (hw i).ne'
    · exact h
  refine ⟨hroot, ?_⟩
  intro n
  rw [hm (n + D)]
  have hterm : ∀ i : Fin D, w i * pts i ^ (n + D)
      = ∑ j : Fin D, a j * (w i * pts i ^ (n + (j : ℕ))) := by
    intro i
    have h' : pts i ^ D = ∑ j : Fin D, a j * pts i ^ (j : ℕ) :=
      sub_eq_zero.mp (hroot i)
    calc w i * pts i ^ (n + D)
        = (w i * pts i ^ n) * pts i ^ D := by rw [pow_add]; ring
      _ = (w i * pts i ^ n) * ∑ j : Fin D, a j * pts i ^ (j : ℕ) := by rw [← h']
      _ = ∑ j : Fin D, a j * (w i * pts i ^ (n + (j : ℕ))) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [pow_add]; ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hm (n + (j : ℕ)), Finset.mul_sum]


open VandermondeThEq in
theorem polynome_Q_complet (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (N : ℕ) (hN : 1 ≤ N)
    (hpos : (hk m N).PosDef) :
    (∀ k ≤ N, (hk m k).PosDef) ∧
    (∀ k ≤ N, ∃! a : Fin k → ℝ, ∀ i : Fin k,
        ∑ j : Fin k, a j * m (i.val + j.val) = m (k + i.val)) ∧
    ((∃ D : ℕ, 1 ≤ D ∧ D < N ∧ (hk m (D + 1)).det = 0 ∧
        ∃ (a : Fin D → ℝ) (pts w : Fin D → ℝ),
          Function.Injective pts ∧ (∀ i, pts i ∈ Set.Icc (0 : ℝ) 1) ∧
          (∀ i, 0 < w i) ∧ (∀ k, m k = ∑ i, w i * pts i ^ k) ∧
          (∀ i, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0) ∧
          (∀ n, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ)))) ∨
     (¬ ∃ T : Finset ℝ, T.card ≤ N - 1 ∧
        μ (Set.Icc (0 : ℝ) 1 \ (T : Set ℝ)) = 0)) := by
  refine ⟨fun k hk' => hk_posDef_of_le m hk' hpos,
          fun k hk' => exists_unique_coeffs m k (hk_posDef_of_le m hk' hpos), ?_⟩
  by_cases hex : ∃ D : ℕ, 1 ≤ D ∧ D < N ∧ (hk m (D + 1)).det = 0
  · left
    obtain ⟨D, hD1, hDN, hdet⟩ := hex
    have hposD : (hk m D).PosDef := hk_posDef_of_le m hDN.le hpos
    obtain ⟨pts, w, hinj, hmem, hw, hm⟩ :=
      critical_order_support m μ hμ D hD1 hposD hdet
    obtain ⟨a, ha, -⟩ := exists_unique_coeffs m D hposD
    have hV := vandermonde_inj_zero D pts hinj
    obtain ⟨hroot, hrec⟩ := atoms_root_and_rec m D pts w hw hm a ha hV
    exact ⟨D, hD1, hDN, hdet, a, pts, w, hinj, hmem, hw, hm, hroot, hrec⟩
  · right
    push Not at hex
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simpa using support_card_ge m μ hμ N' hpos

end ExistQ
