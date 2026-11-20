import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.GammaProp
import ThEqRiemann.RiemannProof.XiEntiereProp
import ThEqRiemann.RiemannProof.Lambda0Prop
import ThEqRiemann.EqTheorem.Vandermonde
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.SpectralSupportHankel
import ThEqRiemann.IntegralResolutionTheorem.CriteriumNewtonColinearity
import ThEqRiemann.RiemannProof.InductionStrongZeros
import ThEqRiemann.RiemannProof.InductionCanoniqueOperator
/-! -/
namespace ExhaustionHankel

open Set Complex
open RiemannDef GammaRiemann XiEntiereRiemann LambdaRiemann
open scoped ComplexConjugate ComplexOrder

lemma exists_exhaustion :
    ∃ E : ℕ → Finset ℂ,
      (∀ N, ↑(E N) ⊆ LambdaZeros) ∧
      (∀ N, E N ⊆ E (N + 1)) ∧
      (∀ γ ∈ LambdaZeros, ∃ N, γ ∈ E N) ∧
      (∀ N γ, γ ∈ E N → (starRingEnd ℂ) γ ∈ E N) := by
  classical
  refine ⟨fun N => (lambdaZeros_finite_ball (N : ℝ)).toFinset, ?_, ?_, ?_, ?_⟩
  · intro N γ hγ
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset] at hγ
    exact hγ.1
  · intro N γ hγ
    simp only [Set.Finite.mem_toFinset] at hγ ⊢
    refine ⟨hγ.1, ?_⟩
    exact Metric.closedBall_subset_closedBall (by push_cast; linarith) hγ.2
  · intro γ hγ
    obtain ⟨N, hN⟩ := exists_nat_ge ‖γ‖
    refine ⟨N, ?_⟩
    simp only [Set.Finite.mem_toFinset]
    exact ⟨hγ, by simpa [Metric.mem_closedBall, dist_zero_right] using hN⟩
  · intro N γ hγ
    simp only [Set.Finite.mem_toFinset] at hγ ⊢
    refine ⟨lambdaZeros_conj hγ.1, ?_⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hγ.2



open ResDef SpecSupportHankel

lemma hankel_posDef_of_real (E : Finset ℝ) :
    (hk (fun k : ℕ => ∑ γ ∈ E, γ ^ k) E.card).PosDef := by
  have e := E.equivFin
  exact posDef_of_atoms _ E.card (fun i => (e.symm i : ℝ)) (fun _ => 1)
    (fun i j h => e.symm.injective (Subtype.ext h))
    (fun _ => one_pos)
    (fun k => by
      simp only [one_mul]
      rw [← Finset.sum_coe_sort E (fun γ => γ ^ k)]
      exact (Equiv.sum_comp e.symm (fun x : E => (x : ℝ) ^ k)).symm)

lemma momentTronque_im_eq_zero (E : Finset ℂ)
    (hconj : ∀ γ ∈ E, (starRingEnd ℂ) γ ∈ E) (k : ℕ) :
    (momentTronque E k).im = 0 := by
  have h : (starRingEnd ℂ) (momentTronque E k) = momentTronque E k := by
    unfold momentTronque
    rw [map_sum]
    simp only [map_pow]
    refine Finset.sum_bij' (fun γ _ => (starRingEnd ℂ) γ)
      (fun γ _ => (starRingEnd ℂ) γ) ?_ ?_ ?_ ?_ ?_
    · intro γ hγ; exact hconj γ hγ
    · intro γ hγ; exact hconj γ hγ
    · intro γ _; exact Complex.conj_conj γ
    · intro γ _; exact Complex.conj_conj γ
    · intro γ _; rfl
  exact Complex.conj_eq_iff_im.mp h


lemma hankel_posDef_of_all_real (E : Finset ℂ) (hreal : ∀ γ ∈ E, γ.im = 0) :
    (hk (fun k => (momentTronque E k).re) E.card).PosDef := by
  classical
  set E' : Finset ℝ := E.image Complex.re with hE'
  have hinj : Set.InjOn Complex.re (E : Set ℂ) := by
    intro a ha b hb hab
    exact Complex.ext hab (by rw [hreal a ha, hreal b hb])
  have hcard : E'.card = E.card := Finset.card_image_of_injOn hinj
  have hmom : (fun k : ℕ => (momentTronque E k).re) = fun k => ∑ γ ∈ E', γ ^ k := by
    funext k
    unfold momentTronque
    rw [hE', Finset.sum_image hinj, Complex.re_sum]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    have : γ = (γ.re : ℂ) := Complex.ext (by simp) (by simp [hreal γ hγ])
    conv_lhs => rw [this]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [hmom]
  have h := hankel_posDef_of_real E'
  rw [hcard] at h
  exact h

lemma hposDef_of_map_complex {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (h : (A.map (fun x : ℝ => (x : ℂ))).PosDef) : A.PosDef := by
  refine ⟨?_, ?_⟩
  · ext i j
    have hij := congrFun (congrFun h.1 i) j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Complex.star_def,
      Complex.conj_ofReal, Complex.ofReal_inj] at hij ⊢
    simp only [star_trivial]
    exact hij
  · intro x hx
    set xc : Fin n →₀ ℂ := x.mapRange (fun r : ℝ => (r : ℂ)) (by simp) with hxc
    have hx' : xc ≠ 0 := by
      intro h0
      apply hx
      ext i
      have := congrArg (fun f : Fin n →₀ ℂ => f i) h0
      simpa [hxc, Finsupp.mapRange_apply] using this
    have hpos := h.2 hx'
    have hsupp : (Finsupp.mapRange (fun r : ℝ => (r : ℂ)) (by simp) x).support = x.support := by
      ext i
      simp [Finsupp.mem_support_iff]
    have key : (xc.sum fun i xi => xc.sum fun j xj => star xi *
      (A.map (fun r : ℝ => (r : ℂ))) i j * xj)
        = (((x.sum fun i xi => x.sum fun j xj => xi * A i j * xj) : ℝ) : ℂ) := by
      rw [hxc, Finsupp.sum_mapRange_index (by simp)]
      simp only [Finsupp.sum, Finsupp.mapRange_apply, Complex.ofReal_sum, Complex.ofReal_mul,
        Matrix.map_apply, Complex.conj_ofReal, Complex.star_def]
      rw [hsupp]
    have hre : (0 : ℝ) < x.sum fun i xi => x.sum fun j xj => xi * A i j * xj := by
      rw [key] at hpos
      exact_mod_cast hpos
    exact hre

open CritColi in
lemma hankel_posDef_iff_real (E : Finset ℂ) (hE : E.Nonempty)
    (hconj : ∀ γ ∈ E, (starRingEnd ℂ) γ ∈ E) :
    (hk (fun k => (momentTronque E k).re) E.card).PosDef ↔ (∀ γ ∈ E, γ.im = 0) := by
  constructor
  · intro hpos
    classical
    set d := E.card with hd
    have hd0 : 0 < d := Finset.card_pos.mpr hE
    let z : Fin d → ℂ := fun j => (E.equivFin.symm j : ℂ)
    have hz : Function.Injective z := by
      intro i j hij
      exact E.equivFin.symm.injective (Subtype.ext hij)
    let m : Fin d → ℕ := fun _ => 1
    have hm : ∀ j, 0 < m j := fun _ => Nat.one_pos
    have hnu : ∀ k, nu
        (fun j => Complex.exp (-((0:ℝ) * Complex.I)) * (z j - 0)) m k
        = momentTronque E k := by
      intro k
      have hw : (fun j => Complex.exp (-((0:ℝ) * Complex.I)) * (z j - 0)) = z := by
        funext j
        simp
      rw [hw]
      unfold nu momentTronque
      simp only [m, Nat.cast_one, one_mul]
      rw [← Finset.sum_coe_sort E (fun γ => γ ^ k)]
      exact Fintype.sum_equiv E.equivFin.symm _ _ (fun j => rfl)
    have hnuR : ∀ k, nuR
        (fun j => Complex.exp (-((0:ℝ) * Complex.I)) * (z j - 0)) m k
        = (momentTronque E k).re := by
      intro k
      unfold nuR
      rw [hnu k]
    have hreal : ∀ k ≤ 2 * d - 1,
        (nu (fun j => Complex.exp (-((0 : ℝ) * Complex.I)) * (z j - 0)) m k).im = 0 := by
      intro k _
      rw [hnu k]
      exact momentTronque_im_eq_zero E hconj k
    have hpos' : (hankel
        (fun j => Complex.exp (-((0:ℝ) * Complex.I)) * (z j - 0)) m).PosDef := by
      have hmat : hankel
          (fun j => Complex.exp (-((0:ℝ) * Complex.I)) * (z j - 0)) m
          = hkR (fun k => (momentTronque E k).re) d := by
        ext p q
        simp only [hankel, hkR, Matrix.of_apply]
        exact hnuR (↑p + ↑q)
      rw [hmat]
      have hmapC : hk (fun k => (momentTronque E k).re) d
          = (hkR (fun k => (momentTronque E k).re) d).map (fun x : ℝ => (x : ℂ)) := by
        ext i j
        simp [hk, hkR]
      rw [hmapC] at hpos
      exact hposDef_of_map_complex hpos
    intro γ hγ
    obtain ⟨j, hj⟩ : ∃ j : Fin d, z j = γ :=
      ⟨E.equivFin ⟨γ, hγ⟩, by simp [z]⟩
    obtain ⟨x, hx⟩ :=
      reciproque_aligned_imp_hankel 0 0 z m hz hm hd0 hreal hpos' j
    rw [← hj, hx]
    simp
  · intro hreal
    exact hankel_posDef_of_all_real E hreal


theorem exhaustion_hankel_riemann
    (E : ℕ → Finset ℂ)
    (hsub : ∀ N, ↑(E N) ⊆ LambdaZeros)
    (hcov : ∀ γ ∈ LambdaZeros, ∃ N, γ ∈ E N) :
    RiemannHypothesisLambda ↔ ∀ N, ∀ γ ∈ E N, γ.im = 0 := by
  constructor
  · intro h N γ hγ
    exact h γ (hsub N hγ)
  · intro h γ hγ
    obtain ⟨N, hN⟩ := hcov γ hγ
    exact h N γ hN

-----------------------------------------------------------------------

open InducStrongZero Matrix

lemma HR_succ_of_posDef (γ : ℕ → ℂ) (n : ℕ) (hn : 2 ≤ n)
    (hPD : ∀ m : ℕ, 2 ≤ m → (hankelZ γ m).PosDef)
    (τ : ℕ → ℝ) (hτ : ∀ k < n - 1, γ k = (τ k : ℂ))
    (hreal : (γ (n - 1)).im = 0) : HR γ n := by
  set a : ℝ := (γ (n - 1)).re with ha
  have hγreal : γ (n - 1) = (a : ℂ) := Complex.ext (by simp [ha]) (by simpa using hreal)
  set τ' : ℕ → ℝ := fun k => if k < n - 1 then τ k else a with hτ'def
  have hτ' : ∀ k < n, γ k = (τ' k : ℂ) := by
    intro k hk
    by_cases hkn : k < n - 1
    · simp [hτ'def, hkn, hτ k hkn]
    · have : k = n - 1 := by omega
      subst this
      simp [hτ'def, hγreal]
  refine ⟨τ', hτ', ?_⟩
  have hdetpos : 0 < ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ' j - τ' i) ^ 2 := by
    have h1 := re_det_pos_of_posDef (hankelZ γ n) (hPD n hn)
    rw [det_hankelZ_reel γ τ' n hτ'] at h1
    rwa [Complex.ofReal_re] at h1
  intro i hi j hj hij hEq
  have hzero : ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ' j - τ' i) ^ 2 = 0 := by
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · refine Finset.prod_eq_zero (Finset.mem_univ (⟨i, hi⟩ : Fin n)) ?_
      refine Finset.prod_eq_zero
        (Finset.mem_Ioi.mpr (show (⟨i, hi⟩ : Fin n) < ⟨j, hj⟩ from hlt)) ?_
      change (τ' j - τ' i) ^ 2 = 0
      rw [hEq, sub_self]; norm_num
    · refine Finset.prod_eq_zero (Finset.mem_univ (⟨j, hj⟩ : Fin n)) ?_
      refine Finset.prod_eq_zero
        (Finset.mem_Ioi.mpr (show (⟨j, hj⟩ : Fin n) < ⟨i, hi⟩ from hgt)) ?_
      change (τ' i - τ' j) ^ 2 = 0
      rw [hEq, sub_self]; norm_num
  exact hdetpos.ne' hzero

lemma mineurs_positifs (γ : ℕ → ℂ) (τ : ℕ → ℝ) (D : ℕ)
    (hτ : ∀ k < D, γ k = (τ k : ℂ))
    (hinj : ∀ i < D, ∀ j < D, i ≠ j → τ i ≠ τ j)
    (n : ℕ) (hnD : n ≤ D) :
    (hankelZ γ n).det =
        ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ (j : ℕ) - τ (i : ℕ)) ^ 2 : ℝ) : ℂ) ∧
      0 < ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ (j : ℕ) - τ (i : ℕ)) ^ 2 := by
  have hτn : ∀ k < n, γ k = (τ k : ℂ) := fun k hk => hτ k (lt_of_lt_of_le hk hnD)
  refine ⟨det_hankelZ_reel γ τ n hτn, ?_⟩
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  have hij : (i : ℕ) ≠ j := by
    have := Finset.mem_Ioi.mp hj
    exact (Fin.lt_def.mp this).ne
  have hne := hinj i (lt_of_lt_of_le i.isLt hnD) j (lt_of_lt_of_le j.isLt hnD) hij
  have h0 : τ j - τ i ≠ 0 := sub_ne_zero.mpr hne.symm
  positivity

open InductionCanoniqueOp

lemma cholesky_hankel (γ : ℕ → ℂ) (n : ℕ)
    (hPD : (hankelZ γ n).PosDef)
    (hreal : ∀ i j, ((hankelZ γ n) i j).im = 0) :
    ∃ R : Matrix (Fin n) (Fin n) ℂ, EstUnitriSup R ∧
      ∃ s : Fin n → ℂ, (∀ k, 0 < (s k).re) ∧
        Rᵀ * hankelZ γ n * R = Matrix.diagonal s :=
  existe_LDL (hankelZ γ n) hPD hreal


lemma det_eq_prod_schur (γ : ℕ → ℂ) (n : ℕ)
    (R : Matrix (Fin n) (Fin n) ℂ) (hR : EstUnitriSup R) (s : Fin n → ℂ)
    (hcong : Rᵀ * hankelZ γ n * R = Matrix.diagonal s) :
    (hankelZ γ n).det = ∏ k, s k := by
  have h1 := congrArg Matrix.det hcong
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
      EstUnitriSup.det_eq_one hR,
      Matrix.det_diagonal] at h1
  simpa using h1

lemma hankelZ_im_zero (γ : ℕ → ℂ) (τ : ℕ → ℝ) (n : ℕ)
    (h : ∀ k < n, γ k = (τ k : ℂ)) (i j : Fin n) :
    ((hankelZ γ n) i j).im = 0 := by
  rw [hankelZ_eq_map_hankelR γ τ n h]
  simp [Matrix.map_apply]

lemma W_unitri {n : ℕ} (R P : Matrix (Fin n) (Fin n) ℂ)
    (hR : EstUnitriSup R) (hP : EstUnitriSup P) : EstUnitriSup (R * P) :=
  EstUnitriSup.mul hR hP

lemma diag_compose {n : ℕ} (T R P : Matrix (Fin n) (Fin n) ℂ) (τ : Fin n → ℂ)
    (hR : IsUnit R.det) (hP : IsUnit P.det)
    (h : P⁻¹ * (R⁻¹ * T * R) * P = Matrix.diagonal τ) :
    (R * P)⁻¹ * T * (R * P) = Matrix.diagonal τ := by
  have hRP : IsUnit (R * P).det := by
    rw [Matrix.det_mul]; exact hR.mul hP
  rw [Matrix.mul_inv_rev, ← h]
  simp only [Matrix.mul_assoc]

theorem synthese_definie_positivite_exhaustion
    (γ : ℕ → ℂ) (τ₁ τ₂ : ℝ) (hne : τ₁ ≠ τ₂)
    (hdeux : γ 0 = (τ₁ : ℂ) ∧ γ 1 = (τ₂ : ℂ))
    (D : ℕ) (hD : 2 ≤ D)
    (hPD : ∀ n : ℕ, 2 ≤ n → (hankelZ γ n).PosDef)
    (T : Matrix (Fin D) (Fin D) ℂ)
    (triang_diag : ∀ (R : Matrix (Fin D) (Fin D) ℂ) (τ : Fin D → ℂ),
      EstUnitriSup R →
      (∀ i j : Fin D, j < i → (R⁻¹ * T * R) i j = 0) →
      (∀ i, (R⁻¹ * T * R) i i = τ i) →
      (∀ i j, i ≠ j → τ i ≠ τ j) →
      ∃ P : Matrix (Fin D) (Fin D) ℂ, EstUnitriSup P ∧
        P⁻¹ * (R⁻¹ * T * R) * P = Matrix.diagonal τ)
    (hT : ∀ (R : Matrix (Fin D) (Fin D) ℂ) (τ : ℕ → ℝ),
      (∀ k < D, γ k = (τ k : ℂ)) →
      EstUnitriSup R →
      (∀ i j : Fin D, j < i → (R⁻¹ * T * R) i j = 0) ∧
        ∀ i, (R⁻¹ * T * R) i i = (τ i : ℂ)) :
    ∃ τ : ℕ → ℝ,
      (∀ k < D, γ k = (τ k : ℂ)) ∧
      (∀ i < D, ∀ j < D, i ≠ j → τ i ≠ τ j) ∧
      (∃ R : Matrix (Fin D) (Fin D) ℂ, EstUnitriSup R ∧
        ∃ s : Fin D → ℂ, (∀ k, 0 < (s k).re) ∧
          Rᵀ * hankelZ γ D * R = Matrix.diagonal s ∧
          (hankelZ γ D).det = ∏ k, s k) ∧
      (∀ n, 1 ≤ n → n ≤ D →
        (hankelZ γ n).det =
            ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ (j : ℕ) - τ (i : ℕ)) ^ 2 : ℝ) : ℂ) ∧
          0 < ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ (j : ℕ) - τ (i : ℕ)) ^ 2) ∧
      (∃ W : Matrix (Fin D) (Fin D) ℂ, EstUnitriSup W ∧
        W⁻¹ * T * W = Matrix.diagonal (fun i : Fin D => (τ i : ℂ))) := by
  have hHR : HR γ D := by
    have := (propagation_recurrence_forte_deux_zeros γ τ₁ τ₂ hne hdeux hPD).2.1
    exact this D hD
  obtain ⟨τ, hτ, hinj⟩ := hHR
  refine ⟨τ, hτ, hinj, ?_, ?_, ?_⟩
  · have hreal := hankelZ_im_zero γ τ D hτ
    obtain ⟨R, hR, s, hs, hcong⟩ := cholesky_hankel γ D (hPD D hD) hreal
    exact ⟨R, hR, s, hs, hcong, det_eq_prod_schur γ D R hR s hcong⟩
  · intro n _ hnD
    exact mineurs_positifs γ τ D hτ hinj n hnD
  · have hreal := hankelZ_im_zero γ τ D hτ
    obtain ⟨R, hR, s, hs, hcong⟩ := cholesky_hankel γ D (hPD D hD) hreal
    obtain ⟨htri, hdiag⟩ := hT R τ hτ hR
    obtain ⟨P, hP, hPdiag⟩ :=
      triang_diag R (fun i : Fin D => (τ i : ℂ)) hR htri
        (fun i => hdiag i)
        (fun i j hij h => hinj i i.isLt j j.isLt
          (fun h' => hij (Fin.ext h')) (by exact_mod_cast h))
    refine ⟨R * P, W_unitri R P hR hP, ?_⟩
    have hRdet : IsUnit R.det := by rw [EstUnitriSup.det_eq_one hR ]; exact isUnit_one
    have hPdet : IsUnit P.det := by rw [EstUnitriSup.det_eq_one hP]; exact isUnit_one
    exact diag_compose T R P _ hRdet hPdet hPdiag




end ExhaustionHankel
