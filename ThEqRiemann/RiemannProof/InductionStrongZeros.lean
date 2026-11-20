import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.SchurPassageMatrix
import ThEqRiemann.EqTheorem.Vandermonde

/-! -/
namespace InducStrongZero

open Set Complex Matrix
open RiemannDef


theorem init_rang_deux (τ₁ τ₂ : ℝ) (h : τ₁ ≠ τ₂) :
    let H : Matrix (Fin 2) (Fin 2) ℝ :=
      !![2, τ₁ + τ₂; τ₁ + τ₂, τ₁ ^ 2 + τ₂ ^ 2]
    H.det = (τ₂ - τ₁) ^ 2 ∧
    0 < (τ₂ - τ₁) ^ 2 ∧
    H.PosDef ∧
    ((τ₁ ^ 2 + τ₂ ^ 2) - (τ₁ + τ₂) ^ 2 / 2 = (τ₂ - τ₁) ^ 2 / 2) ∧
    (2 * ((τ₂ - τ₁) ^ 2 / 2) = H.det) := by
  intro H
  have hne : τ₂ - τ₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  have hpos : 0 < (τ₂ - τ₁) ^ 2 := by positivity
  have hdet : H.det = (τ₂ - τ₁) ^ 2 := by
    simp only [H, Matrix.det_fin_two_of]
    ring
  refine ⟨hdet, hpos, ?_, by ring, by rw [hdet]; ring⟩
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [H, Matrix.conjTranspose_apply]
  · intro x hx
    have hx0 : (⇑x) ≠ 0 := by
      intro h0
      apply hx
      ext i
      simpa using congrFun h0 i
    have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hx0
      ext i; fin_cases i <;> simp [hcon.1, hcon.2]
    have hq : star ⇑x ⬝ᵥ (H *ᵥ ⇑x) =
        2 * (x 0 + (τ₁ + τ₂) / 2 * x 1) ^ 2 + (τ₂ - τ₁) ^ 2 / 2 * (x 1) ^ 2 := by
      simp [H, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    have hpos' : 0 < 2 * (x 0 + (τ₁ + τ₂) / 2 * x 1) ^ 2
        + (τ₂ - τ₁) ^ 2 / 2 * (x 1) ^ 2 := by
      rcases hx' with h0 | h1
      · by_cases h1 : x 1 = 0
        · have : 0 < (x 0 + (τ₁ + τ₂) / 2 * x 1) ^ 2 := by
            rw [h1]
            simp only [Fin.isValue, mul_zero, add_zero]
            positivity
          nlinarith [sq_nonneg (x 1), hpos]
        · have : 0 < (x 1) ^ 2 := by positivity
          nlinarith [sq_nonneg (x 0 + (τ₁ + τ₂) / 2 * x 1), hpos]
      · have : 0 < (x 1) ^ 2 := by positivity
        nlinarith [sq_nonneg (x 0 + (τ₁ + τ₂) / 2 * x 1), hpos]
    have hin : ∀ i : Fin 2,
        (x.sum fun j xj ↦ star (x i) * H i j * xj)
          = ∑ j, star (x i) * H i j * x j := by
      intro i
      exact Finsupp.sum_fintype x (fun j xj ↦ star (x i) * H i j * xj)
        (fun j => by simp)
    have hconv :
        (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * H i j * xj)
          = star ⇑x ⬝ᵥ (H *ᵥ ⇑x) := by
      rw [Finsupp.sum_fintype x
        (fun i xi ↦ x.sum fun j xj ↦ star xi * H i j * xj)
        (fun i => by simp)]
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finsupp.sum_fintype x
        (fun j xj ↦ star (x i) * H i j * xj) (fun j => by simp)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp [mul_assoc]
    change 0 < (x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * H i j * xj)
    rw [hconv, hq]
    exact hpos'

theorem R2_unique (τ₁ τ₂ x : ℝ) :
    (2 * x + (τ₁ + τ₂) = 0) ↔ x = -(τ₁ + τ₂) / 2 := by
  constructor <;> intro h <;> linarith

theorem P2_bien_definie (τ₁ τ₂ : ℝ) (h : τ₁ ≠ τ₂) : τ₂ - τ₁ ≠ 0 :=
  sub_ne_zero.mpr (Ne.symm h)

theorem init_cas_symetrique (γ : ℝ) (hγ : 0 < γ) :
    (!![2, γ + -γ; γ + -γ, γ ^ 2 + (-γ) ^ 2] : Matrix (Fin 2) (Fin 2) ℝ)
        = !![2, 0; 0, 2 * γ ^ 2] ∧
    (-(γ + -γ) / 2 : ℝ) = 0 ∧
    ((γ ^ 2 + (-γ) ^ 2) - (γ + -γ) ^ 2 / 2 : ℝ) = 2 * γ ^ 2 ∧
    (-γ) ≠ γ := by
  refine ⟨?_, by ring, by ring, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp ; ring
  · intro h; linarith

theorem delta_pos {n : ℕ} (τ : Fin n → ℝ) (hτ : Function.Injective τ) :
    0 < ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2 := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  have hij : j ≠ i := (Finset.mem_Ioi.mp hj).ne'
  have : τ j - τ i ≠ 0 := sub_ne_zero.mpr (hτ.ne hij)
  positivity


open SchurPassage in
theorem sigma_nul_de_positivite
    (k : ℕ) (τ : Fin (k + 2) → ℝ) (hτ : Function.Injective τ) (τn σn : ℝ)
    (hpos_adjonction_simple :
      (Matrix.of fun (i j : Fin (k + 3)) =>
        (∑ j' : Fin (k + 2), (τ j' : ℂ) ^ ((i : ℕ) + j)) +
          ((τn : ℂ) - (σn : ℂ) * Complex.I) ^ ((i : ℕ) + j)).IsHermitian ∨
      (Matrix.of fun (i j : Fin (k + 4)) =>
        ∑ l : Fin (k + 2), τ l ^ ((i : ℕ) + j) +
          ((((τn : ℂ) - (σn : ℂ) * Complex.I) ^ ((i : ℕ) + j) +
            (starRingEnd ℂ ((τn : ℂ) - (σn : ℂ) * Complex.I)) ^ ((i : ℕ) + j) : ℂ)).re
        : Matrix (Fin (k + 4)) (Fin (k + 4)) ℝ).PosDef) :
    σn = 0 := by
  have hobs := obstruction_schur_partie_reelle k τ hτ τn σn
  simp only at hobs
  obtain ⟨⟨_, hherm⟩, _, h3⟩ := hobs
  by_contra hσ
  rcases hpos_adjonction_simple with h | h
  · exact hσ ((hherm).mp h)
  · exact (h3 hσ).2 h

theorem prod_carres_pos_iff {n : ℕ} (τ : Fin n → ℝ) (τn : ℝ) :
    0 < ∏ k : Fin n, (τn - τ k) ^ 2 ↔ ∀ k, τn ≠ τ k := by
  constructor
  · intro h k hk
    have : (∏ k : Fin n, (τn - τ k) ^ 2) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk]; simp)
    linarith
  · intro h
    apply Finset.prod_pos
    intro k _
    have : τn - τ k ≠ 0 := sub_ne_zero.mpr (h k)
    positivity

-----------------------------------------------------------------

lemma prod_Ioi_zero {k : ℕ} (g : Fin (k + 1) → ℝ) :
    ∏ j ∈ Finset.Ioi (0 : Fin (k + 1)), g j = ∏ j : Fin k, g j.succ := by
  have h : Finset.Ioi (0 : Fin (k + 1)) = Finset.univ.map (Fin.succEmb k) := by
    ext j
    simp only [Finset.mem_Ioi, Finset.mem_map, Finset.mem_univ, true_and,
      Fin.coe_succEmb]
    constructor
    · intro hj
      exact ⟨j.pred (Fin.pos_iff_ne_zero.mp hj), Fin.succ_pred _ _⟩
    · rintro ⟨i, rfl⟩
      exact Fin.succ_pos i
  rw [h, Finset.prod_map]
  rfl

lemma prod_Ioi_succ {k : ℕ} (i : Fin k) (g : Fin (k + 1) → ℝ) :
    ∏ j ∈ Finset.Ioi i.succ, g j = ∏ j ∈ Finset.Ioi i, g j.succ := by
  have h : Finset.Ioi i.succ = (Finset.Ioi i).map (Fin.succEmb k) := by
    ext j
    simp only [Finset.mem_Ioi, Finset.mem_map, Fin.coe_succEmb]
    constructor
    · intro hj
      have hj0 : j ≠ 0 := by
        intro h0
        rw [h0] at hj
        exact absurd hj (not_lt.mpr (Fin.zero_le _))
      refine ⟨j.pred hj0, ?_, Fin.succ_pred _ _⟩
      rw [← Fin.succ_lt_succ_iff, Fin.succ_pred]
      exact hj
    · rintro ⟨l, hl, rfl⟩
      exact Fin.succ_lt_succ_iff.mpr hl
  rw [h, Finset.prod_map]
  rfl

theorem quotient_dets {k : ℕ} (τ : Fin (k + 1) → ℝ) :
    (∏ i : Fin (k + 1), ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2) =
      (∏ i : Fin k, ∏ j ∈ Finset.Ioi i, (τ j.succ - τ i.succ) ^ 2) *
      ∏ j : Fin k, (τ j.succ - τ 0) ^ 2 := by
  rw [Fin.prod_univ_succ, mul_comm]
  congr 1
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    exact prod_Ioi_succ i (fun j => (τ j - τ i.succ) ^ 2)
  · exact prod_Ioi_zero (fun j => (τ j - τ 0) ^ 2)

-----------------------------------------------------------------

lemma momentZ_succ_un (γ : ℕ → ℂ) (n : ℕ) :
    momentZ γ (n + 1) 1 = momentZ γ n 1 + γ n := by
  unfold momentZ
  rw [Fin.sum_univ_castSucc]
  simp

lemma im_dernier_nul (γ : ℕ → ℂ) (τ : ℕ → ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hτ : ∀ k < n - 1, γ k = (τ k : ℂ))
    (him : (momentZ γ n 1).im = 0) :
    (γ (n - 1)).im = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [momentZ_succ_un] at him
  have hm : (momentZ γ m 1).im = 0 := by
    unfold momentZ
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [pow_one, hτ k (by simp)]
    simp
  simp only [Nat.add_sub_cancel]
  rw [Complex.add_im, hm, zero_add] at him
  exact him

lemma im_moment_un_nul (γ : ℕ → ℂ) (n : ℕ) (hn : 2 ≤ n)
    (hherm : (hankelZ γ n).IsHermitian) :
    (momentZ γ n 1).im = 0 := by
  have h := hherm.apply ⟨0, by omega⟩ ⟨1, by omega⟩
  simp only [hankelZ, Matrix.of_apply, Complex.star_def] at h
  have h' : (starRingEnd ℂ) (momentZ γ n 1) = momentZ γ n 1 := by
    simpa using h
  have := congrArg Complex.im h'
  simp at this
  linarith

open VandermondeThEq in
lemma det_hankelZ_reel (γ : ℕ → ℂ) (τ : ℕ → ℝ) (n : ℕ)
    (h : ∀ k < n, γ k = (τ k : ℂ)) :
    (hankelZ γ n).det =
      ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2 : ℝ) : ℂ) := by
  rw [hankelZ_eq_map_hankelR γ τ n h]
  have hR : (hankelR τ n).det =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2 :=
    det_hankel_vandermonde (fun k : Fin n => τ k)
  rw [← hR]
  exact (RingHom.map_det Complex.ofRealHom (hankelR τ n)).symm

open ComplexOrder in
lemma re_det_pos_of_posDef {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    0 < H.det.re := by
  have h : (0 : ℂ) < H.det := hH.det_pos
  rw [Complex.lt_def] at h
  simpa using h.1

open ComplexOrder in
theorem propagation_recurrence_forte_deux_zeros
    (γ : ℕ → ℂ) (τ₁ τ₂ : ℝ) (hne : τ₁ ≠ τ₂)
    (hdeux : γ 0 = (τ₁ : ℂ) ∧ γ 1 = (τ₂ : ℂ))
    (hPD : ∀ n : ℕ, 2 ≤ n → (hankelZ γ n).PosDef) :
    ((!![2, τ₁ + τ₂; τ₁ + τ₂, τ₁ ^ 2 + τ₂ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).det
        = (τ₂ - τ₁) ^ 2 ∧
      0 < (τ₂ - τ₁) ^ 2 ∧
      (!![2, τ₁ + τ₂; τ₁ + τ₂, τ₁ ^ 2 + τ₂ ^ 2] : Matrix (Fin 2) (Fin 2) ℝ).PosDef ∧
      (∀ x : ℝ, 2 * x + (τ₁ + τ₂) = 0 ↔ x = -(τ₁ + τ₂) / 2)) ∧
    (∀ n, 2 ≤ n → HR γ n) ∧
    (∀ n, 2 ≤ n → ∃ τ : ℕ → ℝ, (∀ k < n + 1, γ k = (τ k : ℂ)) ∧
        τ n = (momentZ γ (n + 1) 1).re - ∑ k : Fin n, τ k) := by
  have h2 : ∀ n, 2 ≤ n → HR γ n := by
    intro n hn
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases h2n : n = 2
      · subst h2n
        refine ⟨fun k => if k = 0 then τ₁ else τ₂, ?_, ?_⟩
        · intro k hk
          interval_cases k
          · simp [hdeux.1]
          · simp [hdeux.2]
        · intro i hi j hj hij
          interval_cases i <;> interval_cases j <;> first
            | exact absurd rfl hij
            | simpa using hne
            | simpa using hne.symm
      · have hn3 : 3 ≤ n := by omega
        obtain ⟨τ, hτ, hinj⟩ := ih (n - 1) (by omega) (by omega)
        have hherm : (hankelZ γ n).IsHermitian := (hPD n hn).isHermitian
        have himM : (momentZ γ n 1).im = 0 := im_moment_un_nul γ n hn hherm
        have hreal : (γ (n - 1)).im = 0 := im_dernier_nul γ τ n (by omega) hτ himM
        have hγreal : γ (n - 1) = ((γ (n - 1)).re : ℂ) :=
          (Complex.ext (by simp) (by simpa using hreal))
        set a : ℝ := (γ (n - 1)).re with ha
        let τ' : ℕ → ℝ := fun k => if k < n - 1 then τ k else a
        have hτ' : ∀ k < n, γ k = (τ' k : ℂ) := by
          intro k hk
          by_cases hkn : k < n - 1
          · simp only [τ', ite_eq_left hkn]; exact hτ k hkn
          · have hk' : k = n - 1 := by omega
            subst hk'
            simp only [τ', ite_eq_right hkn]
            exact hγreal
        have hdetpos : 0 < ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ' j - τ' i) ^ 2 := by
          have h1 := re_det_pos_of_posDef (hankelZ γ n) (hPD n hn)
          rw [det_hankelZ_reel γ τ' n hτ'] at h1
          rwa [Complex.ofReal_re] at h1
        refine ⟨τ', hτ', ?_⟩
        intro i hi j hj hij hEq
        have hprod : ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ' j - τ' i) ^ 2 = 0 := by
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · exact Finset.prod_eq_zero (Finset.mem_univ ⟨i, hi⟩)
              (Finset.prod_eq_zero (Finset.mem_Ioi.mpr
                (by simpa [Fin.lt_def] using hlt) :
                  (⟨j, hj⟩ : Fin n) ∈ Finset.Ioi ⟨i, hi⟩)
                (by simp [hEq]))
          · exact Finset.prod_eq_zero (Finset.mem_univ ⟨j, hj⟩)
              (Finset.prod_eq_zero (Finset.mem_Ioi.mpr
                (by simpa [Fin.lt_def] using hgt) :
                  (⟨i, hi⟩ : Fin n) ∈ Finset.Ioi ⟨j, hj⟩)
                (by simp [hEq]))
        exact absurd hprod hdetpos.ne'
  refine ⟨?_, h2, ?_⟩
  · obtain ⟨hdet, hpos, hPDinit, _, _⟩ := init_rang_deux τ₁ τ₂ hne
    exact ⟨hdet, hpos, hPDinit, fun x => R2_unique τ₁ τ₂ x⟩
  · intro n hn
    obtain ⟨τ, hτ, -⟩ := h2 (n + 1) (by omega)
    refine ⟨τ, fun k hk => hτ k hk, ?_⟩
    have hsum : (momentZ γ (n + 1) 1).re = ∑ k : Fin (n + 1), τ (k : ℕ) := by
      unfold momentZ
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [pow_one, hτ (k : ℕ) (by omega)]
      simp
    rw [hsum, Fin.sum_univ_castSucc]
    simp


end InducStrongZero
