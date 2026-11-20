import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.InductionRiemannZero
import ThEqRiemann.EqTheorem.Vandermonde
import ThEqRiemann.RiemannProof.BrainrotLemma
import ThEqRiemann.RiemannProof.SylvesterCriterium

/-! -/
namespace hPosRiemann

open Set Complex Matrix
open RiemannDef InducRiemannZero VandermondeThEq

lemma image_Icc_eq_of_injOn (n : ℕ) (σ : ℕ → ℕ)
    (hσ_mem : ∀ j ∈ Finset.Icc 1 n, σ j ∈ Finset.Icc 1 n)
    (hσ_inj : Set.InjOn σ (Finset.Icc 1 n)) :
    (Finset.Icc 1 n).image σ = Finset.Icc 1 n := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact hσ_mem j hj
  · rw [Finset.card_image_of_injOn hσ_inj]

lemma det_Hn_eq_prod_vandermonde (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ) :
    (Hn γ m n).det =
      (∏ j : Fin n, (m ((j : ℕ) + 1) : ℂ)) *
        (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
        (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) ^ 2 := by
  have hV : (Vn γ n).det =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1)) := by
    have hVn : Vn γ n = Matrix.vandermonde (fun j : Fin n => γ ((j : ℕ) + 1)) := by
      unfold Vn
      rfl
    rw [hVn, Matrix.det_vandermonde]
  rw [det_Hn_eq γ m n, hV]

lemma det_Hn_pos_of_reels_distincts (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hreal : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0)
    (hinj : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → γ i = γ j → i = j)
    (hm : ∀ j, 1 ≤ j → j ≤ n → 0 < m j) :
    0 < (Hn γ m n).det.re ∧ (Hn γ m n).det.im = 0 := by
  set τ : Fin n → ℝ := fun j => (γ ((j : ℕ) + 1)).re with hτ
  have hγτ : ∀ j : Fin n, γ ((j : ℕ) + 1) = (τ j : ℂ) := by
    intro j
    apply Complex.ext
    · simp [hτ]
    · simp [hreal ((j : ℕ) + 1) (by omega) (by omega)]
  have hτinj : Function.Injective τ := by
    intro i j hij
    have h1 : γ ((i : ℕ) + 1) = γ ((j : ℕ) + 1) := by
      rw [hγτ i, hγτ j, hij]
    have := hinj _ _ (by omega) (by omega) (by omega) (by omega) h1
    exact Fin.ext (by omega)
  have hV : (Vn γ n).det ^ 2 =
      ((∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2 : ℝ) : ℂ) := by
    have h := vandermonde_carre_eq_delta n τ
    have hVn : Vn γ n = Matrix.vandermonde (fun k => (τ k : ℂ)) := by
      ext i j
      simp [Vn, Matrix.vandermonde, hγτ i]
    rw [hVn]
    exact h
  have hprodpos : 0 < ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (τ j - τ i) ^ 2 := by
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : j ≠ i := (Finset.mem_Ioi.mp hj).ne'
    have : τ j - τ i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hτinj h))
    positivity
  have hmpos : 0 < ∏ j : Fin n, (m ((j : ℕ) + 1) : ℝ) := by
    apply Finset.prod_pos
    intro j _
    exact_mod_cast hm ((j : ℕ) + 1) (by omega) (by omega)
  rw [det_Hn_eq γ m n, hV]
  have hcast : (∏ j : Fin n, (m ((j : ℕ) + 1) : ℂ)) =
      ((∏ j : Fin n, (m ((j : ℕ) + 1) : ℝ) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, ← Complex.ofReal_mul]
  constructor
  · rw [Complex.ofReal_re]
    exact mul_pos hmpos hprodpos
  · exact Complex.ofReal_im _


lemma conj_sub_sq_neg (z : ℂ) (hz : z.im ≠ 0) :
    ((starRingEnd ℂ z - z) ^ 2).re < 0 ∧ ((starRingEnd ℂ z - z) ^ 2).im = 0 := by
  have h1 : (starRingEnd ℂ z - z) = ((-2 * z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext
    · simp
    · simp
      ring
  have h2 : (starRingEnd ℂ z - z) ^ 2 = ((-4 * z.im ^ 2 : ℝ) : ℂ) := by
    rw [h1, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [h2]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  have : 0 < z.im ^ 2 := by positivity
  linarith

lemma cross_real_sq_pos (z : ℂ) (hz : z.im ≠ 0) (x : ℝ) :
    ((((z - (x : ℂ)) * (starRingEnd ℂ z - (x : ℂ))) ^ 2).re > 0) ∧
    ((((z - (x : ℂ)) * (starRingEnd ℂ z - (x : ℂ))) ^ 2).im = 0) := by
  have h1 : (z - (x : ℂ)) * (starRingEnd ℂ z - (x : ℂ)) =
      (((z.re - x) ^ 2 + z.im ^ 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [pow_two] ; ring
  have h2 : (((z - (x : ℂ)) * (starRingEnd ℂ z - (x : ℂ))) ^ 2) =
      ((((z.re - x) ^ 2 + z.im ^ 2) ^ 2 : ℝ) : ℂ) := by
    rw [h1]; push_cast; ring
  rw [h2]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  have h3 : 0 < z.im ^ 2 := by positivity
  have h4 : 0 < (z.re - x) ^ 2 + z.im ^ 2 := by positivity
  positivity


lemma det_Hn_split (γ : ℕ → ℂ) (m : ℕ → ℕ) (p : ℕ) :
    (Hn γ m (p + 2)).det =
      (∏ j : Fin (p + 2), (m ((j : ℕ) + 1) : ℂ)) *
        ((∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) *
         (∏ j : Fin p, (γ (p + 1) - γ ((j : ℕ) + 1)) * (γ (p + 2) - γ ((j : ℕ) + 1))) *
         (γ (p + 2) - γ (p + 1))) ^ 2 := by
  rw [det_Hn_eq_prod_vandermonde γ m (p + 2), vandermonde_split γ p]

lemma eq_ofReal_of_im_eq_zero (z : ℂ) (h : z.im = 0) : z = ((z.re : ℝ) : ℂ) :=
  Complex.ext (by simp) (by simp [h])

lemma mul_pos_real (a b : ℂ) (ha : 0 < a.re ∧ a.im = 0) (hb : 0 < b.re ∧ b.im = 0) :
    0 < (a * b).re ∧ (a * b).im = 0 := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re, ha2, hb2]
    nlinarith
  · rw [Complex.mul_im, ha2, hb2]
    ring

lemma mul_pos_neg_real (a b : ℂ) (ha : 0 < a.re ∧ a.im = 0) (hb : b.re < 0 ∧ b.im = 0) :
    (a * b).re < 0 ∧ (a * b).im = 0 := by
  obtain ⟨ha1, ha2⟩ := ha
  obtain ⟨hb1, hb2⟩ := hb
  refine ⟨?_, ?_⟩
  · rw [Complex.mul_re, ha2, hb2]
    nlinarith [mul_pos ha1 (neg_pos.mpr hb1)]
  · rw [Complex.mul_im, ha2, hb2]
    ring

lemma prod_pos_real {ι : Type*} [Fintype ι] (f : ι → ℂ)
    (hf : ∀ i, 0 < (f i).re ∧ (f i).im = 0) :
    0 < (∏ i, f i).re ∧ (∏ i, f i).im = 0 := by
  have h : ∏ i, f i = (((∏ i, (f i).re) : ℝ) : ℂ) := by
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    exact eq_ofReal_of_im_eq_zero (f i) (hf i).2
  rw [h]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  exact Finset.prod_pos (fun i _ => (hf i).1)

lemma prod_mult_pos (m : ℕ → ℕ) (n : ℕ) (hmpos : ∀ j, 1 ≤ j → j ≤ n → 0 < m j) :
    0 < (∏ j : Fin n, (m ((j : ℕ) + 1) : ℂ)).re ∧
    (∏ j : Fin n, (m ((j : ℕ) + 1) : ℂ)).im = 0 := by
  apply prod_pos_real
  intro j
  have hj : 0 < m ((j : ℕ) + 1) := hmpos ((j : ℕ) + 1) (by omega) (by have := j.isLt; omega)
  refine ⟨?_, ?_⟩
  · rw [Complex.natCast_re]
    exact_mod_cast hj
  · rw [Complex.natCast_im]

lemma cross_prod_sq_pos (γ : ℕ → ℂ) (p : ℕ)
    (hreal : ∀ j, 1 ≤ j → j < p + 1 → (γ j).im = 0)
    (hnonreal : (γ (p + 1)).im ≠ 0)
    (hconj : γ (p + 2) = starRingEnd ℂ (γ (p + 1))) :
    0 < ((∏ j : Fin p, (γ (p + 1) - γ ((j : ℕ) + 1)) *
    (γ (p + 2) - γ ((j : ℕ) + 1))) ^ 2).re ∧
    ((∏ j : Fin p, (γ (p + 1) - γ ((j : ℕ) + 1)) *
    (γ (p + 2) - γ ((j : ℕ) + 1))) ^ 2).im = 0 := by
  rw [← Finset.prod_pow]
  apply prod_pos_real
  intro j
  have hj : (γ ((j : ℕ) + 1)).im = 0 :=
    hreal ((j : ℕ) + 1) (by omega) (by have := j.isLt; omega)
  have hγj : γ ((j : ℕ) + 1) = (((γ ((j : ℕ) + 1)).re : ℝ) : ℂ) :=
    eq_ofReal_of_im_eq_zero _ hj
  rw [hconj, hγj]
  exact cross_real_sq_pos (γ (p + 1)) hnonreal (γ ((j : ℕ) + 1)).re

lemma vandermonde_sq_pos (γ : ℕ → ℂ) (m : ℕ → ℕ) (p : ℕ)
    (hmpos : ∀ j, 1 ≤ j → j ≤ p → 0 < m j)
    (hΔ : 0 < ((Hn γ m p).det).re ∧ ((Hn γ m p).det).im = 0) :
    0 < ((∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) ^ 2).re ∧
    ((∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) ^ 2).im = 0 := by
  set V : ℂ := ∏ i : Fin p, ∏ j ∈ Finset.Ioi i, (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1)) with hVdef
  set M : ℂ := ∏ j : Fin p, (m ((j : ℕ) + 1) : ℂ) with hMdef
  have hdet : (Hn γ m p).det = M * V ^ 2 := det_Hn_eq_prod_vandermonde γ m p
  obtain ⟨hM1, hM2⟩ := prod_mult_pos m p hmpos
  obtain ⟨hD1, hD2⟩ := hΔ
  rw [hdet] at hD1 hD2
  rw [Complex.mul_re, hM2] at hD1
  rw [Complex.mul_im, hM2] at hD2
  refine ⟨?_, ?_⟩
  · have h : 0 < M.re * (V ^ 2).re := by linarith
    exact pos_of_mul_pos_right h hM1.le
  · have h : M.re * (V ^ 2).im = 0 := by linarith
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 hM1.ne'
    · exact h0

lemma delta_N0_neg (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ) (h3 : 3 ≤ n₀)
    (hreal : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0)
    (hnonreal : (γ n₀).im ≠ 0)
    (hconj : γ (n₀ + 1) = starRingEnd ℂ (γ n₀))
    (hm : m (n₀ + 1) = m n₀)
    (hmpos : ∀ j, 1 ≤ j → j ≤ n₀ + 1 → 0 < m j)
    (hΔ : 0 < ((Hn γ m (n₀ - 1)).det).re ∧ ((Hn γ m (n₀ - 1)).det).im = 0) :
    ((Hn γ m (n₀ + 1)).det).re < 0 ∧ ((Hn γ m (n₀ + 1)).det).im = 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, n₀ = p + 1 := ⟨n₀ - 1, by omega⟩
  have e1 : p + 1 - 1 = p := by omega
  rw [e1] at hΔ
  have e : p + 1 + 1 = p + 2 := rfl
  rw [e, det_Hn_split γ m p]
  have hD2 : (((γ (p + 2) - γ (p + 1)) ^ 2).re < 0) ∧ ((γ (p + 2) - γ (p + 1)) ^ 2).im = 0 := by
    have hc : γ (p + 2) = starRingEnd ℂ (γ (p + 1)) := hconj
    rw [hc]
    exact conj_sub_sq_neg (γ (p + 1)) hnonreal
  have hC2 := cross_prod_sq_pos γ p hreal hnonreal hconj
  have hV2 := vandermonde_sq_pos γ m p
    (fun j hj1 hj2 => hmpos j hj1 (by omega)) hΔ
  have hM := prod_mult_pos m (p + 2)
    (fun j hj1 hj2 => hmpos j hj1 (by omega))
  rw [mul_pow, mul_pow]
  have hVC := mul_pos_real _ _ hV2 hC2
  have hVCD := mul_pos_neg_real _ _ hVC hD2
  exact mul_pos_neg_real _ _ hM hVCD

lemma not_hankel_pos_of_det_neg (γ : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ) (hN : 1 ≤ N)
    (hDelta : Delta γ m N N = (Hn γ m N).det)
    (hneg : ((Hn γ m N).det).re < 0) :
    ¬ (∀ r, 1 ≤ r → r ≤ N → 0 < (Delta γ m N r).re) := by
  intro hall
  have h := hall N hN le_rfl
  rw [hDelta] at h
  linarith

theorem hankel_synthese_intermed1 :
    (∀ (n : ℕ) (σ : ℕ → ℕ),
      (∀ j ∈ Finset.Icc 1 n, σ j ∈ Finset.Icc 1 n) →
      Set.InjOn σ (Finset.Icc 1 n) →
      (Finset.Icc 1 n).image σ = Finset.Icc 1 n) ∧
    (∀ (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ), (Hn γ m n).det =
        (∏ j : Fin n, (m ((j : ℕ) + 1) : ℂ)) *
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
            (γ ((j : ℕ) + 1) - γ ((i : ℕ) + 1))) ^ 2) ∧
    (∀ (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ), 3 ≤ n₀ →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) →
      (γ n₀).im ≠ 0 →
      γ (n₀ + 1) = starRingEnd ℂ (γ n₀) →
      m (n₀ + 1) = m n₀ →
      (∀ j, 1 ≤ j → j ≤ n₀ + 1 → 0 < m j) →
      0 < ((Hn γ m (n₀ - 1)).det).re ∧ ((Hn γ m (n₀ - 1)).det).im = 0 →
      ((Hn γ m (n₀ + 1)).det).re < 0 ∧ ((Hn γ m (n₀ + 1)).det).im = 0) :=
  ⟨fun n σ hσ_mem hσ_inj => image_Icc_eq_of_injOn n σ hσ_mem hσ_inj,
   fun γ m n => det_Hn_eq_prod_vandermonde γ m n,
   fun γ m n₀ h3 hreal hnonreal hconj hm hmpos hΔ =>
     delta_N0_neg γ m n₀ h3 hreal hnonreal hconj hm hmpos hΔ⟩

lemma exists_first_nonreal (γ : ℕ → ℂ)
    (h1 : (γ 1).im = 0) (h2 : (γ 2).im = 0)
    (hex : ∃ k, 1 ≤ k ∧ (γ k).im ≠ 0) :
    ∃ n₀, 3 ≤ n₀ ∧ (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) ∧ (γ n₀).im ≠ 0 := by
  classical
  have hP : ∃ k, 1 ≤ k ∧ (γ k).im ≠ 0 := hex
  let P : ℕ → Prop := fun k => 1 ≤ k ∧ (γ k).im ≠ 0
  have hPex : ∃ k, P k := hP
  refine ⟨Nat.find hPex, ?_, ?_, ?_⟩
  · have hspec := Nat.find_spec hPex
    by_contra hlt
    push Not at hlt
    have hk : Nat.find hPex = 1 ∨ Nat.find hPex = 2 := by
      have := hspec.1
      omega
    rcases hk with hk | hk
    · rw [hk] at hspec; exact hspec.2 h1
    · rw [hk] at hspec; exact hspec.2 h2
  · intro j hj1 hjlt
    have := Nat.find_min hPex hjlt
    simp only [P, not_and, not_not] at this
    exact this hj1
  · exact (Nat.find_spec hPex).2

lemma det_pos_before_break (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ)
    (hreal : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0)
    (hinj : ∀ i j, 1 ≤ i → 1 ≤ j → γ i = γ j → i = j)
    (hmpos : ∀ j, 1 ≤ j → 0 < m j) :
    0 < ((Hn γ m (n₀ - 1)).det).re ∧ ((Hn γ m (n₀ - 1)).det).im = 0 := by
  apply det_Hn_pos_of_reels_distincts
  · intro j hj1 hj2
    exact hreal j hj1 (by omega)
  · intro i j hi1 _ hj1 _ h
    exact hinj i j hi1 hj1 h
  · intro j hj1 _
    exact hmpos j hj1

lemma Delta_self (γ : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ) :
    Delta γ m N N = (Hn γ m N).det := by
  unfold Delta Hn
  rfl

lemma not_HankelPositive_of_det_neg (γ : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ) (hN : 2 ≤ N)
    (hneg : ((Hn γ m N).det).re < 0) :
    ¬ HankelPositive γ m := by
  intro hpos
  obtain ⟨_, hmin⟩ := hpos N hN
  have h := (hmin N (by omega) le_rfl).1
  rw [Delta_self] at h
  linarith

lemma not_HankelPositive_of_det_neg' (γ : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ) (hN : 2 ≤ N)
    (hneg : ((Hn γ m N).det).re < 0) :
    ¬ HankelPositive γ m := by
  intro hpos
  obtain ⟨_, hmin⟩ := hpos N hN
  have h := (hmin N (by omega) le_rfl).1
  rw [Delta_self] at h
  linarith

lemma prod_fin_eq_prod_Icc' (f : ℕ → ℂ) (M : ℕ) :
    ∏ j : Fin M, f ((j : ℕ) + 1) = ∏ j ∈ Finset.Icc 1 M, f j := by
  rw [Fin.prod_univ_eq_prod_range (fun i => f (i + 1)) M]
  rw [Finset.range_eq_Ico]
  rw [Finset.prod_Ico_add' f 0 M 1]
  rfl

lemma conj_prod_eq_of_stable (γ : ℕ → ℂ) (m : ℕ → ℕ) (M : ℕ) (x : ℂ)
    (hx : x.im = 0) (hstab : ConjStable' γ m M) :
    (starRingEnd ℂ) (∏ j ∈ Finset.Icc 1 M, (x - γ j)) =
      ∏ j ∈ Finset.Icc 1 M, (x - γ j) := by
  obtain ⟨σ, hσ_mem, hσ_inj, hγ, _⟩ := hstab
  have hxc : (starRingEnd ℂ) x = x := Complex.conj_eq_iff_im.mpr hx
  have himg : (Finset.Icc 1 M).image σ = Finset.Icc 1 M :=
    image_Icc_eq_of_injOn M σ hσ_mem hσ_inj
  have h1 : (starRingEnd ℂ) (∏ j ∈ Finset.Icc 1 M, (x - γ j)) =
      ∏ j ∈ Finset.Icc 1 M, (x - γ (σ j)) := by
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro j hj
    rw [map_sub, hxc, hγ j hj]
  rw [h1]
  calc ∏ j ∈ Finset.Icc 1 M, (x - γ (σ j))
      = ∏ k ∈ (Finset.Icc 1 M).image σ, (x - γ k) := by
        rw [Finset.prod_image hσ_inj]
    _ = ∏ k ∈ Finset.Icc 1 M, (x - γ k) := by rw [himg]

lemma transition_factor_sq_pos (γ : ℕ → ℂ) (m : ℕ → ℕ) (M : ℕ) (x : ℂ)
    (hx : x.im = 0)
    (hstab : ConjStable' γ m M)
    (hdist : ∀ j, 1 ≤ j → j ≤ M → γ j ≠ x) :
    0 < ((∏ j : Fin M, (x - γ ((j : ℕ) + 1))) ^ 2).re ∧
    ((∏ j : Fin M, (x - γ ((j : ℕ) + 1))) ^ 2).im = 0 := by
  rw [prod_fin_eq_prod_Icc' (fun j => x - γ j) M]
  set P : ℂ := ∏ j ∈ Finset.Icc 1 M, (x - γ j) with hP
  have hconj : (starRingEnd ℂ) P = P := conj_prod_eq_of_stable γ m M x hx hstab
  have hPim : P.im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hPne : P ≠ 0 := by
    rw [hP, Finset.prod_ne_zero_iff]
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    exact sub_ne_zero.mpr (fun h => hdist j hj'.1 hj'.2 h.symm)
  have hPeq : P = ((P.re : ℝ) : ℂ) := eq_ofReal_of_im_eq_zero P hPim
  have hre : P.re ≠ 0 := by
    intro h0
    apply hPne
    rw [hPeq, h0]
    simp
  have hsq : P ^ 2 = (((P.re) ^ 2 : ℝ) : ℂ) := by
    rw [hPeq]
    push_cast
    ring_nf
    simp
  rw [hsq]
  refine ⟨?_, Complex.ofReal_im _⟩
  rw [Complex.ofReal_re]
  positivity

lemma prod_m_succ (m : ℕ → ℕ) (p : ℕ) :
    (∏ j : Fin (p + 1), (m ((j : ℕ) + 1) : ℂ)) =
      (∏ j : Fin p, (m ((j : ℕ) + 1) : ℂ)) * (m (p + 1) : ℂ) := by
  rw [Fin.prod_univ_castSucc]
  simp

lemma delta_step_neg (γ : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ) (hN : 4 ≤ N)
    (hstab : ConjStable' γ m (N - 1))
    (hreal : (γ N).im = 0)
    (hdist : ∀ j, 1 ≤ j → j < N → γ j ≠ γ N)
    (hmpos : ∀ j, 1 ≤ j → j ≤ N → 0 < m j)
    (hprev : ((Hn γ m (N - 1)).det).re < 0 ∧ ((Hn γ m (N - 1)).det).im = 0) :
    ((Hn γ m N).det).re < 0 ∧ ((Hn γ m N).det).im = 0 := by
  obtain ⟨p, rfl⟩ : ∃ p, N = p + 1 := ⟨N - 1, by omega⟩
  have e1 : p + 1 - 1 = p := by omega
  rw [e1] at hstab hprev
  have htrans : (Hn γ m (p + 1)).det =
      (m (p + 1) : ℂ) * (∏ j : Fin p, (γ (p + 1) - γ ((j : ℕ) + 1))) ^ 2 *
        (Hn γ m p).det := by
    have h1 := det_Hn_eq_prod_vandermonde γ m (p + 1)
    have h2 := det_Hn_eq_prod_vandermonde γ m p
    rw [h1, h2, prod_m_succ m p, vandermonde_succ γ p]
    ring
  have hF := transition_factor_sq_pos γ m p (γ (p + 1)) hreal hstab
    (fun j hj1 hj2 => hdist j hj1 (by omega))
  have hm1 : (0 : ℝ) < m (p + 1) := by exact_mod_cast hmpos (p + 1) (by omega) le_rfl
  have hmC : ((m (p + 1) : ℂ).re = (m (p + 1) : ℝ)) ∧ (m (p + 1) : ℂ).im = 0 :=
    ⟨by simp, by simp⟩
  rw [htrans]
  have hmF := mul_pos_real _ _ ⟨by rw [hmC.1]; exact hm1, hmC.2⟩ hF
  exact mul_pos_neg_real _ _ hmF hprev

lemma delta_neg_propagation (γ : ℕ → ℂ) (m : ℕ → ℕ) (N₀ : ℕ) (hN₀ : 4 ≤ N₀)
    (hbase : ((Hn γ m N₀).det).re < 0 ∧ ((Hn γ m N₀).det).im = 0)
    (hstab : ∀ N, N₀ < N → ConjStable' γ m (N - 1))
    (hreal : ∀ N, N₀ < N → (γ N).im = 0)
    (hdist : ∀ N, N₀ < N → ∀ j, 1 ≤ j → j < N → γ j ≠ γ N)
    (hmpos : ∀ j, 1 ≤ j → 0 < m j) :
    ∀ N, N₀ ≤ N → ((Hn γ m N).det).re < 0 ∧ ((Hn γ m N).det).im = 0 := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact hbase
  | succ N hN ih =>
    have hN4 : 4 ≤ N + 1 := by omega
    have hlt : N₀ < N + 1 := by omega
    have hprev : ((Hn γ m (N + 1 - 1)).det).re < 0 ∧
        ((Hn γ m (N + 1 - 1)).det).im = 0 := by
      simpa using ih
    exact delta_step_neg γ m (N + 1) hN4
      (hstab (N + 1) hlt) (hreal (N + 1) hlt) (hdist (N + 1) hlt)
      (fun j hj1 _ => hmpos j hj1) hprev

theorem hankel_positive_implies_all_real (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hconj : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 → γ (n₀ + 1) = starRingEnd ℂ (γ n₀))
    (hmult : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 → m (n₀ + 1) = m n₀) :
    HankelPositive γ m → ∀ k, 1 ≤ k → (γ k).im = 0 := by
  intro hpos
  by_contra hcon
  push Not at hcon
  obtain ⟨n₁, hn₁1, hn₁2⟩ := hcon
  obtain ⟨n₀, h3, hreal, hnonreal⟩ :=
    exists_first_nonreal γ hEnum.real_one hEnum.real_two ⟨n₁, hn₁1, hn₁2⟩
  have hmpos : ∀ j, 1 ≤ j → 0 < m j := fun j hj => hEnum.mult_pos j hj
  have hΔ := det_pos_before_break γ m n₀ hreal hEnum.injective hmpos
  have hneg := delta_N0_neg γ m n₀ h3 hreal hnonreal
    (hconj n₀ h3 hnonreal) (hmult n₀ h3 hnonreal)
    (fun j hj1 _ => hmpos j hj1) hΔ
  exact not_HankelPositive_of_det_neg γ m (n₀ + 1) (by omega) hneg.1 hpos

theorem all_real_of_hankelPositive (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hcompat : ConjCompatible γ m)
    (hpos : HankelPositive γ m) :
    ∀ k, 1 ≤ k → (γ k).im = 0 :=
  hankel_positive_implies_all_real γ m
    hEnum hcompat.conj_next hcompat.mult_next hpos

lemma newton_im_zero_of_real (γ : ℕ → ℂ) (m : ℕ → ℕ) (n k : ℕ)
    (hreal : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0) :
    (newton γ m n k).im = 0 := by
  unfold newton
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Finset.mem_Icc] at hj
  have hj0 : (γ j).im = 0 := hreal j hj.1 hj.2
  have hγ : γ j = ((γ j).re : ℂ) := (Complex.conj_eq_iff_re.mp
    (Complex.conj_eq_iff_im.mpr hj0)).symm
  rw [hγ, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul]
  exact Complex.ofReal_im _

lemma sum_fin_eq_sum_Icc' (f : ℕ → ℂ) (M : ℕ) :
    ∑ j : Fin M, f ((j : ℕ) + 1) = ∑ j ∈ Finset.Icc 1 M, f j := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) M]
  rw [Finset.range_eq_Ico]
  rw [Finset.sum_Ico_add' f 0 M 1]
  rfl


lemma newton_gram_factor (γ : ℕ → ℂ) (m : ℕ → ℕ) (n r : ℕ) :
    (Matrix.of fun (p q : Fin r) => newton γ m n (p + q)) =
      (Matrix.of fun (p : Fin r) (j : Fin n) => γ ((j : ℕ) + 1) ^ (p : ℕ)) *
      Matrix.diagonal (fun j : Fin n => (m ((j : ℕ) + 1) : ℂ)) *
      (Matrix.of fun (j : Fin n) (q : Fin r) => γ ((j : ℕ) + 1) ^ (q : ℕ)) := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.of_apply, newton]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq',
  Finset.mem_univ, ite_true]
  rw [← sum_fin_eq_sum_Icc' (fun j => (m j : ℂ) * γ j ^ ((p : ℕ) + (q : ℕ)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add]
  ring

lemma delta_pos_of_real_distinct_self (γ : ℕ → ℂ) (m : ℕ → ℕ) (n : ℕ)
    (hreal : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0)
    (hdist : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → γ i = γ j → i = j)
    (hmpos : ∀ j, 1 ≤ j → j ≤ n → 0 < m j) :
    0 < (Delta γ m n n).re ∧ (Delta γ m n n).im = 0 := by
  rw [show Delta γ m n n = (Hn γ m n).det from rfl]
  exact det_Hn_pos_of_reels_distincts γ m n hreal
    (fun i j hi hin hj hjn h => hdist i j hi hin hj hjn h) hmpos

lemma det_vandermonde_extrait_ne_zero (γ : ℕ → ℂ) (n r : ℕ)
    (hdist : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → γ i = γ j → i = j)
    (σ : Fin r → Fin n) (hσ : Function.Injective σ) :
    (Matrix.of fun (p q : Fin r) => γ ((σ q : ℕ) + 1) ^ (p : ℕ)).det ≠ 0 := by
  have hV : (Matrix.of fun (p q : Fin r) => γ ((σ q : ℕ) + 1) ^ (p : ℕ)) =
      (Matrix.vandermonde (fun q : Fin r => γ ((σ q : ℕ) + 1))).transpose := by
    ext p q
    simp [Matrix.vandermonde, Matrix.transpose_apply]
  rw [hV, Matrix.det_transpose, Matrix.det_vandermonde]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hij : j ≠ i := (Finset.mem_Ioi.mp hj).ne'
  apply sub_ne_zero.mpr
  intro h
  have h1 := hdist _ _ (by omega) (by have := (σ j).isLt; omega)
    (by omega) (by have := (σ i).isLt; omega) h.symm
  exact hij (hσ (Fin.ext (by omega)))

lemma det_extrait_im_zero (γ : ℕ → ℂ) (n r : ℕ)
    (hreal : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0)
    (σ : Fin r → Fin n) :
    (Matrix.of fun (p q : Fin r) => γ ((σ q : ℕ) + 1) ^ (p : ℕ)).det.im = 0 := by
  have hγ : ∀ q : Fin r, γ ((σ q : ℕ) + 1) = (((γ ((σ q : ℕ) + 1)).re : ℝ) : ℂ) := fun q =>
    eq_ofReal_of_im_eq_zero _ (hreal _ (by omega) (by have := (σ q).isLt; omega))
  have hM : (Matrix.of fun (p q : Fin r) => γ ((σ q : ℕ) + 1) ^ (p : ℕ)) =
      (Matrix.of fun (p q : Fin r) => (((γ ((σ q : ℕ) + 1)).re ^ (p : ℕ) : ℝ) : ℂ)) := by
    ext p q
    simp only [Matrix.of_apply]
    rw [hγ q]
    push_cast
    rfl
  rw [hM]
  have : (Matrix.of fun (p q : Fin r) => (((γ ((σ q : ℕ) + 1)).re ^ (p : ℕ) : ℝ) : ℂ)) =
      (algebraMap ℝ ℂ).mapMatrix
        (Matrix.of fun (p q : Fin r) => (γ ((σ q : ℕ) + 1)).re ^ (p : ℕ)) := by
    ext p q; simp
  rw [this, ← RingHom.map_det]
  exact Complex.ofReal_im _

lemma eval_poly_comb (r : ℕ) (x : Fin r → ℝ) (t : ℝ) :
    (∑ p : Fin r, Polynomial.C (x p) * Polynomial.X ^ (p : ℕ)).eval t
      = ∑ p : Fin r, x p * t ^ (p : ℕ) := by
  have h : (∑ p : Fin r, Polynomial.C (x p) * Polynomial.X ^ (p : ℕ)).eval t
      = (Polynomial.evalRingHom t) (∑ p : Fin r, Polynomial.C (x p) * Polynomial.X ^ (p : ℕ)) := rfl
  rw [h, map_sum]
  simp

lemma coeff_poly_comb (r : ℕ) (x : Fin r → ℝ) (k : Fin r) :
    (∑ p : Fin r, Polynomial.C (x p) * Polynomial.X ^ (p : ℕ)).coeff (k : ℕ) = x k := by
  have h : (∑ p : Fin r, Polynomial.C (x p) * Polynomial.X ^ (p : ℕ)).coeff (k : ℕ)
      = (Polynomial.lcoeff ℝ (k : ℕ)) (∑ p : Fin r,
      Polynomial.C (x p) * Polynomial.X ^ (p : ℕ)) := rfl
  rw [h, map_sum]
  simp only [Polynomial.lcoeff_apply,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  simp [Fin.val_inj]

lemma degree_poly_comb (r : ℕ) (hr : 0 < r) (x : Fin r → ℝ) :
    (∑ p : Fin r, Polynomial.C (x p) * Polynomial.X ^ (p : ℕ)).natDegree < r := by
  refine lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := r - 1) ?_) (by omega)
  intro p _
  refine (Polynomial.natDegree_C_mul_X_pow_le (x p) (p : ℕ)).trans ?_
  have := p.isLt
  omega

lemma poly_comb_eq_zero (n r : ℕ) (hrn : r ≤ n) (hr : 0 < r)
    (τ : Fin n → ℝ) (hτ : Function.Injective τ) (x : Fin r → ℝ)
    (hx : ∀ j, ∑ p : Fin r, x p * τ j ^ (p : ℕ) = 0) :
    (∑ p : Fin r, Polynomial.C (x p) * Polynomial.X ^ (p : ℕ)) = 0 := by
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hτ
  · intro j
    rw [eval_poly_comb]
    exact hx j
  · rw [Fintype.card_fin]
    exact lt_of_lt_of_le (degree_poly_comb r hr x) hrn

lemma vandermonde_comb_inj (n r : ℕ) (hrn : r ≤ n)
    (τ : Fin n → ℝ) (hτ : Function.Injective τ) (x : Fin r → ℝ)
    (hx : ∀ j, ∑ p : Fin r, x p * τ j ^ (p : ℕ) = 0) : x = 0 := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    funext p
    exact p.elim0
  · have hP0 := poly_comb_eq_zero n r hrn hr τ hτ x hx
    funext k
    have := coeff_poly_comb r x k
    rw [hP0] at this
    simpa using this.symm

lemma gram_entry (n r : ℕ) (τ w : Fin n → ℝ) (p q : Fin r) :
    (((Matrix.of fun (p : Fin r) (j : Fin n) => τ j ^ (p : ℕ)) *
      Matrix.diagonal w) *
      Matrix.of fun (j : Fin n) (q : Fin r) => τ j ^ (q : ℕ)) p q
    = ∑ j, τ j ^ (p : ℕ) * w j * τ j ^ (q : ℕ) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Matrix.diagonal_apply_ne _ hb]
  · intro h
    exact absurd (Finset.mem_univ j) h




lemma gram_quadratic_form (n r : ℕ) (τ w : Fin n → ℝ) (x : Fin r → ℝ) :
    star x ⬝ᵥ ((((Matrix.of fun (p : Fin r) (j : Fin n) => τ j ^ (p : ℕ)) *
        Matrix.diagonal w) *
        Matrix.of fun (j : Fin n) (q : Fin r) => τ j ^ (q : ℕ)) *ᵥ x)
      = ∑ j, w j * (∑ p : Fin r, x p * τ j ^ (p : ℕ)) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, gram_entry]
  have key : ∀ j : Fin n, w j * (∑ p : Fin r, x p * τ j ^ (p : ℕ)) ^ 2
      = ∑ p : Fin r, ∑ q : Fin r, x p * (τ j ^
        (p : ℕ) * w j * τ j ^ (q : ℕ)) * x q := by
    intro j
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    ring
  simp only [key]
  have hL : ∀ p : Fin r, x p * ∑ q : Fin r, (∑ j :
    Fin n, τ j ^ (p : ℕ) * w j * τ j ^ (q : ℕ)) * x q
      = ∑ q : Fin r, ∑ j : Fin n, x p * (τ j ^ (p : ℕ) *
        w j * τ j ^ (q : ℕ)) * x q := by
    intro p
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  simp only [hL]
  calc ∑ p : Fin r, ∑ q : Fin r, ∑ j : Fin n, x p *
    (τ j ^ (p : ℕ) * w j * τ j ^ (q : ℕ)) * x q
      = ∑ p : Fin r, ∑ j : Fin n, ∑ q : Fin r, x p *
      (τ j ^ (p : ℕ) * w j * τ j ^ (q : ℕ)) * x q := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        exact Finset.sum_comm
    _ = ∑ j : Fin n, ∑ p : Fin r, ∑ q : Fin r, x p * (τ j ^
      (p : ℕ) * w j * τ j ^ (q : ℕ)) * x q :=
        Finset.sum_comm

lemma gram_isHermitian (n r : ℕ) (τ w : Fin n → ℝ) :
    ((((Matrix.of fun (p : Fin r) (j : Fin n) => τ j ^ (p : ℕ)) *
      Matrix.diagonal w) *
      Matrix.of fun (j : Fin n) (q : Fin r) => τ j ^ (q : ℕ))).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  ext p q
  rw [Matrix.transpose_apply, gram_entry, gram_entry]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring



lemma gram_posDef_of_distinct (n r : ℕ) (hrn : r ≤ n)
    (τ w : Fin n → ℝ) (hτ : Function.Injective τ) (hw : ∀ j, 0 < w j) :
    (((Matrix.of fun (p : Fin r) (j : Fin n) => τ j ^ (p : ℕ)) *
      Matrix.diagonal w) *
      Matrix.of fun (j : Fin n) (q : Fin r) => τ j ^ (q : ℕ)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨gram_isHermitian n r τ w, ?_⟩
  intro x hx
  rw [gram_quadratic_form n r τ w x]
  have hne : ∃ j, ∑ p : Fin r, x p * τ j ^ (p : ℕ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (vandermonde_comb_inj n r hrn τ hτ x hcon)
  obtain ⟨j₀, hj₀⟩ := hne
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (hw j).le (sq_nonneg _)
  · exact ⟨j₀, Finset.mem_univ _, mul_pos (hw j₀) (by positivity)⟩

lemma gram_complex_eq_map_real (γ : ℕ → ℂ) (m : ℕ → ℕ) (n r : ℕ)
    (hreal : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0) :
    (((Matrix.of fun (p : Fin r) (j : Fin n) => γ ((j : ℕ) + 1) ^ (p : ℕ)) *
        Matrix.diagonal fun j : Fin n => ((m ((j : ℕ) + 1) : ℕ) : ℂ)) *
        Matrix.of fun (j : Fin n) (q : Fin r) => γ ((j : ℕ) + 1) ^ (q : ℕ))
    = ((((Matrix.of fun (p : Fin r) (j : Fin n) => ((γ ((j : ℕ) + 1)).re) ^ (p : ℕ)) *
          Matrix.diagonal fun j : Fin n => ((m ((j : ℕ) + 1) : ℕ) : ℝ)) *
          Matrix.of fun (j : Fin n) (q : Fin r) => ((γ ((j : ℕ) + 1)).re) ^ (q : ℕ))).map
          (algebraMap ℝ ℂ) := by
  have hγre : ∀ j : Fin n, γ ((j : ℕ) + 1) = ((γ ((j : ℕ) + 1)).re : ℂ) := by
    intro j
    apply Complex.ext
    · simp
    · simp [hreal _ (Nat.succ_pos _) j.isLt]
  ext p q
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.of_apply, Complex.coe_algebraMap]
  have e : ∀ l : Fin n, ((γ ((l : ℕ) + 1)).re : ℂ) = γ ((l : ℕ) + 1) :=
    fun l => (hγre l).symm
  have hif : ∀ (b : Prop) [Decidable b] (a : ℕ),
      (((if b then (a : ℝ) else 0 : ℝ)) : ℂ) = if b then (a : ℂ) else 0 := by
    intro b _ a
    split_ifs <;> simp
  push_cast
  simp only [hif, e]

lemma delta_pos_of_real_distinct (γ : ℕ → ℂ) (m : ℕ → ℕ) (n r : ℕ)
    (hreal : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0)
    (hdist : ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → γ i = γ j → i = j)
    (hmpos : ∀ j, 1 ≤ j → j ≤ n → 0 < m j)
    (_ : 1 ≤ r) (hrn : r ≤ n) :
    0 < (Delta γ m n r).re ∧ (Delta γ m n r).im = 0 := by
  unfold Delta
  rw [newton_gram_factor γ m n r]
  set τ : Fin n → ℝ := fun j => (γ ((j : ℕ) + 1)).re with hτdef
  set w : Fin n → ℝ := fun j => (m ((j : ℕ) + 1) : ℝ) with hwdef
  have hτ : Function.Injective τ := by
    intro i j hij
    have hi : 1 ≤ (i : ℕ) + 1 := Nat.succ_pos _
    have hi' : (i : ℕ) + 1 ≤ n := i.isLt
    have hj : 1 ≤ (j : ℕ) + 1 := Nat.succ_pos _
    have hj' : (j : ℕ) + 1 ≤ n := j.isLt
    have hγ : γ ((i : ℕ) + 1) = γ ((j : ℕ) + 1) := by
      apply Complex.ext
      · exact hij
      · rw [hreal _ hi hi', hreal _ hj hj']
    have := hdist _ _ hi hi' hj hj' hγ
    exact Fin.ext (by omega)
  have hw : ∀ j, 0 < w j := by
    intro j
    have h := hmpos ((j : ℕ) + 1) (Nat.succ_pos _) j.isLt
    change (0 : ℝ) < (m ((j : ℕ) + 1) : ℝ)
    exact_mod_cast h
  have hmap := gram_complex_eq_map_real γ m n r hreal
  rw [hmap]
  have hpos : 0 < (((Matrix.of fun (p : Fin r) (j : Fin n) => τ j ^ (p : ℕ)) *
        Matrix.diagonal w) *
        Matrix.of fun (j : Fin n) (q : Fin r) => τ j ^ (q : ℕ)).det :=
    (gram_posDef_of_distinct n r hrn τ w hτ hw).det_pos
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  constructor
  · simpa using hpos
  · simp


lemma hankelPositive_of_all_real (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hreal : ∀ k, 1 ≤ k → (γ k).im = 0) :
    HankelPositive γ m := by
  intro n hn
  refine ⟨fun k _ => newton_im_zero_of_real γ m n k (fun j hj _ => hreal j hj), ?_⟩
  intro r hr1 hrn
  exact delta_pos_of_real_distinct γ m n r
    (fun j hj _ => hreal j hj)
    (fun i j hi _ hj _ h => hEnum.injective i j hi hj h)
    (fun j hj _ => hEnum.mult_pos j hj)
    hr1 hrn

theorem hankelPositive_iff_all_real (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hcompat : ConjCompatible γ m) :
    HankelPositive γ m ↔ ∀ k, 1 ≤ k → (γ k).im = 0 :=
  ⟨all_real_of_hankelPositive γ m hEnum hcompat,
   hankelPositive_of_all_real γ m hEnum⟩


open BrainrotLemma_Riemann SylvesterCrit

theorem hPosProof_two_zeros (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hcompat : ConjCompatible γ m)
    (_ : HardyTheorem)
    (hall : (∀ n₀, PalierCritique γ m n₀ → False)) :
    HankelPositive γ m := by
  rw [hankelPositive_iff_all_real γ m hEnum hcompat]
  intro k hk
  by_contra hne
  obtain ⟨n₀, h3, hreal, hnon⟩ :=
    exists_first_nonreal γ hEnum.real_one hEnum.real_two ⟨k, hk, hne⟩
  have hpal : PalierCritique γ m n₀ := by
    refine ⟨h3, hreal, hnon, hcompat.conj_next n₀ h3 hnon, ?_, hcompat.mult_next n₀ h3 hnon, ?_⟩
    · intro j hj1 _
      exact hEnum.mult_pos j hj1
    · intro i j hi1 _ hj1 _ h
      exact hEnum.injective i j hi1 hj1 h
  exact hall n₀ hpal

theorem hPosProof_two_zeros' (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hcompat : ConjCompatible γ m)
    (_ : HardyTheorem)
    (hBrain : ∀ n₀, PalierCritique γ m n₀ →
      (Delta γ m (n₀ + 1) (n₀ + 1)).re < 0)
    (hpos : HankelPositive γ m) :
    ∀ k, 1 ≤ k → (γ k).im = 0 := by
  intro k hk
  by_contra hne
  obtain ⟨n₀, h3, hreal, hnon⟩ :=
    exists_first_nonreal γ hEnum.real_one hEnum.real_two ⟨k, hk, hne⟩
  have hpalier : PalierCritique γ m n₀ :=
    { n0_ge := h3
      reels_avant := hreal
      non_reel := hnon
      conj_zero := hcompat.conj_next n₀ h3 hnon
      mult_pos := fun j hj1 _ => hEnum.mult_pos j hj1
      mult_conj := hcompat.mult_next n₀ h3 hnon
      injectif := fun i j hi1 _ hj1 _ h => hEnum.injective i j hi1 hj1 h }
  have hneg := hBrain n₀ hpalier
  have hdet : ((Hn γ m (n₀ + 1)).det).re < 0 := by
    rw [← Delta_self]; exact hneg
  exact not_HankelPositive_of_det_neg γ m (n₀ + 1) (by omega) hdet hpos

theorem hankel_real_of_all_minors_or_contra
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hcompat : ConjCompatible γ m)
    (_ : ∀ n₀, PalierCritique γ m n₀ →
      (Delta γ m (n₀ + 1) (n₀ + 1)).re < 0) :
    HankelPositive γ m → ∀ k, 1 ≤ k → (γ k).im = 0 :=
  fun hpos => all_real_of_hankelPositive γ m hEnum hcompat hpos

theorem hankelPositive_iff_real_of_hardy
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hcompat : ConjCompatible γ m)
    (_ : HardyTheorem) :
    HankelPositive γ m ↔ ∀ k, 1 ≤ k → (γ k).im = 0 :=
  hankelPositive_iff_all_real γ m hEnum hcompat

theorem hPosProof_conditionnal (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (_ : ConjCompatible γ m)
    (hRH : ∀ k, 1 ≤ k → (γ k).im = 0) :
    HankelPositive γ m :=
  hankelPositive_of_all_real γ m hEnum hRH

lemma init_rank_two_XiEntiere (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (h : ZeroEnumeration (fun z => xiEntiere (1 / 2 + Complex.I * z)) γ m) :
    (∀ k, (newton γ m 2 k).im = 0) ∧
    (0 < (Delta γ m 2 1).re ∧ (Delta γ m 2 1).im = 0) ∧
    (0 < (Delta γ m 2 2).re ∧ (Delta γ m 2 2).im = 0) ∧
    ∃ (g₁ g₂ : ℝ), g₁ ≠ g₂ ∧ γ 1 = g₁ ∧ γ 2 = g₂ ∧
      (H2R (m 1) (m 2) g₁ g₂).PosDef ∧
      Hn γ m 2 = (H2R (m 1) (m 2) g₁ g₂).map (algebraMap ℝ ℂ) :=
  init_rank_two (fun z => xiEntiere (1 / 2 + Complex.I * z)) γ m h

lemma init_rank_two_XiRiemann (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (h : ZeroEnumeration XiRiemann γ m) :
    (∀ k, (newton γ m 2 k).im = 0) ∧
    (0 < (Delta γ m 2 1).re ∧ (Delta γ m 2 1).im = 0) ∧
    (0 < (Delta γ m 2 2).re ∧ (Delta γ m 2 2).im = 0) ∧
    ∃ (g₁ g₂ : ℝ), g₁ ≠ g₂ ∧ γ 1 = g₁ ∧ γ 2 = g₂ ∧
      (H2R (m 1) (m 2) g₁ g₂).PosDef ∧
      Hn γ m 2 = (H2R (m 1) (m 2) g₁ g₂).map (algebraMap ℝ ℂ) :=
  init_rank_two XiRiemann γ m h

open ComplexConjugate


lemma XiRiemann_conj_forall :
    ∀ z : ℂ, XiRiemann ((starRingEnd ℂ) z) = (starRingEnd ℂ) (XiRiemann z) := by
  intro z
  change xiEntiere (1/2 + Complex.I * (starRingEnd ℂ) z)
      = (starRingEnd ℂ) (xiEntiere (1/2 + Complex.I * z))
  rw [← xiEntiere_conj_forall]
  have h : (starRingEnd ℂ) (1/2 + Complex.I * z)
      = 1 - (1/2 + Complex.I * (starRingEnd ℂ) z) := by
    simp only [map_add, map_mul, map_div₀, map_one, Complex.conj_I, map_ofNat]
    ring
  rw [h]
  exact (xiEntiere_one_sub _).symm

lemma Delta_pos_before_palier
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (hEnum : ZeroEnumeration XiRiemann γ m)
    (n₀ : ℕ) (hn₀3 : 3 ≤ n₀)
    (hreal : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) :
    ∀ r, 1 ≤ r → r ≤ n₀ - 1 →
      0 < (Delta γ m (n₀ - 1) r).re ∧ (Delta γ m (n₀ - 1) r).im = 0 := by
  intro r hr1 hrn
  apply delta_pos_of_real_distinct γ m (n₀ - 1) r
  · intro j hj1 hjn
    exact hreal j hj1 (by omega)
  · intro i j hi hin hj hjn hij
    exact hEnum.injective i j hi hj hij
  · intro j hj1 _
    exact hEnum.mult_pos j hj1
  · exact hr1
  · exact hrn

lemma newton_re_eq (γ : ℕ → ℂ) (m : ℕ → ℕ) (N : ℕ)
    (h : ∀ k, (newton γ m N k).im = 0) (k : ℕ) :
    ((newton γ m N k).re : ℂ) = newton γ m N k := by
  apply Complex.ext
  · simp
  · simp [h k]

lemma zero_critique_to_XiRiemann (s : ℂ) (hs : s ∈ zerosCritiques) :
    XiRiemann (-Complex.I * (s - 1 / 2)) = 0 := by
  obtain ⟨hzeta, hre⟩ := hs
  rw [XiRiemann_eq]
  have harg : (1 / 2 : ℂ) + Complex.I * (-Complex.I * (s - 1 / 2)) = s := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    linear_combination (s - 1 / 2) * hI * (-1 : ℂ)
  rw [harg]
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at hre; norm_num at hre
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at hre; norm_num at hre
  have hpos : 0 < s.re := by rw [hre]; norm_num
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hpos
  have hc : completedRiemannZeta s = 0 := by
    have hz : riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
      riemannZeta_def_of_ne_zero hs0
    rw [hzeta] at hz
    exact (div_eq_zero_iff.mp hz.symm).resolve_right hG
  rw [← xi_eq_xiEntiere s hs0 hs1]
  unfold xi
  rw [hc, mul_zero]


lemma hardy_gives_infinite_real_indices
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (hEnum : ZeroEnumeration XiRiemann γ m)
    (hHardy : HardyTheorem) :
    Set.Infinite {k : ℕ | 1 ≤ k ∧ (γ k).im = 0} := by
  have hex : ∀ s ∈ zerosCritiques, ∃ k, 1 ≤ k ∧ γ k = -Complex.I * (s - 1 / 2) := by
    intro s hs
    exact hEnum.exhaustive _ (zero_critique_to_XiRiemann s hs)
  have hreal : ∀ s ∈ zerosCritiques, (-Complex.I * (s - 1 / 2)).im = 0 := by
    intro s hs
    have h : s.re = 1 / 2 := hs.2
    simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, h]
  have hinj : Function.Injective (fun s : ℂ => -Complex.I * (s - 1 / 2)) := by
    intro a b hab
    have hab' : -Complex.I * (a - 1 / 2) = -Complex.I * (b - 1 / 2) := hab
    have h1 : a = b := by
      linear_combination Complex.I * hab' + (a - b) * Complex.I_sq
    exact h1
  choose! κ hκ1 hκγ using hex
  have hκinj : Set.InjOn κ zerosCritiques := by
    intro a ha b hb hab
    apply hinj
    change -Complex.I * (a - 1 / 2) = -Complex.I * (b - 1 / 2)
    rw [← hκγ a ha, ← hκγ b hb, hab]
  have hsub : κ '' zerosCritiques ⊆ {k : ℕ | 1 ≤ k ∧ (γ k).im = 0} := by
    rintro k ⟨s, hs, rfl⟩
    refine ⟨hκ1 s hs, ?_⟩
    rw [hκγ s hs]
    exact hreal s hs
  exact Set.Infinite.mono hsub (hHardy.image hκinj)

lemma propagation_defaut
    (γ : ℕ → ℂ)
    (m : ℕ → ℕ)
    (hcompat : ConjCompatible γ m)
    (n₀ : ℕ)
    (hpalier : PalierCritique γ m n₀) :
    PropagationDefaut γ n₀ := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact hpalier.non_reel
  | succ N hN ih =>
      have hc : γ (N + 1) = starRingEnd ℂ (γ N) :=
        hcompat.conj_next N (le_trans hpalier.n0_ge hN) ih
      rw [hc, Complex.conj_im]
      exact neg_ne_zero.mpr ih

theorem hankelPositive_of_hardy
    (γ : ℕ → ℂ)
    (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hcompat : ConjCompatible γ m)
    (hHardy : HardyTheorem) :
    HankelPositive γ m := by
  refine hankelPositive_of_all_real γ m hEnum ?_
  by_contra hcon
  push Not at hcon
  classical
  have hex : ∃ k, 1 ≤ k ∧ (γ k).im ≠ 0 := hcon
  obtain ⟨n₀, hn₀, hmin⟩ : ∃ n₀, (1 ≤ n₀ ∧ (γ n₀).im ≠ 0) ∧
      ∀ j, j < n₀ → ¬ (1 ≤ j ∧ (γ j).im ≠ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hreal_before : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0 := by
    intro j hj1 hjlt
    by_contra hne
    exact hmin j hjlt ⟨hj1, hne⟩
  have hn₀3 : 3 ≤ n₀ := by
    by_contra hlt
    push Not at hlt
    have h12 : n₀ = 1 ∨ n₀ = 2 := by omega
    rcases h12 with h1 | h2
    · exact hn₀.2 (h1 ▸ hEnum.real_one)
    · exact hn₀.2 (h2 ▸ hEnum.real_two)
  have hconj : γ (n₀ + 1) = conj (γ n₀) := hcompat.conj_next n₀ hn₀3 hn₀.2
  have hmult : m (n₀ + 1) = m n₀ := hcompat.mult_next n₀ hn₀3 hn₀.2
  have hpalier : PalierCritique γ m n₀ :=
    { n0_ge       := hn₀3
      reels_avant := hreal_before
      non_reel    := hn₀.2
      conj_zero   := hconj
      mult_pos    := fun j hj1 _ => hEnum.mult_pos j hj1
      mult_conj   := hmult
      injectif    := fun i j hi _ hj _ hij => hEnum.injective i j hi hj hij }
  have hbrain := brainrot_Lemma XiRiemann XiRiemann_conj_forall γ m hEnum n₀ hpalier
  obtain ⟨_, ⟨_, hDelta_neg, hDelta_im, _⟩, hprop, _⟩ := hbrain
  have hprop_def := propagation_defaut γ m hcompat n₀ hpalier
  have hsub : {k : ℕ | 1 ≤ k ∧ (γ k).im = 0} ⊆ (Finset.range n₀ : Set ℕ) := by
    intro k hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hge
    push Not at hge
    exact hprop_def k hge hk.2
  exact (hardy_gives_infinite_real_indices γ m hEnum hHardy)
    ((Finset.range n₀).finite_toSet.subset hsub)


end hPosRiemann
