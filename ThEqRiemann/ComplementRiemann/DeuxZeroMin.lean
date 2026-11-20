import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.ComplementRiemann.DecaleZeroProperty
import ThEqRiemann.ComplementRiemann.InvarianceIntegralMobius
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.SpectrumInversion
import ThEqRiemann.EqTheorem.ObservableAnalytiqueSelection
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2

/-! -/
namespace ZeroMin2

open Set Complex
open RiemannDef DefinitionsThEq DecaleZeroProp InvaranceIntMobius
open CircInt2

theorem exclusion_cadre_spectral_bis
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


lemma lam_neg_conj_eq_conj_lam (w : ℂ) :
    (-Complex.I) * (-(starRingEnd ℂ) w) = (starRingEnd ℂ) ((-Complex.I) * w) := by
  simp only [map_mul, map_neg, Complex.conj_I]
  ring

lemma lam_im_eq_neg_re (w : ℂ) :
    ((-Complex.I) * w).im = -w.re := by
  simp [Complex.mul_im]

lemma XiRiemann_neg (z : ℂ) : XiRiemann (-z) = XiRiemann z := by
  rw [XiRiemann_eq, XiRiemann_eq]
  have h_arg : (1 / 2 : ℂ) + Complex.I * (-z) =
    1 - ((1 / 2 : ℂ) + Complex.I * z) := by
    ring
  rw [h_arg, xiEntiere_one_sub]

lemma XiRiemann_neg_zero {z : ℂ} (hz : XiRiemann z = 0) :
    XiRiemann (-z) = 0 := by
  rw [XiRiemann_neg, hz]

lemma XiRiemann_conj_zero
    (hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) =
    (starRingEnd ℂ) (xiDecale w))
    {z : ℂ} (hz : XiRiemann z = 0) :
    XiRiemann ((starRingEnd ℂ) z) = 0 := by
  unfold XiRiemann at hz ⊢
  have h1 : Complex.I * (starRingEnd ℂ) z = -(starRingEnd ℂ)
    (Complex.I * z) := by
    simp only [map_mul, Complex.conj_I, neg_mul, neg_neg]
  rw [h1, hsym (Complex.I * z), hz, map_zero]

lemma conj_pair_of_im_ne_zero_via_exclusion
    {K : ℕ} (zs : Fin K → ℂ) (m : Fin K → ℕ)
    (hm : ∀ j, 0 < m j)
    (hinj : Function.Injective (fun j => (-Complex.I) * zs j))
    (hsym : ∀ j, ∃ k, zs k = -(starRingEnd ℂ) (zs j))
    (j : Fin K)
    (him : ((-Complex.I) * zs j).im ≠ 0) :
    ∃ k : Fin K, k ≠ j ∧
      (-Complex.I) * zs k = (starRingEnd ℂ) ((-Complex.I) * zs j) := by
  have hre : (zs j).re ≠ 0 := by
    rw [lam_im_eq_neg_re] at him
    exact neg_ne_zero.mp him
  have hexcl := (exclusion_cadre_spectral_bis zs m hm hinj hsym).2.2.2
  exact hexcl j hre

lemma conj_ne_self_of_im_ne_zero {z : ℂ} (him : z.im ≠ 0) :
    (starRingEnd ℂ) z ≠ z := by
  intro h
  have him_eq : ((starRingEnd ℂ) z).im = z.im := congrArg Complex.im h
  simp only [Complex.conj_im] at him_eq
  have hz_im_zero : z.im = 0 := by linarith
  exact him hz_im_zero

lemma norm_symmetries (z : ℂ) :
    ‖-z‖ = ‖z‖ ∧
    ‖(starRingEnd ℂ) z‖ = ‖z‖ ∧
    ‖-(starRingEnd ℂ) z‖ = ‖z‖ := by
   refine ⟨norm_neg z, Complex.norm_conj z, ?_⟩
   rw [norm_neg, Complex.norm_conj]

lemma conj_ne_neg_and_neg_ne_self_of_re_ne_zero {z : ℂ} (hre : z.re ≠ 0) :
    (starRingEnd ℂ) z ≠ -z ∧ -z ≠ z := by
  constructor
  · intro h
    have hre_eq : ((starRingEnd ℂ) z).re = (-z).re := congrArg Complex.re h
    simp only [Complex.conj_re, Complex.neg_re] at hre_eq
    have hz_re_zero : z.re = 0 := by linarith
    exact hre hz_re_zero
  · intro h
    have hre_eq : (-z).re = z.re := congrArg Complex.re h
    simp only [Complex.neg_re] at hre_eq
    have hz_re_zero : z.re = 0 := by linarith
    exact hre hz_re_zero

lemma norm_b_eq_norm_a
    (a b : ℂ)
    (ha : XiRiemann a = 0) (hb : XiRiemann b = 0) (ha0 : a ≠ 0)
    (hamin' : ∀ z : ℂ, XiRiemann z = 0 → ‖a‖ ≤ ‖z‖)
    (hbmin' : ∀ z : ℂ, XiRiemann z = 0 → z ≠ a → ‖b‖ ≤ ‖z‖) :
    ‖b‖ = ‖a‖ := by
  have hab : ‖a‖ ≤ ‖b‖ := hamin' b hb
  have h_neg_a_zero : XiRiemann (-a) = 0 := XiRiemann_neg_zero ha
  have h_neg_a_ne : -a ≠ a := neg_ne_self.mpr ha0
  have hba : ‖b‖ ≤ ‖-a‖ := hbmin' (-a) h_neg_a_zero h_neg_a_ne
  rw [norm_neg] at hba
  exact le_antisymm hba hab

lemma deux_plus_petits_zeros_reels_of_cercle_minimal
    (a b : ℂ)
    (ha : XiRiemann a = 0) (hb : XiRiemann b = 0) (_ : b ≠ a)
    (hamin' : ∀ z : ℂ, XiRiemann z = 0 → ‖a‖ ≤ ‖z‖)
    (hbmin' : ∀ z : ℂ, XiRiemann z = 0 → z ≠ a → ‖b‖ ≤ ‖z‖)
    (hsym : ∀ w,
    xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w))
    (hre_ne : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z.re ≠ 0)
    (hdeux_cercle : ∀ z : ℂ,
    XiRiemann z = 0 → ‖z‖ = ‖a‖ → z = a ∨ z = -a) :
    a.im = 0 ∧ b.im = 0 := by
  have ha_re : a.re ≠ 0 := hre_ne a ha rfl
  have ha0 : a ≠ 0 := by
    intro h0
    apply ha_re
    simp [h0]
  have hnorm_ba : ‖b‖ = ‖a‖ := norm_b_eq_norm_a a b ha hb ha0 hamin' hbmin'
  have hconj_a_zero : XiRiemann ((starRingEnd ℂ) a) = 0 :=
    XiRiemann_conj_zero hsym ha
  have hconj_a_norm : ‖(starRingEnd ℂ) a‖ = ‖a‖ := Complex.norm_conj a
  have h_cases_a : (starRingEnd ℂ) a = a ∨ (starRingEnd ℂ) a = -a :=
    hdeux_cercle ((starRingEnd ℂ) a) hconj_a_zero hconj_a_norm
  have ha_im : a.im = 0 := by
    rcases h_cases_a with h_eq | h_neg
    · by_contra him
      exact conj_ne_self_of_im_ne_zero him h_eq
    · exfalso
      exact (conj_ne_neg_and_neg_ne_self_of_re_ne_zero ha_re).1 h_neg
  have h_cases_b : b = a ∨ b = -a := hdeux_cercle b hb hnorm_ba
  have hb_im : b.im = 0 := by
    rcases h_cases_b with rfl | rfl
    · exact ha_im
    · simp [ha_im]
  exact ⟨ha_im, hb_im⟩

lemma xiDecale_symm_conj
    (h_schwarz : ∀ s : ℂ, xiEntiere ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xiEntiere s))
    (w : ℂ) :
    xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w) := by
  unfold xiDecale
  have h_arg : (1 / 2 : ℂ) + -(starRingEnd ℂ) w =
      1 - (starRingEnd ℂ) ((1 / 2 : ℂ) + w) := by
    simp only [map_add, map_div₀, map_ofNat, map_one]
    ring
  rw [h_arg, xiEntiere_one_sub]
  exact h_schwarz ((1 / 2 : ℂ) + w)

open ComplexConjugate XiEntiereRiemann in
lemma XiRiemann_conj_symm' (z : ℂ) :
    XiRiemann (conj z) = conj (XiRiemann (-z)) := by
  unfold XiRiemann RiemannDef.xiDecale
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  have harg : (1 / 2 : ℂ) + I * conj z = conj ((1 / 2 : ℂ) + I * (-z)) := by
    simp only [map_add, map_mul, map_neg, map_div₀, map_one, Complex.conj_I, h2]
    ring
  rw [harg, xiEntiere_conj]

lemma re_ne_zero_of_strip_and_norm_ge_half
    (a : ℂ)
    (h_strip : ∀ z : ℂ, XiRiemann z = 0 → |z.im| < 1 / 2)
    (ha_norm : (1 / 2 : ℝ) ≤ ‖a‖) :
    ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z.re ≠ 0 := by
  intro z hz hnorm hre0
  have hz_eq : z = (z.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simp [hre0]
    · simp
  have hnorm_im : ‖z‖ = |z.im| := by
    nth_rw 1 [hz_eq]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have him_lt : |z.im| < 1 / 2 := h_strip z hz
  linarith

lemma deux_cercle_of_au_plus_deux
    (a : ℂ) (ha : XiRiemann a = 0)
    (hre_ne : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z.re ≠ 0)
    (h_au_plus_deux : ∀ z₁ z₂ z₃ : ℂ,
      XiRiemann z₁ = 0 → XiRiemann z₂ = 0 → XiRiemann z₃ = 0 →
      ‖z₁‖ = ‖a‖ → ‖z₂‖ = ‖a‖ → ‖z₃‖ = ‖a‖ →
      z₁ ≠ z₂ → z₃ = z₁ ∨ z₃ = z₂) :
    ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z = a ∨ z = -a := by
  intro z hz hnorm
  have ha_re : a.re ≠ 0 := hre_ne a ha rfl
  have h_neg_a_zero : XiRiemann (-a) = 0 := XiRiemann_neg_zero ha
  have h_neg_a_ne_a : -a ≠ a := (conj_ne_neg_and_neg_ne_self_of_re_ne_zero ha_re).2
  exact h_au_plus_deux a (-a) z ha h_neg_a_zero hz rfl (norm_neg a) hnorm h_neg_a_ne_a.symm

lemma deux_plus_petits_zeros_reels_preproof
    (a b : ℂ)
    (ha : XiRiemann a = 0) (hb : XiRiemann b = 0) (hba : b ≠ a)
    (hamin' : ∀ z : ℂ, XiRiemann z = 0 → ‖a‖ ≤ ‖z‖)
    (hbmin' : ∀ z : ℂ, XiRiemann z = 0 → z ≠ a → ‖b‖ ≤ ‖z‖)
    (h_schwarz : ∀ s : ℂ, xiEntiere ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xiEntiere s))
    (h_strip : ∀ z : ℂ, XiRiemann z = 0 → |z.im| < 1 / 2)
    (ha_norm : (1 / 2 : ℝ) ≤ ‖a‖)
    (h_au_plus_deux : ∀ z₁ z₂ z₃ : ℂ,
      XiRiemann z₁ = 0 → XiRiemann z₂ = 0 → XiRiemann z₃ = 0 →
      ‖z₁‖ = ‖a‖ → ‖z₂‖ = ‖a‖ → ‖z₃‖ = ‖a‖ →
      z₁ ≠ z₂ → z₃ = z₁ ∨ z₃ = z₂) :
    a.im = 0 ∧ b.im = 0 := by
  have hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w) :=
    xiDecale_symm_conj h_schwarz
  have hre_ne : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z.re ≠ 0 :=
    re_ne_zero_of_strip_and_norm_ge_half a h_strip ha_norm
  have hdeux_cercle : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z = a ∨ z = -a :=
    deux_cercle_of_au_plus_deux a ha hre_ne h_au_plus_deux
  exact deux_plus_petits_zeros_reels_of_cercle_minimal
    a b ha hb hba hamin' hbmin' hsym hre_ne hdeux_cercle

theorem deux_premiers_zeros_reels_of_minimal
    (a : ℂ) (ha : XiRiemann a = 0)
    (hamin' : ∀ z : ℂ, XiRiemann z = 0 → ‖a‖ ≤ ‖z‖)
    (hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w))
    (hre_ne : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z.re ≠ 0)
    (hdeux_cercle : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z = a ∨ z = -a) :
    DeuxPremiersZerosReels := by
  have ha_re : a.re ≠ 0 := hre_ne a ha rfl
  have hba : -a ≠ a := (conj_ne_neg_and_neg_ne_self_of_re_ne_zero ha_re).2
  have hb : XiRiemann (-a) = 0 := XiRiemann_neg_zero ha
  have hbmin' : ∀ z : ℂ, XiRiemann z = 0 → z ≠ a → ‖-a‖ ≤ ‖z‖ := by
    intro z hz _
    rw [norm_neg]
    exact hamin' z hz
  have him : a.im = 0 ∧ (-a).im = 0 :=
    deux_plus_petits_zeros_reels_of_cercle_minimal
      a (-a) ha hb hba hamin' hbmin' hsym hre_ne hdeux_cercle
  refine ⟨a, -a, hba.symm, ha, hb, him.1, him.2, ?_, ?_⟩
  · rw [norm_neg]
  · intro z hz hza hzna
    exact hbmin' z hz hza





open ComplexConjugate XiEntiereRiemann


lemma XiRiemann_zero_in_strip (z : ℂ) (hz : XiRiemann z = 0) :
    |z.im| < 1 / 2 := by
  have hs : xiEntiere ((1 / 2 : ℂ) + Complex.I * z) = 0 := by
    simpa [XiRiemann, xiDecale] using hz
  have hre : 0 < ((1 / 2 : ℂ) + Complex.I * z).re ∧ ((1 / 2 : ℂ) + Complex.I * z).re < 1 :=
    xiEntiere_zero_in_strip hs
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re,
    Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub] at hre
  rw [abs_lt]
  constructor <;> linarith

lemma xiDecale_symm_conj' (w : ℂ) :
    xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w) := by
  unfold xiDecale
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  have h_arg : (1 / 2 : ℂ) + -(starRingEnd ℂ) w =
      1 - (starRingEnd ℂ) ((1 / 2 : ℂ) + w) := by
    simp only [map_add, map_div₀, map_one, h2]
    ring
  rw [h_arg, xiEntiere_one_sub, xiEntiere_conj]

lemma XiRiemann_ne_zero_at_half_I :
    XiRiemann (Complex.I / 2) ≠ 0 ∧ XiRiemann (-Complex.I / 2) ≠ 0 := by
  constructor
  · intro h
    have hs : xiEntiere ((1 / 2 : ℂ) + Complex.I * (Complex.I / 2)) = 0 := by
      simpa [XiRiemann, xiDecale] using h
    have h_arg : (1 / 2 : ℂ) + Complex.I * (Complex.I / 2) = 0 := by
      calc (1 / 2 : ℂ) + Complex.I * (Complex.I / 2)
        _ = (1 / 2 : ℂ) + (Complex.I * Complex.I) / 2 := by ring
        _ = 0 := by rw [Complex.I_mul_I]; ring
    rw [h_arg, xiEntiere_zero] at hs
    norm_num at hs
  · intro h
    have hs : xiEntiere ((1 / 2 : ℂ) + Complex.I * (-Complex.I / 2)) = 0 := by
      simpa [XiRiemann, xiDecale] using h
    have h_arg : (1 / 2 : ℂ) + Complex.I * (-Complex.I / 2) = 1 := by
      calc (1 / 2 : ℂ) + Complex.I * (-Complex.I / 2)
        _ = (1 / 2 : ℂ) - (Complex.I * Complex.I) / 2 := by ring
        _ = 1 := by rw [Complex.I_mul_I]; ring
    rw [h_arg, xiEntiere_one] at hs
    norm_num at hs

lemma eq_neg_conj_of_lam_eq_conj {z_k z_j : ℂ}
    (hlam : (-Complex.I) * z_k = (starRingEnd ℂ) ((-Complex.I) * z_j)) :
    z_k = -(starRingEnd ℂ) z_j := by
  have h1 : (starRingEnd ℂ) ((-Complex.I) * z_j) = Complex.I * (starRingEnd ℂ) z_j := by
    simp only [map_mul, map_neg, Complex.conj_I]
    ring
  rw [h1] at hlam
  have h2 : Complex.I * ((-Complex.I) * z_k) = Complex.I * (Complex.I * (starRingEnd ℂ) z_j) :=
    congrArg (Complex.I * ·) hlam
  calc z_k
    _ = -(Complex.I * Complex.I) * z_k := by rw [Complex.I_mul_I]; ring
    _ = Complex.I * ((-Complex.I) * z_k) := by ring
    _ = Complex.I * (Complex.I * (starRingEnd ℂ) z_j) := h2
    _ = (Complex.I * Complex.I) * (starRingEnd ℂ) z_j := by ring
    _ = -(starRingEnd ℂ) z_j := by rw [Complex.I_mul_I]; ring

lemma deux_plus_petits_zeros_reels_aux
    (a b : ℂ)
    (ha : XiRiemann a = 0) (hb : XiRiemann b = 0) (hba : b ≠ a)
    (hamin' : ∀ z : ℂ, XiRiemann z = 0 → ‖a‖ ≤ ‖z‖)
    (hbmin' : ∀ z : ℂ, XiRiemann z = 0 → z ≠ a → ‖b‖ ≤ ‖z‖)
    (h_schwarz : ∀ s : ℂ, xiEntiere ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xiEntiere s))
    (h_strip : ∀ z : ℂ, XiRiemann z = 0 → |z.im| < 1 / 2)
    (ha_norm : (1 / 2 : ℝ) ≤ ‖a‖)
    (h_au_plus_deux : ∀ z₁ z₂ z₃ : ℂ,
      XiRiemann z₁ = 0 → XiRiemann z₂ = 0 → XiRiemann z₃ = 0 →
      ‖z₁‖ = ‖a‖ → ‖z₂‖ = ‖a‖ → ‖z₃‖ = ‖a‖ →
      z₁ ≠ z₂ → z₃ = z₁ ∨ z₃ = z₂) :
    a.im = 0 ∧ b.im = 0 := by
  have hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w) :=
    xiDecale_symm_conj h_schwarz
  have hre_ne : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z.re ≠ 0 :=
    re_ne_zero_of_strip_and_norm_ge_half a h_strip ha_norm
  have hdeux_cercle : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z = a ∨ z = -a :=
    deux_cercle_of_au_plus_deux a ha hre_ne h_au_plus_deux
  exact deux_plus_petits_zeros_reels_of_cercle_minimal
    a b ha hb hba hamin' hbmin' hsym hre_ne hdeux_cercle



lemma zeta_zero_iff_xiEntiere_zero_of_in_strip (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannZeta s = 0 ↔ xiEntiere s = 0 := by
  have h0 : s ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hs0; exact lt_irrefl 0 hs0
  have h1 : s ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hs1; exact lt_irrefl 1 hs1
  have hs_sub : s - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hhalf : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  have hxi : xiEntiere s = (1 / 2 : ℂ) * s * (s - 1) * (Gammaℝ s * riemannZeta s) := by
    rw [← xi_eq_xiEntiere s h0 h1, xi_eq_of_re_pos s hs0]
  rw [hxi]
  constructor
  · intro hzeta
    rw [hzeta, mul_zero, mul_zero]
  · intro hprod
    rcases mul_eq_zero.mp hprod with hleft | hright
    · rcases mul_eq_zero.mp hleft with hleft2 | hsub
      · rcases mul_eq_zero.mp hleft2 with hh | hs_zero
        · exact absurd hh hhalf
        · exact absurd hs_zero h0
      · exact absurd hsub hs_sub
    · rcases mul_eq_zero.mp hright with hG | hzeta
      · exact absurd hG hGamma
      · exact hzeta

lemma XiRiemann_zero_re_ne_zero
    (h_zeta_real : ∀ x : ℝ, 0 < x → x < 1 → riemannZeta (x : ℂ) ≠ 0)
    (z : ℂ) (hz : XiRiemann z = 0) :
    z.re ≠ 0 := by
  intro hz_re
  set s : ℂ := (1 / 2 : ℂ) + Complex.I * z
  have hs_xi : xiEntiere s = 0 := by
    simpa [s, XiRiemann, xiDecale] using hz
  have hstrip : 0 < s.re ∧ s.re < 1 := xiEntiere_zero_in_strip hs_xi
  have hs_zeta : riemannZeta s = 0 :=
    (zeta_zero_iff_xiEntiere_zero_of_in_strip s hstrip.1 hstrip.2).mpr hs_xi
  have hs_im : s.im = 0 := by
    simp [s, hz_re]
  have hs_real : (s.re : ℂ) = s := by
    apply Complex.ext
    · simp
    · simp [hs_im]
  rw [← hs_real] at hs_zeta
  exact h_zeta_real s.re hstrip.1 hstrip.2 hs_zeta

open ObservableSelectionTheorem

lemma recherche_zeros_observable_entiere
    {K : ℕ} (az : Fin K → ℂ) (m : Fin K → ℕ)
    (hm : ∀ j, 0 < m j)
    (haz : Function.Injective az) :
    let ap : Fin 0 → ℂ := Fin.elim0
    let d : Fin 0 → ℕ := Fin.elim0
    let lam : Fin (K + 0) → ℂ := Sum.elim az ap ∘ finSumFinEquiv.symm
    let w : Fin (K + 0) → ℤ :=
      Sum.elim (fun j => (m j : ℤ)) (fun l => -(d l : ℤ)) ∘ finSumFinEquiv.symm
    IsUnit (hankel0 lam w).det ∧
    spectrum ℂ (operateurM lam w) = Set.range az ∧
    (∀ i, 0 < w i ↔ lam i ∈ Set.range az) := by
  intro ap d lam w
  have hd : ∀ l : Fin 0, 0 < d l := fun l => Fin.elim0 l
  have hdist : Function.Injective (Sum.elim az ap) := by
    intro x y hxy
    rcases x with x | x
    · rcases y with y | y
      · simp only [Sum.elim_inl] at hxy
        exact congrArg Sum.inl (haz hxy)
      · exact Fin.elim0 y
    · exact Fin.elim0 x
  obtain ⟨hunit, hspec, hw_pos⟩ := recherche_zeros_observable az ap m d hm hd hdist
  have hrange_ap : Set.range ap = ∅ := by
    ext x
    simp [ap]
  rw [hrange_ap, Set.union_empty] at hspec
  exact ⟨hunit, hspec, hw_pos⟩

lemma hdeux_cercle_of_spectre_minimal
    (a : ℂ) (ha_re : a.re ≠ 0)
    (m : Fin 2 → ℕ) (hm : ∀ j, 0 < m j)
    (h_cercle_in_spec : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ →
      let az : Fin 2 → ℂ := ![a, -a]
      let ap : Fin 0 → ℂ := Fin.elim0
      let d : Fin 0 → ℕ := Fin.elim0
      let lam : Fin (2 + 0) → ℂ := Sum.elim az ap ∘ finSumFinEquiv.symm
      let w : Fin (2 + 0) → ℤ :=
        Sum.elim (fun j => (m j : ℤ)) (fun l => -(d l : ℤ)) ∘ finSumFinEquiv.symm
      z ∈ spectrum ℂ (operateurM lam w)) :
    ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z = a ∨ z = -a := by
  let az : Fin 2 → ℂ := ![a, -a]
  have hne : a ≠ -a :=
    (conj_ne_neg_and_neg_ne_self_of_re_ne_zero ha_re).2.symm
  have haz : Function.Injective az := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · change a = -a at hij
      exact absurd hij hne
    · change -a = a at hij
      exact absurd hij.symm hne
    · rfl
  obtain ⟨_, hspec, _⟩ :=
    recherche_zeros_observable_entiere az m hm haz
  intro z hz hnorm
  have hz_spec := h_cercle_in_spec z hz hnorm
  dsimp only at hz_spec
  rw [hspec] at hz_spec
  rcases hz_spec with ⟨i, hi⟩
  fin_cases i
  · left
    simpa [az] using hi.symm
  · right
    simpa [az] using hi.symm

lemma GammaR_real_pos_of_pos (x : ℝ) (hx0 : 0 < x) :
    0 < (Complex.Gammaℝ (x : ℂ)).re ∧
    (Complex.Gammaℝ (x : ℂ)).im = 0 := by
  rw [Complex.Gammaℝ_def]
  have h_arg1 : -(x : ℂ) / 2 = ((-x / 2 : ℝ) : ℂ) := by push_cast; ring
  have h_arg2 : (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [h_arg1, h_arg2]
  have hpi : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
  rw [← Complex.ofReal_cpow hpi (-x / 2), Complex.Gamma_ofReal, ← Complex.ofReal_mul]
  constructor
  · rw [Complex.ofReal_re]
    exact mul_pos (Real.rpow_pos_of_pos Real.pi_pos (-x / 2))
      (Real.Gamma_pos_of_pos (by linarith))
  · exact Complex.ofReal_im _

lemma xiEntiere_real_re_eq (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (xiEntiere (x : ℂ)).re =
      (1 / 2 * x * (x - 1)) *
        (Complex.Gammaℝ (x : ℂ)).re * (riemannZeta (x : ℂ)).re := by
  have h0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx0)
  have h1 : (x : ℂ) ≠ 1 := by
    intro h
    have : x = 1 := by simpa using congrArg Complex.re h
    linarith
  have hre : 0 < ((x : ℂ)).re := by simpa using hx0
  rw [← xi_eq_xiEntiere (x : ℂ) h0 h1, xi_eq_of_re_pos (x : ℂ) hre]
  have hpoly : (1 / 2 : ℂ) * (x : ℂ) * ((x : ℂ) - 1) = ((1 / 2 * x * (x - 1) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hpoly]
  have hG_im : (Complex.Gammaℝ (x : ℂ)).im = 0 :=
    (GammaR_real_pos_of_pos x hx0).2
  have hG_real : Complex.Gammaℝ (x : ℂ) =
    (((Complex.Gammaℝ (x : ℂ)).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [hG_im]
  rw [hG_real]
  rw [← mul_assoc]
  rw [← Complex.ofReal_mul]
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]


theorem xiRiemann_eq_cos_integral (t : ℝ) :
    ∃ Phi : ℝ → ℝ, (∀ u ≥ 0, 0 < Phi u) ∧
      XiRiemann (t : ℂ) = 2 *
      ∫ u in Set.Ioi (0 : ℝ),
        (Phi u : ℂ) * (Real.cos (t * u) : ℂ) := by
  obtain ⟨Phi, hPhi_pos, _, hPhi_int⟩ := exists_riemann_kernel
  refine ⟨Phi, hPhi_pos, ?_⟩
  have h1 := hPhi_int (Complex.I * (t : ℂ))
  have h2 : (∫ u in Set.Ioi (0 : ℝ),
      (Phi u : ℂ) * Complex.cosh (Complex.I * (t : ℂ) * (u : ℂ))) =
      ∫ u in Set.Ioi (0 : ℝ),
      (Phi u : ℂ) * (Real.cos (t * u) : ℂ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    congr 1
    have h_arg : Complex.I * (t : ℂ) * (u : ℂ) = ↑(t * u) * Complex.I := by
      push_cast; ring
    rw [h_arg, Complex.cosh_mul_I, Complex.ofReal_cos]
  unfold XiRiemann
  rw [h1, h2]


theorem xiRiemann_eq_complex_cos_integral (z : ℂ) :
    ∃ Phi : ℝ → ℝ, (∀ u ≥ 0, 0 < Phi u) ∧
      (∀ σ : ℝ, MeasureTheory.IntegrableOn
        (fun u : ℝ => Phi u * Real.cosh (σ * u)) (Set.Ioi (0 : ℝ))) ∧
      XiRiemann z = 2 *
      ∫ u in Set.Ioi (0 : ℝ),
        (Phi u : ℂ) * Complex.cos (z * (u : ℂ)) := by
  obtain ⟨Phi, hPhi_pos, hPhi_integrable, hPhi_int⟩ := exists_riemann_kernel
  refine ⟨Phi, hPhi_pos, hPhi_integrable, ?_⟩
  have h1 := hPhi_int (Complex.I * z)
  have h2 : (∫ u in Set.Ioi (0 : ℝ),
      (Phi u : ℂ) * Complex.cosh (Complex.I * z * (u : ℂ))) =
      ∫ u in Set.Ioi (0 : ℝ),
      (Phi u : ℂ) * Complex.cos (z * (u : ℂ)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    congr 1
    have h_arg : Complex.I * z * (u : ℂ) = (z * (u : ℂ)) * Complex.I := by ring
    rw [h_arg, Complex.cosh_mul_I]
  unfold XiRiemann
  rw [h1, h2]


lemma xiEntiere_real_pos_of_mem_Ioo
  (x : ℝ) (_ : 0 < x) (_ : x < 1) :
    0 < (xiEntiere (x : ℂ)).re := by
  let σ : ℝ := x - 1 / 2
  let z : ℂ := -Complex.I * (σ : ℂ)
  have h_eq_xi : xiEntiere (x : ℂ) = XiRiemann z := by
    rw [XiRiemann_eq]
    congr 1
    dsimp [z, σ]
    push_cast
    calc (x : ℂ)
      _ = 1 / 2 + (x - 1 / 2) := by ring
      _ = 1 / 2 - Complex.I ^ 2 * ((x : ℂ) - 1 / 2) := by
          rw [Complex.I_sq]; ring
      _ = 1 / 2 + Complex.I *
        (-Complex.I * ((x : ℂ) - 1 / 2)) := by ring
  obtain ⟨Phi, hPhi_pos, hPhi_integrable, hXi_cos⟩ := xiRiemann_eq_complex_cos_integral z
  have h_int_cosh :
      (∫ u in Set.Ioi (0 : ℝ), (Phi u : ℂ) * Complex.cos (z * (u : ℂ))) =
      ∫ u in Set.Ioi (0 : ℝ), ((Phi u * Real.cosh (σ * u) : ℝ) : ℂ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    have h_cos_eq_cosh : Complex.cos (z * (u : ℂ)) = (Real.cosh (σ * u) : ℂ) := by
      have h_arg : z * (u : ℂ) = -(((σ * u : ℝ) : ℂ) * Complex.I) := by
        dsimp [z]
        push_cast
        ring
      rw [h_arg, Complex.cos_neg, Complex.cos_mul_I, Complex.ofReal_cosh]
    rw [h_cos_eq_cosh, Complex.ofReal_mul]
  have h_re_eq : (xiEntiere (x : ℂ)).re =
      2 * ∫ u in Set.Ioi (0 : ℝ), Phi u * Real.cosh (σ * u) := by
    have h_ofReal : (∫ u in Set.Ioi (0 : ℝ), ((Phi u * Real.cosh (σ * u) : ℝ) : ℂ)) =
        ((∫ u in Set.Ioi (0 : ℝ), Phi u * Real.cosh (σ * u) : ℝ) : ℂ) :=
      integral_ofReal
    rw [h_eq_xi, hXi_cos, h_int_cosh, h_ofReal]
    have h_two : (2 : ℂ) = ((2 : ℝ) : ℂ) := rfl
    rw [h_two, ← Complex.ofReal_mul, Complex.ofReal_re]
  have h_cosh_pos : ∀ u : ℝ, 0 < Real.cosh (σ * u) := by
    intro u
    rw [Real.cosh_eq]
    have h_exp1 : 0 < Real.exp (σ * u) := Real.exp_pos (σ * u)
    have h_exp2 : 0 < Real.exp (-(σ * u)) := Real.exp_pos (-(σ * u))
    linarith
  have h_integrand_pos : ∀ u : ℝ, u ∈ Set.Ioi (0 : ℝ) →
      0 < Phi u * Real.cosh (σ * u) := by
    intro u hu
    have hu_nonneg : u ≥ 0 := le_of_lt hu
    exact mul_pos (hPhi_pos u hu_nonneg) (h_cosh_pos u)
  rw [h_re_eq]
  have h_int_pos : 0 < ∫ u in Set.Ioi (0 : ℝ), Phi u * Real.cosh (σ * u) := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae]
    · have h_supp : Function.support (fun u : ℝ => Phi u * Real.cosh (σ * u)) ∩ Set.Ioi (0 : ℝ) =
          Set.Ioi (0 : ℝ) := by
        ext u
        simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi, and_iff_right_iff_imp]
        intro hu
        exact ne_of_gt (h_integrand_pos u hu)
      rw [h_supp, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      exact le_of_lt (h_integrand_pos u hu)
    · exact hPhi_integrable σ
  linarith

lemma riemannZeta_real_neg_of_mem_Ioo (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    (riemannZeta (x : ℂ)).re < 0 := by
  have hxi_pos : 0 < (xiEntiere (x : ℂ)).re := xiEntiere_real_pos_of_mem_Ioo x hx0 hx1
  rw [xiEntiere_real_re_eq x hx0 hx1] at hxi_pos
  have hG_pos : 0 < (Complex.Gammaℝ (x : ℂ)).re := (GammaR_real_pos_of_pos x hx0).1
  have hpoly_neg : 1 / 2 * x * (x - 1) < 0 := by
    have hx_sub : x - 1 < 0 := sub_neg.mpr hx1
    have hx_half : 0 < 1 / 2 * x := by linarith
    exact mul_neg_of_pos_of_neg hx_half hx_sub
  have hprod_neg : (1 / 2 * x * (x - 1)) * (Complex.Gammaℝ (x : ℂ)).re < 0 :=
    mul_neg_of_neg_of_pos hpoly_neg hG_pos
  by_contra h_nonneg
  push Not at h_nonneg
  have h_le_zero :
      (1 / 2 * x * (x - 1)) * (Complex.Gammaℝ (x : ℂ)).re * (riemannZeta (x : ℂ)).re ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt hprod_neg) h_nonneg
  linarith


lemma riemannZeta_ne_zero_of_mem_Ioo_real
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    riemannZeta (x : ℂ) ≠ 0 := by
  intro h
  have hneg := riemannZeta_real_neg_of_mem_Ioo x hx0 hx1
  rw [h, Complex.zero_re] at hneg
  exact lt_irrefl 0 hneg

lemma enumeration_spectrale_par_choix
    (a : ℂ)
    (h_fin : {w : ℂ | XiRiemann w = 0 ∧ ‖w‖ = ‖a‖}.Finite) :
    ∃ (K : ℕ) (az : Fin K → ℂ),
      Function.Injective az ∧
      (∀ z : ℂ, (XiRiemann z = 0 ∧ ‖z‖ = ‖a‖) ↔ z ∈ Set.range az) ∧
      (∀ (m : Fin K → ℕ) (_ : ∀ j, 0 < m j),
        let ap : Fin 0 → ℂ := Fin.elim0
        let d : Fin 0 → ℕ := Fin.elim0
        let lam : Fin (K + 0) → ℂ := Sum.elim az ap ∘ finSumFinEquiv.symm
        let w : Fin (K + 0) → ℤ :=
          Sum.elim (fun j => (m j : ℤ)) (fun l => -(d l : ℤ)) ∘ finSumFinEquiv.symm
        ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ →
          z ∈ spectrum ℂ (operateurM lam w)) := by
  let S : Set ℂ := {w : ℂ | XiRiemann w = 0 ∧ ‖w‖ = ‖a‖}
  have _ : Finite S := h_fin
  obtain ⟨K, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  let az : Fin K → ℂ := fun j => (e.symm j).val
  have haz_inj : Function.Injective az :=
    Subtype.val_injective.comp e.symm.injective
  have h_range : Set.range az = S := by
    ext z
    simp only [Set.mem_range, az]
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).property
    · intro hz
      refine ⟨e ⟨z, hz⟩, ?_⟩
      simp
  refine ⟨K, az, haz_inj, ?_, ?_⟩
  · intro z
    rw [h_range]
    rfl
  · intro m hm ap d lam w z hz hnorm
    obtain ⟨_, hspec, _⟩ := recherche_zeros_observable_entiere az m hm haz_inj
    dsimp only [lam, w, ap, d]
    rw [hspec, h_range]
    exact ⟨hz, hnorm⟩

lemma XiRiemann_zero_ne_zero : XiRiemann 0 ≠ 0 := by
  intro h0
  have h_pos : 0 < (xiEntiere ((1 / 2 : ℝ) : ℂ)).re :=
    xiEntiere_real_pos_of_mem_Ioo (1 / 2) (by norm_num) (by norm_num)
  have h_eq : XiRiemann 0 = xiEntiere ((1 / 2 : ℝ) : ℂ) := by
    rw [XiRiemann_eq]
    congr 1
    push_cast
    ring
  rw [← h_eq, h0, Complex.zero_re] at h_pos
  exact lt_irrefl 0 h_pos


lemma selection_spectrale_cercle_minimal_choix
    (a : ℂ) (h_fin : {w : ℂ | XiRiemann w = 0 ∧ ‖w‖ = ‖a‖}.Finite) :
    ∃ (K : ℕ) (az : Fin K → ℂ),
      Function.Injective az ∧
      (let ap : Fin 0 → ℂ := Fin.elim0
       let d : Fin 0 → ℕ := Fin.elim0
       let lam : Fin (K + 0) → ℂ := Sum.elim az ap ∘ finSumFinEquiv.symm
       let w : Fin (K + 0) → ℤ :=
         Sum.elim (fun j => ((fun _ => 1 : Fin K → ℕ) j : ℤ)) (fun l => -(d l : ℤ)) ∘
         finSumFinEquiv.symm
       ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ →
         z ∈ spectrum ℂ (operateurM lam w)) := by
  let S : Set ℂ := {w : ℂ | XiRiemann w = 0 ∧ ‖w‖ = ‖a‖}
  have _ : Finite S := h_fin
  obtain ⟨K, ⟨e⟩⟩ := Finite.exists_equiv_fin S
  let az : Fin K → ℂ := fun j => (e.symm j).val
  have haz_inj : Function.Injective az :=
    Subtype.val_injective.comp e.symm.injective
  have h_range : Set.range az = S := by
    ext z
    simp only [Set.mem_range, az]
    constructor
    · rintro ⟨j, rfl⟩
      exact (e.symm j).property
    · intro hz
      refine ⟨e ⟨z, hz⟩, ?_⟩
      simp
  refine ⟨K, az, haz_inj, ?_⟩
  intro ap d lam w z hz hnorm
  have hm : ∀ j : Fin K, 0 < (fun _ : Fin K => 1 : Fin K → ℕ) j :=
    fun _ => Nat.zero_lt_one
  obtain ⟨_, hspec, _⟩ := recherche_zeros_observable_entiere az (fun _ => 1) hm haz_inj
  dsimp only [lam, w, ap, d]
  rw [hspec, h_range]
  exact ⟨hz, hnorm⟩

lemma mem_range_pair (a b z : ℂ) :
    z ∈ Set.range (![a, b] : Fin 2 → ℂ) ↔ z = a ∨ z = b := by
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · left; rfl
    · right; rfl
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

lemma complex_eq_ofReal_of_im_eq_zero (w : ℂ) (hw : w.im = 0) :
    w = (w.re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [hw]

lemma norm_eq_abs_re_of_im_eq_zero (w : ℂ) (hw : w.im = 0) :
    ‖w‖ = |w.re| := by
  rw [complex_eq_ofReal_of_im_eq_zero w hw]
  simp

lemma eq_or_neg_of_real_and_norm_eq (z a : ℂ)
    (hz : z.im = 0) (ha : a.im = 0) (hnorm : ‖z‖ = ‖a‖) :
    z = a ∨ z = -a := by
  have hz_norm : ‖z‖ = |z.re| := norm_eq_abs_re_of_im_eq_zero z hz
  have ha_norm : ‖a‖ = |a.re| := norm_eq_abs_re_of_im_eq_zero a ha
  have h_abs : |z.re| = |a.re| := by linarith [hz_norm, ha_norm, hnorm]
  rcases abs_eq_abs.mp h_abs with heq | hneg
  · left
    apply Complex.ext
    · exact heq
    · simp [hz, ha]
  · right
    apply Complex.ext
    · simp [hneg]
    · simp [hz, ha]

lemma ne_neg_conj_of_re_ne_zero {a : ℂ} (ha_re : a.re ≠ 0) :
    a ≠ -(starRingEnd ℂ) a ∧ -(starRingEnd ℂ) a ≠ a ∧ -a ≠ (starRingEnd ℂ) a := by
  have h1 : a ≠ -(starRingEnd ℂ) a := by
    intro h
    have hre : a.re = (-(starRingEnd ℂ) a).re := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at hre
    have : a.re = 0 := by linarith
    exact ha_re this
  have h2 : -(starRingEnd ℂ) a ≠ a := fun h => h1 h.symm
  have h3 : -a ≠ (starRingEnd ℂ) a := by
    intro h
    have hre : (-a).re = ((starRingEnd ℂ) a).re := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.conj_re] at hre
    have : a.re = 0 := by linarith
    exact ha_re this
  exact ⟨h1, h2, h3⟩

lemma injective_quatre_points_of_conj_ne
    {a : ℂ} (ha_re : a.re ≠ 0) (hconj_ne : (starRingEnd ℂ) a ≠ a) :
    Function.Injective (![a, -a, (starRingEnd ℂ) a, -(starRingEnd ℂ) a] : Fin 4 → ℂ) := by
  obtain ⟨hconj_ne_neg, hneg_ne_self⟩ := conj_ne_neg_and_neg_ne_self_of_re_ne_zero ha_re
  obtain ⟨ha_ne_neg_conj, hneg_conj_ne_a, hneg_a_ne_conj⟩ := ne_neg_conj_of_re_ne_zero ha_re
  have hconj_re : ((starRingEnd ℂ) a).re ≠ 0 := by simpa using ha_re
  obtain ⟨_, hneg_conj_ne_conj⟩ := conj_ne_neg_and_neg_ne_self_of_re_ne_zero hconj_re
  have hneg_a_ne_neg_conj : -a ≠ -(starRingEnd ℂ) a := by
    intro h
    have : a = (starRingEnd ℂ) a := neg_inj.mp h
    exact hconj_ne this.symm
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij hneg_ne_self.symm
  · exact absurd hij.symm hconj_ne
  · exact absurd hij ha_ne_neg_conj
  · exact absurd hij hneg_ne_self
  · rfl
  · exact absurd hij hneg_a_ne_conj
  · exact absurd hij hneg_a_ne_neg_conj
  · exact absurd hij hconj_ne
  · exact absurd hij hconj_ne_neg
  · rfl
  · exact absurd hij hneg_conj_ne_conj.symm
  · exact absurd hij hneg_conj_ne_a
  · exact absurd hij.symm hneg_a_ne_neg_conj
  · exact absurd hij hneg_conj_ne_conj
  · rfl



lemma superposition_quatre_zeros_implique_reel
    (a : ℂ) (ha_re : a.re ≠ 0)
    (h_non_inj : ¬ Function.Injective
    (![a, -a, (starRingEnd ℂ) a, -(starRingEnd ℂ) a] : Fin 4 → ℂ)) :
    (starRingEnd ℂ) a = a ∧ a.im = 0 := by
  have hconj_eq_a : (starRingEnd ℂ) a = a := by
    by_contra hconj_ne_a
    have hinj := injective_quatre_points_of_conj_ne ha_re hconj_ne_a
    exact h_non_inj hinj
  refine ⟨hconj_eq_a, ?_⟩
  have him := congrArg Complex.im hconj_eq_a
  simp only [Complex.conj_im] at him
  linarith

lemma couplage_par_exclusion_cadre_spectral_bis
    {K : ℕ} (zs : Fin K → ℂ)
    (hzs_inj : Function.Injective zs)
    (hsym : ∀ j, ∃ k, zs k = -(starRingEnd ℂ) (zs j)) :
    let lam : Fin K → ℂ := fun j => (-Complex.I) * zs j
    let w : Fin K → ℤ := fun _ => (1 : ℤ)
    spectrum ℂ (operateurM lam w) = Set.range lam ∧
    (∀ μ ∈ spectrum ℂ (operateurM lam w),
        (starRingEnd ℂ) μ ∈ spectrum ℂ (operateurM lam w)) ∧
    (∀ j, (zs j).re ≠ 0 →
        ∃ k, k ≠ j ∧ zs k = -(starRingEnd ℂ) (zs j)) := by
  intro lam w
  let m : Fin K → ℕ := fun _ => 1
  have hm : ∀ j : Fin K, 0 < m j := fun _ => Nat.zero_lt_one
  have hinj : Function.Injective (fun j => (-Complex.I) * zs j) := by
    intro i j hij
    have h_neg_I_ne : (-Complex.I : ℂ) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    exact hzs_inj (mul_left_cancel₀ h_neg_I_ne hij)
  obtain ⟨_, hspec, hspec_conj, hpair⟩ :=
    exclusion_cadre_spectral_bis zs m hm hinj hsym
  refine ⟨hspec, hspec_conj, ?_⟩
  intro j hj_re
  obtain ⟨k, hkj, hlam_eq⟩ := hpair j hj_re
  refine ⟨k, hkj, ?_⟩
  have h_conj_lam : (starRingEnd ℂ) ((-Complex.I) * zs j) =
      (-Complex.I) * (-(starRingEnd ℂ) (zs j)) := by
    simp only [map_mul, map_neg, Complex.conj_I]
    ring
  dsimp only [lam] at hlam_eq
  rw [h_conj_lam] at hlam_eq
  have h_neg_I_ne : (-Complex.I : ℂ) ≠ 0 :=
    neg_ne_zero.mpr Complex.I_ne_zero
  exact mul_left_cancel₀ h_neg_I_ne hlam_eq

lemma eq_neg_of_quatre_zeros_et_superposition
    (a w : ℂ) (ha_re : a.re ≠ 0) (hwa : w ≠ a)
    (h_quatre_cas : w = a ∨ w = -a ∨ w = (starRingEnd ℂ) a ∨ w = -(starRingEnd ℂ) a)
    (h_superposition : ¬ Function.Injective
    (![a, -a, (starRingEnd ℂ) a, -(starRingEnd ℂ) a] : Fin 4 → ℂ)) :
    w = -a := by
  have hconj_eq_a : (starRingEnd ℂ) a = a :=
    (superposition_quatre_zeros_implique_reel a ha_re h_superposition).1
  rcases h_quatre_cas with rfl | rfl | rfl | rfl
  · exact absurd rfl hwa
  · rfl
  · exact absurd hconj_eq_a hwa
  · rw [hconj_eq_a]



lemma conj_eq_self_of_exclusion
    (a : ℂ) (ha_re : a.re ≠ 0)
    (h_sym_cercle : (starRingEnd ℂ) a = a ∨ (starRingEnd ℂ) a = -a) :
    (starRingEnd ℂ) a = a := by
  obtain ⟨hconj_ne_neg, _⟩ := conj_ne_neg_and_neg_ne_self_of_re_ne_zero ha_re
  rcases h_sym_cercle with h_eq | h_neg
  · exact h_eq
  · exact absurd h_neg hconj_ne_neg

lemma non_injective_quatre_points
    (a : ℂ) (_ : a.re ≠ 0) (ha_im : a.im = 0) :
    ¬ Function.Injective
    (![a, -a, (starRingEnd ℂ) a, -(starRingEnd ℂ) a] : Fin 4 → ℂ) := by
  intro hinj
  have hconj : (starRingEnd ℂ) a = a := by
    apply Complex.ext
    · simp
    · simp [ha_im]
  have h02 :
  (![a, -a, (starRingEnd ℂ) a, -(starRingEnd ℂ) a] : Fin 4 → ℂ) 0 =
  (![a, -a, (starRingEnd ℂ) a, -(starRingEnd ℂ) a] : Fin 4 → ℂ) 2 := by
    simp [hconj]
  have : (0 : Fin 4) = 2 := hinj h02
  revert this
  decide

lemma eval_lam_zs_conj_pair (a : ℂ) :
    let zs : Fin 2 → ℂ := ![Complex.I * a, -(starRingEnd ℂ) (Complex.I * a)]
    (-Complex.I) * zs 0 = a ∧
    (-Complex.I) * zs 1 = (starRingEnd ℂ) a := by
  intro zs
  have h0 : (-Complex.I) * zs 0 = a := by
    change (-Complex.I) * (Complex.I * a) = a
    calc (-Complex.I) * (Complex.I * a)
      _ = -(Complex.I * Complex.I) * a := by ring
      _ = -(-1 : ℂ) * a := by rw [Complex.I_mul_I]
      _ = a := by ring
  have h1 : (-Complex.I) * zs 1 = (starRingEnd ℂ) a := by
    change (-Complex.I) * (-(starRingEnd ℂ) (Complex.I * a)) = (starRingEnd ℂ) a
    simp only [map_mul, Complex.conj_I]
    calc (-Complex.I) * -(-Complex.I * (starRingEnd ℂ) a)
      _ = -(Complex.I * Complex.I) * (starRingEnd ℂ) a := by ring
      _ = -(-1 : ℂ) * (starRingEnd ℂ) a := by rw [Complex.I_mul_I]
      _ = (starRingEnd ℂ) a := by ring
  exact ⟨h0, h1⟩

lemma lam_zs_zero (a : ℂ) :
    (-Complex.I) * (![Complex.I * a, -(starRingEnd ℂ)
    (Complex.I * a)] : Fin 2 → ℂ) 0 = a := by
  have : (![Complex.I * a, -(starRingEnd ℂ) (Complex.I * a)] : Fin 2 → ℂ) 0 = Complex.I * a := rfl
  rw [this]
  calc (-Complex.I) * (Complex.I * a)
    _ = -(Complex.I * Complex.I) * a := by ring
    _ = -(-1 : ℂ) * a := by rw [Complex.I_mul_I]
    _ = a := by ring

lemma lam_zs_one (a : ℂ) :
    (-Complex.I) * (![Complex.I * a, -(starRingEnd ℂ)
    (Complex.I * a)] : Fin 2 → ℂ) 1 = (starRingEnd ℂ) a := by
  have : (![Complex.I * a, -(starRingEnd ℂ) (Complex.I * a)] : Fin 2 → ℂ) 1 =
      -(starRingEnd ℂ) (Complex.I * a) := rfl
  rw [this]
  simp only [map_mul, Complex.conj_I]
  calc (-Complex.I) * -(-Complex.I * (starRingEnd ℂ) a)
    _ = -(Complex.I * Complex.I) * (starRingEnd ℂ) a := by ring
    _ = -(-1 : ℂ) * (starRingEnd ℂ) a := by rw [Complex.I_mul_I]
    _ = (starRingEnd ℂ) a := by ring

lemma lam_zs_val_zero (a : ℂ) :
    (-Complex.I) * (![Complex.I * a, -(starRingEnd ℂ) (Complex.I * a)] : Fin 2 → ℂ) 0 = a := by
  simp only [Matrix.cons_val_zero]
  calc (-Complex.I) * (Complex.I * a)
    _ = -(Complex.I * Complex.I) * a := by ring
    _ = -(-1 : ℂ) * a := by rw [Complex.I_mul_I]
    _ = a := by ring

lemma lam_zs_val_one (a : ℂ) :
    (-Complex.I) *
    (![Complex.I * a, -(starRingEnd ℂ) (Complex.I * a)] :
    Fin 2 → ℂ) 1 = (starRingEnd ℂ) a := by
  simp only [Matrix.cons_val_one, map_mul, Complex.conj_I]
  calc (-Complex.I) * -(-Complex.I * (starRingEnd ℂ) a)
    _ = -(Complex.I * Complex.I) * (starRingEnd ℂ) a := by ring
    _ = -(-1 : ℂ) * (starRingEnd ℂ) a := by rw [Complex.I_mul_I]
    _ = (starRingEnd ℂ) a := by ring

open SpecInversion
lemma mem_spectre_operateurM_of_ensembleSolutions
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y : ℂ)
    (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam) (hw : ∀ r : Fin K, w r ≠ 0)
    (_ : ∀ k : ℕ,
      momentsParametres C γΩ g y k =
        ∑ r : Fin K, (w r : ℂ) * (lam r) ^ k)
    (hsol : Set.range lam = ensembleSolutions C.f C.Ω (g y))
    (z : ℂ) (hz : z ∈ ensembleSolutions C.f C.Ω (g y)) :
    z ∈ spectrum ℂ (operateurM lam w) := by
  rw [ObservableSelectionTheorem.spectre_operateurM lam w hlam hw]
  rw [hsol]
  exact hz


lemma inj_lam_zs_of_conj_ne (a : ℂ) (hconj_ne : (starRingEnd ℂ) a ≠ a) :
    Function.Injective (fun j : Fin 2 =>
      (-Complex.I) *
      (![Complex.I * a, -(starRingEnd ℂ) (Complex.I * a)] : Fin 2 → ℂ) j) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · dsimp only at hij
    have h_eval : a = (starRingEnd ℂ) a := by
      revert hij
      simp only [map_mul, Complex.conj_I]
      intro h
      calc a
        _ = -(-1 : ℂ) * a := by ring
        _ = -(Complex.I * Complex.I) * a := by rw [Complex.I_mul_I]
        _ = (-Complex.I) * (Complex.I * a) := by ring
        _ = (-Complex.I) * -(-Complex.I * (starRingEnd ℂ) a) := h
        _ = -(Complex.I * Complex.I) * (starRingEnd ℂ) a := by ring
        _ = -(-1 : ℂ) * (starRingEnd ℂ) a := by rw [Complex.I_mul_I]
        _ = (starRingEnd ℂ) a := by ring
    exact absurd h_eval.symm hconj_ne
  · dsimp only at hij
    have h_eval : (starRingEnd ℂ) a = a := by
      revert hij
      simp only [map_mul, Complex.conj_I]
      intro h
      calc (starRingEnd ℂ) a
        _ = -(-1 : ℂ) * (starRingEnd ℂ) a := by ring
        _ = -(Complex.I * Complex.I) * (starRingEnd ℂ) a := by rw [Complex.I_mul_I]
        _ = (-Complex.I) * -(-Complex.I * (starRingEnd ℂ) a) := by ring
        _ = (-Complex.I) * (Complex.I * a) := h
        _ = -(Complex.I * Complex.I) * a := by ring
        _ = -(-1 : ℂ) * a := by rw [Complex.I_mul_I]
        _ = a := by ring
    exact absurd h_eval hconj_ne
  · rfl


lemma conj_eq_self_of_couplage_neg
    (a : ℂ) (ha_re : a.re ≠ 0)
    (h_couplage : (starRingEnd ℂ) a = -a) :
    (starRingEnd ℂ) a = a := by
  exfalso
  have hre : ((starRingEnd ℂ) a).re = (-a).re := congrArg Complex.re h_couplage
  simp only [Complex.conj_re, Complex.neg_re] at hre
  have ha_re_zero : a.re = 0 := by linarith
  exact ha_re ha_re_zero

lemma fermeture_spectrale_conj_eq_self
    (a : ℂ) (ha : XiRiemann a = 0)
    (_ : ∀ w : ℂ, XiRiemann w = 0 → ‖a‖ ≤ ‖w‖)
    (ha_re : a.re ≠ 0)
    (_ : XiRiemann ((starRingEnd ℂ) a) = 0)
    (_ : ‖(starRingEnd ℂ) a‖ = ‖a‖)
    (hpaliers : PaliersStrictsXiRiemann) :
    (starRingEnd ℂ) a = a := by
  obtain ⟨hconj_ne_neg, h_neg_ne_a⟩ := conj_ne_neg_and_neg_ne_self_of_re_ne_zero ha_re
  have h_neg_a : XiRiemann (-a) = 0 := XiRiemann_neg_zero ha
  have h_norm_eq : ‖a‖ = ‖-a‖ := (norm_neg a).symm
  have h_couplage : (starRingEnd ℂ) a = -a :=
    (hpaliers a (-a) ha h_neg_a h_neg_ne_a.symm h_norm_eq).symm
  exact conj_eq_self_of_couplage_neg a ha_re h_couplage


lemma zero_minimal_a_im_zero
    (a : ℂ) (ha : XiRiemann a = 0)
    (hamin' : ∀ w : ℂ, XiRiemann w = 0 → ‖a‖ ≤ ‖w‖)
    (ha_re : a.re ≠ 0)
    (hpaliers : PaliersStrictsXiRiemann) :
    a.im = 0 := by
  have hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w) :=
    xiDecale_symm_conj'
  have hconj_a : XiRiemann ((starRingEnd ℂ) a) = 0 := XiRiemann_conj_zero hsym ha
  have hconj_norm : ‖(starRingEnd ℂ) a‖ = ‖a‖ := Complex.norm_conj a
  have hconj_self : (starRingEnd ℂ) a = a :=
    fermeture_spectrale_conj_eq_self
      a ha hamin' ha_re hconj_a hconj_norm hpaliers
  have him := congrArg Complex.im hconj_self
  simp only [Complex.conj_im] at him
  linarith


lemma zeros_cercle_minimal_eq_or_neg
    (a : ℂ) (ha : XiRiemann a = 0)
    (hamin' : ∀ w : ℂ, XiRiemann w = 0 → ‖a‖ ≤ ‖w‖)
    (z : ℂ) (hz : XiRiemann z = 0) (hnorm : ‖z‖ = ‖a‖)
    (hz_re : z.re ≠ 0)
    (hpaliers : PaliersStrictsXiRiemann) :
    z = a ∨ z = -a := by
  have ha_re : a.re ≠ 0 :=
    XiRiemann_zero_re_ne_zero riemannZeta_ne_zero_of_mem_Ioo_real a ha
  have ha_im : a.im = 0 :=
    zero_minimal_a_im_zero a ha hamin' ha_re hpaliers
  have hzmin : ∀ w : ℂ, XiRiemann w = 0 → ‖z‖ ≤ ‖w‖ := by
    intro w hw
    have h : ‖a‖ ≤ ‖w‖ := hamin' w hw
    rwa [← hnorm] at h
  have hz_im : z.im = 0 :=
    zero_minimal_a_im_zero z hz hzmin hz_re hpaliers
  exact eq_or_neg_of_real_and_norm_eq z a hz_im ha_im hnorm


theorem xi_riemann_nonzero_on_imaginary_axis (z : ℂ) (hzre : z.re = 0) :
    XiRiemann z ≠ 0 := by
  intro hz
  exact XiRiemann_zero_re_ne_zero
    riemannZeta_ne_zero_of_mem_Ioo_real z hz hzre

lemma selection_spectrale_cercle_minimal
    (a : ℂ) (ha : XiRiemann a = 0)
    (hamin' : ∀ w : ℂ, XiRiemann w = 0 → ‖a‖ ≤ ‖w‖)
    (ha_re : a.re ≠ 0)
    (z : ℂ) (hz : XiRiemann z = 0) (hnorm : ‖z‖ = ‖a‖)
    (hpaliers : PaliersStrictsXiRiemann) :
    let az : Fin 2 → ℂ := ![a, -a]
    let ap : Fin 0 → ℂ := Fin.elim0
    let d : Fin 0 → ℕ := Fin.elim0
    let lam : Fin (2 + 0) → ℂ := Sum.elim az ap ∘ finSumFinEquiv.symm
    let w : Fin (2 + 0) → ℤ :=
      Sum.elim (fun j =>
      ((![1, 1] : Fin 2 → ℕ) j : ℤ)) (fun l => -(d l : ℤ)) ∘
      finSumFinEquiv.symm
    z ∈ spectrum ℂ (operateurM lam w) := by
  intro az ap d lam w
  have hne : a ≠ -a :=
    (conj_ne_neg_and_neg_ne_self_of_re_ne_zero ha_re).2.symm
  have haz : Function.Injective az := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · change a = -a at hij; exact absurd hij hne
    · change -a = a at hij; exact absurd hij.symm hne
    · rfl
  have hm : ∀ j : Fin 2, 0 < (![1, 1] : Fin 2 → ℕ) j := by
    intro j
    fin_cases j <;> decide
  obtain ⟨_, hspec, _⟩ :=
    recherche_zeros_observable_entiere az ![1, 1] hm haz
  dsimp only [lam, w, ap, d]
  rw [hspec]
  rw [mem_range_pair]
  have hz_re : z.re ≠ 0 := by
    intro hzre
    exact absurd hz (xi_riemann_nonzero_on_imaginary_axis z hzre)
  exact zeros_cercle_minimal_eq_or_neg a ha hamin' z hz hnorm hz_re hpaliers



end ZeroMin2
