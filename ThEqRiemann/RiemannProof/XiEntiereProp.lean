import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.GammaProp

/-! -/
namespace XiEntiereRiemann

open Set Complex RiemannDef GammaRiemann

lemma xiEntiere_zero : xiEntiere 0 = 1 / 2 := by
  unfold xiEntiere
  simp

lemma xiEntiere_not_identically_zero : ∃ s : ℂ, xiEntiere s ≠ 0 := by
  refine ⟨0, ?_⟩
  rw [xiEntiere_zero]
  norm_num

lemma GLambda_differentiable : Differentiable ℂ GLambda := by
  unfold GLambda
  exact xiEntiere_differentiable.comp
    ((differentiable_const _).add
    ((differentiable_const _).mul differentiable_id))

lemma GLambda_at : GLambda (Complex.I / 2) = 1 / 2 := by
  unfold GLambda
  have : (1 / 2 : ℂ) + Complex.I * (Complex.I / 2) = 0 := by
    ring_nf
    simp [Complex.I_sq]
  rw [this, xiEntiere_zero]


lemma xiEntiere_conj (s : ℂ) :
    xiEntiere ((starRingEnd ℂ) s) = (starRingEnd ℂ) (xiEntiere s) := by
  unfold xiEntiere
  rw [completedRiemannZeta₀_conj']
  simp [map_add, map_mul, map_sub, map_one, map_ofNat]

-------------------------------------------------------------------

lemma zeta_zero_iff_xiEntiere_zero (s : ℂ) (hs : s.re = 1 / 2) :
    riemannZeta s = 0 ↔ xiEntiere s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hG : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  rw [← xi_eq_xiEntiere s hs0 hs1, xi_eq_of_ne s hs0 hs1,
      riemannZeta_def_of_ne_zero hs0]
  constructor
  · intro h
    have : completedRiemannZeta s = 0 := by
      rcases div_eq_zero_iff.mp h with h | h
      · exact h
      · exact absurd h hG
    rw [this]
    ring
  · intro h
    have hc : completedRiemannZeta s = 0 := by
      have h2 : (1 / 2 : ℂ) ≠ 0 := by norm_num
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h h2
          · exact absurd h hs0
        · exact absurd h hs1'
      · exact h
    rw [hc]
    simp

lemma zeros_xiEntiere_eq_critiques (hRH : RiemannHypothesisXi) :
    {s : ℂ | xiEntiere s = 0} = {s : ℂ | xiEntiere s = 0 ∧ s.re = 1 / 2} := by
  ext s
  constructor
  · intro h
    exact ⟨h, hRH s h⟩
  · intro h
    exact h.1

lemma xiEntiere_eq_zero_of_zeroNonTrivial {s : ℂ} (hs : ZeroNonTrivial s) :
    xiEntiere s = 0 := by
  obtain ⟨hz, hneg, h1⟩ := hs
  have h0 : s ≠ 0 := by
    intro h
    rw [h, riemannZeta_zero] at hz
    norm_num at hz
  rw [← xi_eq_xiEntiere s h0 h1, xi_eq_of_ne s h0 h1]
  have hΛ : completedRiemannZeta s = 0 := by
    have hG : Complex.Gammaℝ s ≠ 0 := by
      intro hG
      rw [Complex.Gammaℝ_eq_zero_iff] at hG
      obtain ⟨n, hn⟩ := hG
      cases n with
      | zero => exact h0 (by simpa using hn)
      | succ m =>
        apply hneg
        refine ⟨m, ?_⟩
        rw [hn]
        push_cast
        ring
    rw [riemannZeta_def_of_ne_zero h0, div_eq_zero_iff] at hz
    exact hz.resolve_right hG
  rw [hΛ, mul_zero]

lemma xiEntiere_one : xiEntiere 1 = 1 / 2 := by
  unfold xiEntiere
  simp

lemma xiEntiere_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
  xiEntiere s ≠ 0 := by
  have h0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    norm_num at hs
  by_cases h1 : s = 1
  · subst h1
    rw [xiEntiere_one]
    norm_num
  · have hre : 0 < s.re := by linarith
    rw [← xi_eq_xiEntiere s h0 h1, xi_eq_of_re_pos s hre]
    have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hs
    have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr h1
    simp [h0, hs1, hG, hz]

lemma xiEntiere_zero_in_strip {s : ℂ} (hs : xiEntiere s = 0) :
    0 < s.re ∧ s.re < 1 := by
  have h1 : s.re < 1 := by
    by_contra h
    exact xiEntiere_ne_zero_of_one_le_re (not_lt.mp h) hs
  have h2 : (1 - s).re < 1 := by
    by_contra h
    refine xiEntiere_ne_zero_of_one_le_re (not_lt.mp h) ?_
    rw [xiEntiere_one_sub]; exact hs
  refine ⟨?_, h1⟩
  simp only [Complex.sub_re, Complex.one_re] at h2
  linarith












end XiEntiereRiemann
