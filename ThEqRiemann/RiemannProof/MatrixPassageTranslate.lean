import mathlib
import ThEqRiemann.EqTheorem.Vandermonde

/-! -/
namespace MatTranslate

open Set Complex Matrix
open scoped ComplexOrder

lemma resolvante_explicite (τk τn σn : ℝ)
    (h : (τn - τk) ^ 2 + σn ^ 2 ≠ 0) :
    1 / (((τn : ℂ) - (σn : ℂ) * Complex.I) - (τk : ℂ)) =
      (((τn - τk : ℝ) : ℂ) + (σn : ℂ) * Complex.I) /
        (((τn - τk) ^ 2 + σn ^ 2 : ℝ) : ℂ) := by
  have hc : ((((τn - τk) ^ 2 + σn ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast h
  have hden : (((τn : ℂ) - (σn : ℂ) * Complex.I) - (τk : ℂ)) ≠ 0 := by
    intro h0
    apply h
    have h1 := congrArg Complex.re h0
    have h2 := congrArg Complex.im h0
    simp at h1 h2
    nlinarith [sq_nonneg (τn - τk), sq_nonneg σn]
  field_simp
  push_cast
  ring_nf
  simp [sq]

lemma resolvante_reelle_iff (τk τn σn : ℝ)
    (h : (τn - τk) ^ 2 + σn ^ 2 ≠ 0) :
    (1 / (((τn : ℂ) - (σn : ℂ) * Complex.I) - (τk : ℂ))).im = 0 ↔ σn = 0 := by
  rw [resolvante_explicite τk τn σn h, Complex.div_ofReal_im]
  simp only [ofReal_sub, add_im, sub_im, ofReal_im, sub_self, mul_im, ofReal_re, I_im,
    mul_one, I_re, mul_zero, add_zero, zero_add, div_eq_zero_iff, or_iff_left_iff_imp]
  intro h0
  exact absurd h0 h

lemma moment_un_im (s τn σn : ℝ) :
    ((s : ℂ) + ((τn : ℂ) - (σn : ℂ) * Complex.I)).im = -σn := by
  simp


lemma not_posDef_of_det_neg {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (hdet : H.det < 0) : ¬ H.PosDef := by
  intro hpd
  have := hpd.det_pos
  linarith

lemma operateur_non_defini_positif {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ)
    (hsymm : H.IsHermitian) (hdet : H.det < 0) :
    ¬ ∀ x : Fin m → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (H *ᵥ x) := by
  intro hall
  apply not_posDef_of_det_neg H hdet
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨hsymm, ?_⟩
  intro x hx
  simpa using hall x hx

end MatTranslate
