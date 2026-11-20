import mathlib
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.CompagnonCharpoly
import ThEqRiemann.EqTheorem.Vandermonde

/-! -/
namespace SpectrumHankel

open Set Complex DefinitionsThEq Matrix
open CompagnonCharpolyThEq VandermondeThEq

lemma hankel_inverse_mul_eq_companion
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam) (hw : ∀ r : Fin K, w r ≠ 0) :
    (hankel0 lam w)⁻¹ * hankel1 lam w = companion' lam := by
  rw [hankel1_eq_hankel0_mul_companion, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul (hankel0 lam w)
        (hankel0_det_ne_zero lam w hlam hw).isUnit,
      Matrix.one_mul]

lemma hankel_inverse_mul_charpoly
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam) (hw : ∀ r : Fin K, w r ≠ 0) :
    Matrix.charpoly ((hankel0 lam w)⁻¹ * hankel1 lam w) =
    polyAssocie lam := by
  rw [hankel_inverse_mul_eq_companion lam w hlam hw]
  exact companion'_charpoly lam

lemma spectre_eq_roots_charpoly
    {K : ℕ} (M : Matrix (Fin K) (Fin K) ℂ) (r : ℂ) :
    r ∈ spectrum ℂ M ↔ (Matrix.charpoly M).IsRoot r :=
  Matrix.mem_spectrum_iff_isRoot_charpoly

lemma polyAssocie_eval
    {K : ℕ} (lam : Fin K → ℂ) (z : ℂ) :
    (polyAssocie lam).eval z = ∏ j : Fin K, (z - lam j) := by
  simp [polyAssocie, Polynomial.eval_prod]

lemma polyAssocie_isRoot_iff_mem_range
    {K : ℕ} (lam : Fin K → ℂ) (z : ℂ) :
    (polyAssocie lam).IsRoot z ↔ z ∈ Set.range lam := by
  change (polyAssocie lam).eval z = 0 ↔ z ∈ Set.range lam
  rw [polyAssocie_eval]
  constructor
  · intro h
    have h' : ∃ j ∈ (Finset.univ : Finset (Fin K)), z - lam j = 0 :=
      (Finset.prod_eq_zero_iff).mp h
    rcases h' with ⟨j, hj, hz⟩
    exact ⟨j, (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨j, rfl⟩
    exact (Finset.prod_eq_zero_iff).mpr
      ⟨j, Finset.mem_univ j, by simp⟩

theorem spectre_hankel_inverse
    {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam) (hw : ∀ r : Fin K, w r ≠ 0) :
    spectrum ℂ ((hankel0 lam w)⁻¹ * hankel1 lam w) = Set.range lam := by
  ext z
  rw [spectre_eq_roots_charpoly, hankel_inverse_mul_charpoly
      lam w hlam hw, polyAssocie_isRoot_iff_mem_range]






end SpectrumHankel
