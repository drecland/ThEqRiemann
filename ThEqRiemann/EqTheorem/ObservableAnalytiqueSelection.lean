import mathlib
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.Vandermonde
import ThEqRiemann.EqTheorem.EigenSpectrumHankel

/-! -/
namespace ObservableSelectionTheorem

open Set Complex DefinitionsThEq VandermondeThEq SpectrumHankel

lemma hankelOfMoments_factorisation
    {K : ℕ}
    (mu : ℕ → ℂ)
    (lam : Fin K → ℂ)
    (w : Fin K → ℤ)
    (hmu : ∀ k : ℕ, mu k = ∑ r : Fin K, (w r : ℂ) * (lam r) ^ k) :
    hankelOfMoments K mu =
      vandermonde' lam * diagPoids w * (vandermonde' lam).transpose := by
  rw [hankelOfMoments_eq_hankel0 mu lam w hmu]
  exact factorisation_hankel lam w

lemma hankel0_factorisation_mathlib
    {K : ℕ}
    (mu : ℕ → ℂ)
    (lam : Fin K → ℂ)
    (w : Fin K → ℤ)
    (hmu : ∀ k : ℕ, mu k = ∑ r : Fin K, (w r : ℂ) * (lam r) ^ k) :
    hankelOfMoments K mu =
      (Matrix.vandermonde lam).transpose * diagPoids w * Matrix.vandermonde lam := by
  rw [hankelOfMoments_factorisation mu lam w hmu]
  have hV : vandermonde' lam = (Matrix.vandermonde lam).transpose :=
    vandermonde'_eq_transpose_vandermonde lam
  rw [hV, Matrix.transpose_transpose]


theorem hankel0_inversible
    {K : ℕ} (mu : ℕ → ℂ) (lam : Fin K → ℂ) (w : Fin K → ℤ)
    (hlam : Function.Injective lam) (hw : ∀ r : Fin K, w r ≠ 0)
    (hmu : ∀ k : ℕ, mu k = ∑ r : Fin K, (w r : ℂ) * (lam r) ^ k) :
    IsUnit (hankelOfMoments K mu).det := by
  rw [hankelOfMoments_eq_hankel0 mu lam w hmu]
  exact (hankel0_det_ne_zero lam w hlam hw).isUnit

theorem hankel1_factorisation
    {r : ℕ} (a : Fin r → ℂ) (w : Fin r → ℤ) (μ : ℕ → ℂ)
    (hμ : ∀ k, μ k = ∑ j, (w j : ℂ) * (a j) ^ k) :
    hankelOfMoments r (fun k => μ (k + 1)) =
      (Matrix.vandermonde a).transpose *
        Matrix.diagonal (fun j => (w j : ℂ) * a j) *
        Matrix.vandermonde a := by
  have h1 : hankelOfMoments r (fun k => μ (k + 1)) =
    hankel1 a w := by
    ext i j
    simp only [hankelOfMoments, hankel1, momentsHankel]
    exact hμ (i.1 + j.1 + 1)
  rw [h1]
  ext i j
  simp only [hankel1, momentsHankel, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.vandermonde_apply,
    Matrix.diagonal_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

theorem spectre_operateurM
    {r : ℕ} (a : Fin r → ℂ) (w : Fin r → ℤ)
    (ha : Function.Injective a) (hw : ∀ j, w j ≠ 0) :
    spectrum ℂ (operateurM a w) = Set.range a := by
  unfold operateurM
  exact spectre_hankel_inverse a w ha hw

theorem zero_dans_spectre_iff
    {K M : ℕ} (az : Fin K → ℂ) (ap : Fin M → ℂ)
    (Mat : Matrix (Fin (K + M)) (Fin (K + M)) ℂ)
    (h : spectrum ℂ Mat = Set.range az ∪ Set.range ap) :
    (0 : ℂ) ∈ spectrum ℂ Mat ↔ (∃ j, az j = 0) ∨ (∃ l, ap l = 0) := by
  rw [h]
  simp [Set.mem_union, Set.mem_range]

theorem selection_spectrale
    {K M : ℕ} (az : Fin K → ℂ) (ap : Fin M → ℂ)
    (m : Fin K → ℕ) (d : Fin M → ℕ)
    (hm : ∀ j, 0 < m j) (hd : ∀ l, 0 < d l)
    (hdist : Function.Injective (Sum.elim az ap)) :
    let lam : Fin (K + M) → ℂ := Sum.elim az ap ∘
      finSumFinEquiv.symm
    let w : Fin (K + M) → ℤ :=
      Sum.elim (fun j => (m j : ℤ)) (fun l => -(d l : ℤ)) ∘
      finSumFinEquiv.symm
    IsUnit (hankel0 lam w).det ∧
    spectrum ℂ (operateurM lam w) = Set.range az ∪ Set.range ap := by
  intro lam w
  have hlam : Function.Injective lam :=
    hdist.comp finSumFinEquiv.symm.injective
  have hw : ∀ i, w i ≠ 0 := by
    intro i
    simp only [w, Function.comp]
    rcases finSumFinEquiv.symm i with j | l
    · simp only [Sum.elim_inl]
      exact_mod_cast (hm j).ne'
    · simp only [Sum.elim_inr]
      have := hd l
      omega
  refine ⟨(hankel0_det_ne_zero lam w hlam hw).isUnit, ?_⟩
  rw [spectre_operateurM lam w hlam hw]
  ext z
  simp only [lam, Set.mem_range, Set.mem_union, Function.comp]
  constructor
  · rintro ⟨i, hi⟩
    rcases h : finSumFinEquiv.symm i with j | l
    · left; exact ⟨j, by simpa [h] using hi⟩
    · right; exact ⟨l, by simpa [h] using hi⟩
  · rintro (⟨j, hj⟩ | ⟨l, hl⟩)
    · exact ⟨finSumFinEquiv (Sum.inl j), by simp [hj]⟩
    · exact ⟨finSumFinEquiv (Sum.inr l), by simp [hl]⟩


theorem recherche_zeros_observable
    {K M : ℕ} (az : Fin K → ℂ) (ap : Fin M → ℂ)
    (m : Fin K → ℕ) (d : Fin M → ℕ)
    (hm : ∀ j, 0 < m j) (hd : ∀ l, 0 < d l)
    (hdist : Function.Injective (Sum.elim az ap)) :
    let lam : Fin (K + M) → ℂ := Sum.elim az ap ∘ finSumFinEquiv.symm
    let w : Fin (K + M) → ℤ :=
      Sum.elim (fun j => (m j : ℤ)) (fun l => -(d l : ℤ)) ∘
        finSumFinEquiv.symm
    IsUnit (hankel0 lam w).det ∧
    spectrum ℂ (operateurM lam w) = Set.range az ∪ Set.range ap ∧
    (∀ i, 0 < w i ↔ lam i ∈ Set.range az) := by
  intro lam w
  obtain ⟨hinv, hspec⟩ := selection_spectrale az ap m d hm hd hdist
  refine ⟨hinv, hspec, ?_⟩
  intro i
  rcases h : finSumFinEquiv.symm i with j | l
  · simp only [w, lam, Function.comp, h, Sum.elim_inl]
    constructor
    · intro _; exact ⟨j, rfl⟩
    · intro _; exact_mod_cast hm j
  · simp only [w, lam, Function.comp, h, Sum.elim_inr]
    constructor
    · intro hpos
      have := hd l
      omega
    · rintro ⟨j, hj⟩
      have : Sum.elim az ap (Sum.inl j) =
        Sum.elim az ap (Sum.inr l) := by
        simpa using hj
      exact absurd (hdist this) (by simp)



end ObservableSelectionTheorem
