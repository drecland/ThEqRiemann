import mathlib
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.EigenSpectrumHankel
import ThEqRiemann.EqTheorem.EquationnaryTheorem

/-! -/
namespace SpecInversion

open Set Complex DefinitionsThEq SpectrumHankel ThEq

theorem inversion_spectrale_general
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y : ℂ)
    (lam : Fin K → ℂ) (mult : Fin K → ℤ)
    (hlam : Function.Injective lam) (hmult : ∀ r, mult r ≠ 0)
    (hmom : ∀ k : ℕ, momentsParametres C γΩ g y k
              = ∑ r : Fin K, (mult r : ℂ) * (lam r) ^ k) :
    IsUnit (hankel0Dynamique K C γΩ g y) ∧
    spectrum ℂ ((hankel0Dynamique K C γΩ g y)⁻¹ *
      hankel1Dynamique K C γΩ g y)
      = Set.range lam :=
  spectre_operateur_regulier K C γΩ g y lam mult hlam hmult hmom

theorem inversion_spectrale_one
    (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y : ℂ)
    (lam : Fin 1 → ℂ) (mult : Fin 1 → ℤ)
    (hmult1 : mult 0 = 1)
    (hmom : ∀ k : ℕ, momentsParametres C γΩ g y k
              = ∑ r : Fin 1, (mult r : ℂ) * (lam r) ^ k) :
    momentsParametres C γΩ g y 1 = lam 0 := by
  rw [hmom 1]
  rw [Fin.sum_univ_one]
  rw [hmult1, Int.cast_one, one_mul, pow_one]

lemma operateur_un_eq_moment (C : CadreGeometrique) (γΩ : ℝ → ℂ)
    (g : ℂ → ℂ) (y : ℂ) (lam : Fin 1 → ℂ) (mult : Fin 1 → ℤ)
    (hmult1 : mult 0 = 1)
    (hmom : ∀ k : ℕ,
      momentsParametres C γΩ g y k =
        ∑ r : Fin 1, (mult r : ℂ) * (lam r) ^ k) :
    (hankel0Dynamique 1 C γΩ g y)⁻¹ *
        hankel1Dynamique 1 C γΩ g y =
      Matrix.of (fun _ _ => lam 0) := by
  have hν0 : momentsParametres C γΩ g y 0 = 1 := by
    rw [hmom 0]
    simp [hmult1]
  have hν1 : momentsParametres C γΩ g y 1 = lam 0 := by
    rw [hmom 1]
    simp [hmult1]
  have hH0 : hankel0Dynamique 1 C γΩ g y =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    have hi : i = 0 := Fin.fin_one_eq_zero i
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst hi
    subst hj
    simp [hankel0Dynamique, hankelOfMoments, hν0]
  rw [hH0]
  ext i j
  have hi : i = 0 := Fin.fin_one_eq_zero i
  have hj : j = 0 := Fin.fin_one_eq_zero j
  subst hi
  subst hj
  simp [hankel1Dynamique, hν1]

theorem inversion_spectrale_meromorphe
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ)
    (lamFun : ℂ → Fin K → ℂ) (w : ℂ → Fin K → ℤ)
    (hlam : ∀ y, Function.Injective (lamFun y))
    (hw : ∀ y r, w y r ≠ 0)
    (hmom : ∀ y k, momentsParametres C γΩ g y k
              = ∑ r : Fin K, (w y r : ℂ) * (lamFun y r) ^ k)
    (hsol : ∀ y, Set.range (lamFun y) = ensembleSolutions C.f C.Ω (g y)) :
    ∀ y : ℂ,
      IsUnit (hankel0Dynamique K C γΩ g y) ∧
      spectrum ℂ ((hankel0Dynamique K C γΩ g y)⁻¹ * hankel1Dynamique K C γΩ g y)
        = ensembleSolutions C.f C.Ω (g y) := by
  intro y
  obtain ⟨hU, hspec⟩ :=
    inversion_spectrale_general K C γΩ g y (lamFun y) (w y) (hlam y) (hw y) (hmom y)
  exact ⟨hU, hspec.trans (hsol y)⟩



end SpecInversion
