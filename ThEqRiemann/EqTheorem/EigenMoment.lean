import mathlib

import ThEqRiemann.EqTheorem.DefThEq

/-! -/
namespace EigenMomentThEq

open DefinitionsThEq Set Complex


lemma finset_disjoint_solutions_poles
    {f : ℂ → ℂ} {Ω₁ : Set ℂ} {w : ℂ}
    (S : Finset ℂ) (P : Finset ℂ)
    (hS : (S : Set ℂ) = ensembleSolutions f Ω₁ w)
    (hP : (P : Set ℂ) = poles f Ω₁)
    (hdisj : Disjoint (ensembleSolutions f Ω₁ w) (poles f Ω₁)) :
    Disjoint S P := by
  rw [← Finset.disjoint_coe]
  rw [hS, hP]
  exact hdisj

lemma sum_residus_union_eq_add
    {f : ℂ → ℂ} {w : ℂ} {k : ℕ}
    {γ : ℝ → ℂ} (S P : Finset ℂ) (hdisj : Disjoint S P) :
    ∑ a ∈ S ∪ P, (indiceLacet γ a) * (residu (formeSpectrale f w k) a 1)
      = (∑ a ∈ S, (indiceLacet γ a) * (residu (formeSpectrale f w k) a 1))
      + (∑ a ∈ P, (indiceLacet γ a) * (residu (formeSpectrale f w k) a 1)) := by
  exact Finset.sum_union hdisj


lemma sum_residus_solutions_eq
    {f : ℂ → ℂ} {w : ℂ} {k : ℕ} {γ : ℝ → ℂ}
    (S : Finset ℂ)
    (m : ℂ → ℕ)
    (hind : ∀ x ∈ S, indiceLacet γ x = 1)
    (hres : ∀ x ∈ S, residu (formeSpectrale f w k) x 1 = (m x : ℂ) * x ^ k) :
    ∑ a ∈ S, (indiceLacet γ a) * (residu (formeSpectrale f w k) a 1)
      = ∑ a ∈ S, (m a : ℂ) * a ^ k := by
  apply Finset.sum_congr rfl
  intro x hx
  rw [hind x hx, hres x hx, one_mul]


lemma sum_residus_poles_eq
    {f : ℂ → ℂ} {w : ℂ} {k : ℕ} {γ : ℝ → ℂ}
    (P : Finset ℂ)
    (n : ℂ → ℕ)
    (hind : ∀ p ∈ P, indiceLacet γ p = 1)
    (hres : ∀ p ∈ P, residu (formeSpectrale f w k) p 1 = -(n p : ℂ) * p ^ k) :
    ∑ a ∈ P, (indiceLacet γ a) * (residu (formeSpectrale f w k) a 1)
      = ∑ a ∈ P, -(n a : ℂ) * a ^ k := by
  apply Finset.sum_congr rfl
  intro x hx
  rw [hind x hx, hres x hx, one_mul]


theorem moments_spectraux_meromorphe_parametre
    {f : ℂ → ℂ} {Ω₁ : Set ℂ} {w : ℂ} {k : ℕ} {γ : ℝ → ℂ}
    (S P : Finset ℂ) (m n : ℂ → ℕ)
    (_ : (S : Set ℂ) = ensembleSolutions f Ω₁ w)
    (_ : (P : Set ℂ) = poles f Ω₁)
    (hdisj : Disjoint S P)
    (_ : MeromorphicOn f Ω₁)
    (_ : poles (formeSpectrale f w k) Ω₁ ⊆ (S : Set ℂ) ∪ (P : Set ℂ))
    (hresidus_thm :
      (∫ t in (0 : ℝ)..1, deriv γ t * (formeSpectrale f w k) (γ t))
        = 2 * Complex.I * (Real.pi : ℂ) *
          ∑ a ∈ S ∪ P, (indiceLacet γ a) * (residu (formeSpectrale f w k) a 1))
    (hind : ∀ x ∈ S ∪ P, indiceLacet γ x = 1)
    (hres_sol : ∀ x ∈ S, residu (formeSpectrale f w k) x 1 = (m x : ℂ) * x ^ k)
    (hres_pole : ∀ p ∈ P, residu (formeSpectrale f w k) p 1 = -(n p : ℂ) * p ^ k) :
    (1 / (2 * Real.pi * Complex.I)) *
      (∫ t in (0 : ℝ)..1, deriv γ t * (formeSpectrale f w k) (γ t))
      = (∑ x ∈ S, (m x : ℂ) * x ^ k) - (∑ p ∈ P, (n p : ℂ) * p ^ k) := by
  rw [hresidus_thm]
  rw [Finset.sum_union hdisj]
  rw [sum_residus_solutions_eq S m (fun x hx => hind x (Finset.mem_union_left P hx)) hres_sol]
  rw [sum_residus_poles_eq P n (fun x hx => hind x (Finset.mem_union_right S hx)) hres_pole]
  field_simp
  ring_nf
  rw [Finset.sum_neg_distrib]
  ring





end EigenMomentThEq
