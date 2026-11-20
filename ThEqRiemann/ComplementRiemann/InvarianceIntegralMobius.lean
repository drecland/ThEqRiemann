import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.ComplementRiemann.AnnulationSymetricConjugate
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2
import ThEqRiemann.ComplementRiemann.BijectionHolomorphismeDisc
/-! -/
namespace InvaranceIntMobius

open Set Complex
open RiemannDef AnnulationSymmConj BijHoloDisc


theorem conj_g_conj_eq_g_neg
    (f : ℂ → ℂ)
    (hsym : ∀ w, f (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (f w))
    (hd : ∀ w, DifferentiableAt ℂ f w) (w : ℂ) :
    (starRingEnd ℂ) ((starRingEnd ℂ) w *
      (deriv f ((starRingEnd ℂ) w) / f ((starRingEnd ℂ) w)))
      = (-w) * (deriv f (-w) / f (-w)) := by
  have h := deriv_symm_neg_conj f hsym (-w) (hd (-w)) (hd _)
  have hs := hsym (-w)
  simp only [map_neg, neg_neg] at h hs ⊢
  rw [map_mul, map_div₀, h, hs]
  simp only [Complex.conj_conj, map_neg]
  ring

open CircInt2

theorem integrande_symetrie_conj (f : ℂ → ℂ)
    (hsym : ∀ w, f (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (f w))
    (w : ℂ) (hd : DifferentiableAt ℂ f w)
    (hd' : DifferentiableAt ℂ f (-(starRingEnd ℂ) w)) :
    (-(starRingEnd ℂ) w) *
        (deriv f (-(starRingEnd ℂ) w) / f (-(starRingEnd ℂ) w))
      = (starRingEnd ℂ) (w * (deriv f w / f w)) := by
  rw [logDeriv_symm_neg_conj f hsym w hd hd']
  simp [map_mul]


theorem integrale_cercle_symetrique
    (zm : ℂ) (ε : ℝ) (_ : 0 < ε)
    (hd : ∀ w, DifferentiableAt ℂ xiDecale w)
    (hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w)) :
    (∮ z in C(-(starRingEnd ℂ) zm, ε), z * (deriv xiDecale z / xiDecale z))
      = (starRingEnd ℂ) (∮ z in C(zm, ε), z * (deriv xiDecale z / xiDecale z)) := by
  set g : ℂ → ℂ := fun z => z * (deriv xiDecale z / xiDecale z) with hg
  simp only [circleIntegral, deriv_circleMap]
  rw [intervalIntegral_conj']
  have hpoint : ∀ t : ℝ,
      (circleMap 0 ε t * Complex.I) • g (circleMap (-(starRingEnd ℂ) zm) ε t)
      = (starRingEnd ℂ) ((circleMap 0 ε (Real.pi - t) * Complex.I)
          • g (circleMap zm ε (Real.pi - t))) := by
    intro t
    rw [circleMap_neg_conj]
    have hgs := integrande_symetrie_conj xiDecale hsym
      (circleMap zm ε (Real.pi - t)) (hd _) (hd _)
    simp only [hg, smul_eq_mul]
    rw [hgs, deriv_circleMap_reflexion ε t]
    simp only [map_mul, Complex.conj_I]
  set F : ℝ → ℂ := fun t => (starRingEnd ℂ)
    ((circleMap 0 ε t * Complex.I) • g (circleMap zm ε t)) with hF
  have hper : Function.Periodic F (2 * Real.pi) := by
    intro t
    simp only [hF]
    rw [periodic_circleMap 0 ε t, periodic_circleMap zm ε t]
  have hleft : (∫ θ in (0:ℝ)..2 * Real.pi,
      (circleMap 0 ε θ * Complex.I) • g (circleMap (-(starRingEnd ℂ) zm) ε θ))
      = ∫ θ in (0:ℝ)..2 * Real.pi, F (Real.pi - θ) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hF]
    exact hpoint t
  rw [hleft, integral_reflexion_periodique F hper]

theorem integrale_zm_valeur
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hxi : Differentiable ℂ xiDecale)
    (hz0 : xiDecale zm = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm) :
    (∮ z in C(zm, ε), z * (deriv xiDecale z / xiDecale z))
      = 2 * Real.pi * Complex.I * ((analyticOrderAt xiDecale zm).toNat : ℂ) * zm := by
  have hne : ∀ z ∈ Metric.sphere zm ε, xiDecale z ≠ 0 := by
    intro z hz hz'
    have h := hiso1 z (le_of_eq (Metric.mem_sphere.mp hz)) hz'
    rw [h] at hz
    have h0 : (0 : ℝ) = ε := by simpa [Metric.mem_sphere] using hz
    exact hε.ne h0
  have hS : ∀ z, z ∈ ({zm} : Finset ℂ) ↔ z ∈ Metric.ball zm ε ∧ xiDecale z = 0 := by
    intro z
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨Metric.mem_ball_self hε, hz0⟩
    · rintro ⟨hb, hz⟩
      exact hiso1 z (le_of_lt (Metric.mem_ball.mp hb)) hz
  have h := argument_principle_circle hε hxi
    (differentiable_id) hne {zm} hS
  simp only [Finset.sum_singleton, id] at h
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp at h
  have hint : (fun z : ℂ => z * deriv xiDecale z / xiDecale z)
      = (fun z : ℂ => z * (deriv xiDecale z / xiDecale z)) := by
    funext z
    exact mul_div_assoc _ _ _
  rw [hint] at h
  exact h

theorem calcul_algebrique_final (zm : ℂ) (m : ℕ) :
    (starRingEnd ℂ) (2 * Real.pi * Complex.I * (m : ℂ) * zm)
      - 2 * Real.pi * Complex.I * (m : ℂ) * zm
      = -4 * Complex.I * Real.pi * (m : ℂ) * zm.re := by
  have h : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (m : ℂ) * zm)
      = -(2 * Real.pi * Complex.I * (m : ℂ) * (starRingEnd ℂ) zm) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]
    ring
  rw [h]
  have hre : (starRingEnd ℂ) zm = 2 * (zm.re : ℂ) - zm := by
    have := Complex.add_conj zm
    push_cast at this
    linear_combination this
  rw [hre]
  ring

theorem InvarianceEtValeurIntegrale
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hxi : Differentiable ℂ xiDecale)
    (_ : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w))
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (_ : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat)
    (hint : ∀ φ : ℂ → ℂ, BijHolPresOrient zm (-(starRingEnd ℂ) zm) ε φ →
      CircleIntegrable
        (fun z => φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z) zm ε ∧
      CircleIntegrable (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hMob : ∀ (a : ℂ) (θ : ℝ), ‖a‖ < 1 →
      BijHolPresOrient zm (-(starRingEnd ℂ) zm) ε
        (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ)) :
    ∀ (a : ℂ) (θ : ℝ), ‖a‖ < 1 →
      (∮ z in C(zm, ε),
          (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z *
              (deriv xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z) /
                xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z)) *
              deriv (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ) z
            - z * (deriv xiDecale z / xiDecale z)))
        = -4 * Complex.I * Real.pi * (analyticOrderAt xiDecale zm).toNat * zm.re := by
  intro a θ ha
  have h1 : (∮ z in C(zm, ε),
        mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z *
          (deriv xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z) /
            xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z)) *
          deriv (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ) z)
      = ∮ z in C(-(starRingEnd ℂ) zm, ε), z * (deriv xiDecale z / xiDecale z) := by
    have hφ := mobiusDisque_bijHolPresOrient zm (-(starRingEnd ℂ) zm) hε a ha θ
    have hG := continuousOn_log_deriv_sphere zm ε hε hiso2
    exact (hφ.chgt (fun w : ℂ => w * (deriv xiDecale w / xiDecale w)) hG).symm
  have hI2 := integrale_zm_valeur zm ε hε hxi hz0 hiso1
  have hI1 := integrale_cercle_symetrique zm ε hε (fun w => hxi w) hsym
  rw [circleIntegral.integral_sub (hint _ (hMob a θ ha)).1 (hint _ (hMob a θ ha)).2]
  rw [h1, hI1, hI2]
  exact calcul_algebrique_final zm _

theorem calcul_algebrique_final_somme (zm : ℂ) (m : ℕ) :
    (starRingEnd ℂ) (2 * Real.pi * Complex.I * (m : ℂ) * zm)
      + 2 * Real.pi * Complex.I * (m : ℂ) * zm
      = -4 * Real.pi * (m : ℂ) * zm.im := by
  have h : (starRingEnd ℂ) (2 * Real.pi * Complex.I * (m : ℂ) * zm)
      = -(2 * Real.pi * Complex.I * (m : ℂ) * (starRingEnd ℂ) zm) := by
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]
    ring
  rw [h]
  have him : (starRingEnd ℂ) zm = zm - 2 * (zm.im : ℂ) * Complex.I := by
    have hsub := Complex.sub_conj zm
    push_cast at hsub
    linear_combination -hsub
  rw [him]
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  linear_combination (4 * (Real.pi : ℂ) * (m : ℂ) * (zm.im : ℂ)) * hI2

theorem ExtractionImaginaire
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hxi : Differentiable ℂ xiDecale)
    (_ : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w))
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (_ : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat)
    (hint : ∀ φ : ℂ → ℂ, BijHolPresOrient zm (-(starRingEnd ℂ) zm) ε φ →
      CircleIntegrable
        (fun z => φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z) zm ε ∧
      CircleIntegrable (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hMob : ∀ (a : ℂ) (θ : ℝ), ‖a‖ < 1 →
      BijHolPresOrient zm (-(starRingEnd ℂ) zm) ε
        (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ)) :
    ∀ (a : ℂ) (θ : ℝ), ‖a‖ < 1 →
      (∮ z in C(zm, ε),
          (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z *
              (deriv xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z) /
                xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z)) *
              deriv (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ) z
            + z * (deriv xiDecale z / xiDecale z)))
        = -4 * Real.pi * (analyticOrderAt xiDecale zm).toNat * zm.im := by
  intro a θ ha
  have h1 : (∮ z in C(zm, ε),
        mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z *
          (deriv xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z) /
            xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z)) *
          deriv (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ) z)
      = ∮ z in C(-(starRingEnd ℂ) zm, ε), z * (deriv xiDecale z / xiDecale z) := by
    have hφ := mobiusDisque_bijHolPresOrient zm (-(starRingEnd ℂ) zm) hε a ha θ
    have hG := continuousOn_log_deriv_sphere zm ε hε hiso2
    exact (hφ.chgt (fun w : ℂ => w * (deriv xiDecale w / xiDecale w)) hG).symm
  have hI2 := integrale_zm_valeur zm ε hε hxi hz0 hiso1
  have hI1 := integrale_cercle_symetrique zm ε hε (fun w => hxi w) hsym
  rw [circleIntegral.integral_add (hint _ (hMob a θ ha)).1 (hint _ (hMob a θ ha)).2]
  rw [h1, hI1, hI2]
  exact calcul_algebrique_final_somme zm _


theorem inversion_systeme_integrales_locales
    (I₁ I₂ zm : ℂ) (m : ℕ)
    (hDelta : I₁ - I₂ = -4 * Complex.I * Real.pi * (m : ℂ) * zm.re)
    (hSigma : I₁ + I₂ = -4 * Real.pi * (m : ℂ) * zm.im) :
    I₁ = -2 * Complex.I * Real.pi * (m : ℂ) * (starRingEnd ℂ) zm ∧
    I₂ = 2 * Complex.I * Real.pi * (m : ℂ) * zm := by
  have hre_im : (zm.re : ℂ) + (zm.im : ℂ) * Complex.I = zm := Complex.re_add_im zm
  have hconj_re_im : (zm.re : ℂ) - (zm.im : ℂ) * Complex.I = (starRingEnd ℂ) zm := by
    apply Complex.ext <;> simp
  have hI2 : (Complex.I : ℂ) ^ 2 = -1 := Complex.I_sq
  constructor
  · have h1 : I₁ = (1/2 : ℂ) * (I₁ + I₂) + (1/2 : ℂ) * (I₁ - I₂) := by ring
    calc I₁ = (1/2 : ℂ) * (I₁ + I₂) + (1/2 : ℂ) * (I₁ - I₂) := h1
      _ = (1/2 : ℂ) * (-4 * Real.pi * (m : ℂ) * zm.im)
            + (1/2 : ℂ) * (-4 * Complex.I * Real.pi * (m : ℂ) * zm.re) := by
          rw [hSigma, hDelta]
      _ = -2 * Complex.I * Real.pi * (m : ℂ) * ((zm.re : ℂ) - (zm.im : ℂ) * Complex.I) := by
          linear_combination (-2 * (Real.pi : ℂ) * (m : ℂ) * (zm.im : ℂ)) * hI2
      _ = -2 * Complex.I * Real.pi * (m : ℂ) * (starRingEnd ℂ) zm := by
          rw [hconj_re_im]
  · have h2 : I₂ = (1/2 : ℂ) * (I₁ + I₂) - (1/2 : ℂ) * (I₁ - I₂) := by ring
    calc I₂ = (1/2 : ℂ) * (I₁ + I₂) - (1/2 : ℂ) * (I₁ - I₂) := h2
      _ = (1/2 : ℂ) * (-4 * Real.pi * (m : ℂ) * zm.im)
            - (1/2 : ℂ) * (-4 * Complex.I * Real.pi * (m : ℂ) * zm.re) := by
          rw [hSigma, hDelta]
      _ = 2 * Complex.I * Real.pi * (m : ℂ) * ((zm.re : ℂ) + (zm.im : ℂ) * Complex.I) := by
          linear_combination (-2 * (Real.pi : ℂ) * (m : ℂ) * (zm.im : ℂ)) * hI2
      _ = 2 * Complex.I * Real.pi * (m : ℂ) * zm := by
          rw [hre_im]

theorem DecompositionIntegralesLocales
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hxi : Differentiable ℂ xiDecale)
    (hz0 : xiDecale zm = 0)
    (hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w))
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm) :
    (∮ z in C(-(starRingEnd ℂ) zm, ε), z * (deriv xiDecale z / xiDecale z))
      = -2 * Complex.I * Real.pi * ((analyticOrderAt xiDecale zm).toNat : ℂ) *
          (starRingEnd ℂ) zm ∧
    (∮ z in C(zm, ε), z * (deriv xiDecale z / xiDecale z))
      = 2 * Complex.I * Real.pi * ((analyticOrderAt xiDecale zm).toNat : ℂ) * zm := by
  have hI2 := integrale_zm_valeur zm ε hε hxi hz0 hiso1
  have hI1 := integrale_cercle_symetrique zm ε hε (fun w => hxi w) hsym
  have hDiff :
      (∮ z in C(-(starRingEnd ℂ) zm, ε), z * (deriv xiDecale z / xiDecale z)) -
      (∮ z in C(zm, ε), z * (deriv xiDecale z / xiDecale z))
        = -4 * Complex.I * Real.pi * ((analyticOrderAt xiDecale zm).toNat : ℂ) * zm.re := by
    rw [hI1, hI2]
    exact calcul_algebrique_final zm _
  have hSum :
      (∮ z in C(-(starRingEnd ℂ) zm, ε), z * (deriv xiDecale z / xiDecale z)) +
      (∮ z in C(zm, ε), z * (deriv xiDecale z / xiDecale z))
        = -4 * Real.pi * ((analyticOrderAt xiDecale zm).toNat : ℂ) * zm.im := by
    rw [hI1, hI2]
    exact calcul_algebrique_final_somme zm _
  exact inversion_systeme_integrales_locales _ _ zm
    (analyticOrderAt xiDecale zm).toNat hDiff hSum



end InvaranceIntMobius
