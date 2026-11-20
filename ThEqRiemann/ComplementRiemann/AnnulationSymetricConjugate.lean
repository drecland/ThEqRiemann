import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.ComplementRiemann.BijectionHolomorphismeDisc
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2

/-! -/
namespace AnnulationSymmConj

open Set Complex
open RiemannDef BijHoloDisc


theorem deriv_symm_neg_conj (f : ℂ → ℂ)
    (hsym : ∀ w, f (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (f w))
    (w : ℂ) (_ : DifferentiableAt ℂ f w)
    (hd' : DifferentiableAt ℂ f (-(starRingEnd ℂ) w)) :
    deriv f (-(starRingEnd ℂ) w) = -(starRingEnd ℂ) (deriv f w) := by
  let g : ℂ → ℂ := fun z => f (-z)
  have hg : HasDerivAt g
      (-deriv f (-(starRingEnd ℂ) w)) ((starRingEnd ℂ) w) := by
    have h1 : HasDerivAt (fun z : ℂ => -z) (-1) ((starRingEnd ℂ) w) :=
      (hasDerivAt_id _).neg
    have h2 : HasDerivAt f (deriv f (-(starRingEnd ℂ) w))
        (-(starRingEnd ℂ) w) := hd'.hasDerivAt
    have h3 := h2.scomp ((starRingEnd ℂ) w) h1
    have h4 : (-1 : ℂ) • deriv f (-(starRingEnd ℂ) w)
        = -deriv f (-(starRingEnd ℂ) w) := by
      simp
    rw [h4] at h3
    exact h3
  have hfun : f = fun z => (starRingEnd ℂ) (g ((starRingEnd ℂ) z)) := by
    funext z
    dsimp [g]
    have h := hsym (-(starRingEnd ℂ) z)
    simpa [map_neg] using h
  have hdouble : ∀ x, deriv (fun z => (starRingEnd ℂ) (g ((starRingEnd ℂ) z))) x
      = (starRingEnd ℂ) (deriv g ((starRingEnd ℂ) x)) := by
    intro x
    exact congrFun (deriv_conj_conj (f := g)) x
  have hEq : deriv f w =
      -(starRingEnd ℂ) (deriv f (-(starRingEnd ℂ) w)) := by
    have e1 : deriv f w = (starRingEnd ℂ) (deriv g ((starRingEnd ℂ) w)) := by
      conv_lhs => rw [hfun]
      exact hdouble w
    rw [e1, hg.deriv]
    simp [map_neg]
  rw [hEq]
  simp [map_neg]

theorem logDeriv_symm_neg_conj (f : ℂ → ℂ)
    (hsym : ∀ w, f (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (f w))
    (w : ℂ) (hd : DifferentiableAt ℂ f w)
    (hd' : DifferentiableAt ℂ f (-(starRingEnd ℂ) w)) :
    deriv f (-(starRingEnd ℂ) w) / f (-(starRingEnd ℂ) w)
      = -(starRingEnd ℂ) (deriv f w / f w) := by
  rw [deriv_symm_neg_conj f hsym w hd hd', hsym w, map_div₀, neg_div]

theorem simplification_integrale_symetrie_zero
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε) (hre : zm.re = 0) :
    (∮ z in C(zm, ε),
      (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε 0 0 z *
          (deriv xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε 0 0 z) /
            xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε 0 0 z)) *
          deriv (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε 0 0) z
        - z * (deriv xiDecale z / xiDecale z))) = 0 := by
  have hconj : -(starRingEnd ℂ) zm = zm := by
    apply Complex.ext
    · simp [hre]
    · simp
  have hM : mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε 0 0 = fun z => z := by
    rw [hconj, mobiusDisque_zero_zero zm zm hε.ne']
    funext z
    simp
  rw [hM]
  have h0 : (fun z : ℂ =>
      ((fun z : ℂ => z) z *
          (deriv xiDecale ((fun z : ℂ => z) z) /
            xiDecale ((fun z : ℂ => z) z)) *
          deriv (fun z : ℂ => z) z
        - z * (deriv xiDecale z / xiDecale z))) = fun _ => 0 := by
    funext z
    simp
  rw [h0]
  simp [circleIntegral]


---------------------------------------------------------------------




end AnnulationSymmConj
