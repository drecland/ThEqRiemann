import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.XiDecaleProp
import ThEqRiemann.RiemannProof.XiEntiereProp
import ThEqRiemann.ComplementRiemann.RealPartCaracterisation
import ThEqRiemann.ComplementRiemann.DecaleZeroProperty
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2
import ThEqRiemann.ComplementRiemann.BijectionHolomorphismeDisc

/-! -/
namespace RiemannHypEnonce

open Set Complex
open RiemannDef XiDecalePropRiemann XiEntiereRiemann RealPartCarac

theorem RiemannHypothesisXi_of_config
    (hconfig : ∀ zm ∈ zerosXiDecale, |zm.re| < 1 / 2 →
      ∃ U : Set ℂ, zm ∈ U ∧ (∀ z ∈ U, -(starRingEnd ℂ) z ∈ U) ∧
        (∀ z ∈ zerosXiDecale, z ∈ U → z = zm)) :
    RiemannHypothesisXi := by
  intro s hs
  obtain ⟨hpos, hlt⟩ := xiEntiere_zero_in_strip hs
  have hzm : (s - 1 / 2 : ℂ) ∈ zerosXiDecale := by
    simp only [zerosXiDecale, xiDecale, Set.mem_ofPred_eq]
    rw [show (1 / 2 : ℂ) + (s - 1 / 2) = s by ring]
    exact hs
  have hre : |(s - 1 / 2 : ℂ).re| < 1 / 2 := by
    have : (s - 1 / 2 : ℂ).re = s.re - 1 / 2 := by simp
    rw [this, abs_lt]
    constructor <;> linarith
  obtain ⟨U, hU, hUsymm, hUniq⟩ := hconfig _ hzm hre
  have hmain : (s - 1 / 2 : ℂ).re = 0 :=
    AnnulationPartieReelleZeta zerosXiDecale U _ hzm hU hUsymm hUniq
      zerosXiDecale_conj zerosXiDecale_neg
  have : s.re - 1 / 2 = 0 := by simpa using hmain
  linarith


theorem RiemannHypothesis_of_config
    (hconfig : ∀ zm ∈ zerosXiDecale, |zm.re| < 1 / 2 →
      ∃ U : Set ℂ, zm ∈ U ∧
        (∀ z ∈ U, -(starRingEnd ℂ) z ∈ U) ∧
        (∀ z ∈ zerosXiDecale, z ∈ U → z = zm)) :
    ∀ s : ℂ, riemannZeta s = 0 →
      (¬∃ n : ℕ, s = -2 * (n + 1)) → s ≠ 1 → s.re = 1 / 2 := by
  intro s hzeta hneg h1
  have hxi : xiEntiere s = 0 :=
    xiEntiere_eq_zero_of_zeroNonTrivial ⟨hzeta, hneg, h1⟩
  exact RiemannHypothesisXi_of_config hconfig s hxi


open DecaleZeroProp


theorem riemann_iff_moments_egaux :
    (∀ zm : ℂ, xiDecale zm = 0 → 0 < (analyticOrderAt xiDecale zm).toNat →
        zm.re = 0) ↔
    (∀ zm : ℂ, xiDecale zm = 0 → 0 < (analyticOrderAt xiDecale zm).toNat →
        moment1 (analyticOrderAt xiDecale zm).toNat zm =
        moment1 (analyticOrderAt xiDecale zm).toNat (-(starRingEnd ℂ) zm)) := by
  constructor
  · intro H zm hz hm
    exact (re_nulle_iff_moments_egaux _ hm zm).mp (H zm hz hm)
  · intro H zm hz hm
    exact (re_nulle_iff_moments_egaux _ hm zm).mpr (H zm hz hm)

open CircInt2 in
theorem equivalence_riemann_invariance_geometrique
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hm : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hz1 : xiDecale (-(starRingEnd ℂ) zm) = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (hmult : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat)
    (hint : ∀ φ : ℂ → ℂ, BijHolPresOrient zm (-(starRingEnd ℂ) zm) ε φ →
      CircleIntegrable
        (fun z => φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z)
        zm ε ∧
      CircleIntegrable (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hintT : CircleIntegrable
      (fun z => (z + (-(starRingEnd ℂ) zm - zm)) *
        (deriv xiDecale (z + (-(starRingEnd ℂ) zm - zm)) /
          xiDecale (z + (-(starRingEnd ℂ) zm - zm)))) zm ε)
    (hintB : CircleIntegrable
      (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε) :
    zm.re = 0 ↔
      ∀ φ : ℂ → ℂ, BijHolPresOrient zm (-(starRingEnd ℂ) zm) ε φ →
        (∮ z in C(zm, ε),
          (φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z
            - z * (deriv xiDecale z / xiDecale z))) = 0 := by
  constructor
  · intro hre φ hφ
    obtain ⟨hA, hB⟩ := hint φ hφ
    have hmom := (re_nulle_iff_moments_integrales zm ε hε hm hz0 hz1 hiso1 hiso2 hmult).mp hre
    have hchg := hφ.chgt (fun w => (-Complex.I * w) * (deriv xiDecale w / xiDecale w))
    rw [hchg] at hmom
    have hmom' :
        (∮ z in C(zm, ε), (-Complex.I) * (z * (deriv xiDecale z / xiDecale z))) =
        ∮ z in C(zm, ε), (-Complex.I) *
          (φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z) := by
      have e1 : (fun z : ℂ => (-Complex.I) * (z * (deriv xiDecale z / xiDecale z))) =
          fun z => -Complex.I * z * (deriv xiDecale z / xiDecale z) :=
        funext fun z => by ring
      have e2 : (fun z : ℂ => (-Complex.I) *
            (φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z)) =
          fun z => -Complex.I * φ z * (deriv xiDecale (φ z) / xiDecale (φ z))
            * deriv φ z :=
        funext fun z => by ring
      rw [e1, e2]
      exact hmom
    exact integrale_diff_nulle_of_moments hA hB hmom'
  · intro hall
    have hφ0 := translation_bijHolPresOrient zm (-(starRingEnd ℂ) zm - zm) ε
    have hc : zm + (-(starRingEnd ℂ) zm - zm) = -(starRingEnd ℂ) zm := by ring
    rw [hc] at hφ0
    have h0 := hall (fun z => z + (-(starRingEnd ℂ) zm - zm)) hφ0
    have hd : ∀ z : ℂ, deriv (fun z : ℂ => z + (-(starRingEnd ℂ) zm - zm)) z = 1 := by
      intro z; simp
    simp_rw [hd, mul_one] at h0
    exact (re_nulle_iff_integrale_translation zm ε hε hm hz0 hz1 hiso1 hiso2 hmult
      hintT hintB).mpr h0

open BijHoloDisc


theorem equivalence_riemann_parametree
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hm : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hz1 : xiDecale (-(starRingEnd ℂ) zm) = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (hmult : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat)
    (hint : ∀ φ : ℂ → ℂ, BijHolPresOrient zm (-(starRingEnd ℂ) zm) ε φ →
      CircleIntegrable
        (fun z => φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z) zm ε ∧
      CircleIntegrable (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hintT : CircleIntegrable
      (fun z => (z + (-(starRingEnd ℂ) zm - zm)) *
        (deriv xiDecale (z + (-(starRingEnd ℂ) zm - zm)) /
          xiDecale (z + (-(starRingEnd ℂ) zm - zm)))) zm ε)
    (hintB : CircleIntegrable
      (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hMob : ∀ (a : ℂ) (θ : ℝ), ‖a‖ < 1 →
      BijHolPresOrient zm (-(starRingEnd ℂ) zm) ε
        (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ)) :
    zm.re = 0 ↔
      ∀ (a : ℂ) (θ : ℝ), ‖a‖ < 1 →
        (∮ z in C(zm, ε),
          (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z *
              (deriv xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z) /
                xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z)) *
              deriv (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ) z
            - z * (deriv xiDecale z / xiDecale z))) = 0 := by
  have hcor := equivalence_riemann_invariance_geometrique zm ε hε hm hz0 hz1 hiso1 hiso2
    hmult hint hintT hintB
  constructor
  · intro hre a θ ha
    exact (hcor.mp hre) _ (hMob a θ ha)
  · intro hall
    refine (re_nulle_iff_integrale_translation zm ε hε hm hz0 hz1 hiso1 hiso2 hmult
      hintT hintB).mpr ?_
    have h0 := hall 0 0 (by simp)
    have hT : mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε 0 0 =
        fun z => z + (-(starRingEnd ℂ) zm - zm) :=
      mobiusDisque_zero_zero zm (-(starRingEnd ℂ) zm) hε.ne'
    rw [hT] at h0
    have hd : ∀ z : ℂ, deriv (fun z : ℂ => z + (-(starRingEnd ℂ) zm - zm)) z = 1 := by
      intro z; simp
    simp_rw [hd, mul_one] at h0
    exact h0

open CircInt2 in
theorem equivalence_riemann_invariance_geometrique_continuity
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hm : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hz1 : xiDecale (-(starRingEnd ℂ) zm) = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (hmult : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat)
    (hint : ∀ φ : ℂ → ℂ, BijHolPresOrientContinuity zm (-(starRingEnd ℂ) zm) ε φ →
      CircleIntegrable
        (fun z => φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z) zm ε ∧
      CircleIntegrable (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hintT : CircleIntegrable
      (fun z => (z + (-(starRingEnd ℂ) zm - zm)) *
        (deriv xiDecale (z + (-(starRingEnd ℂ) zm - zm)) /
          xiDecale (z + (-(starRingEnd ℂ) zm - zm)))) zm ε)
    (hintB : CircleIntegrable
      (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε) :
    zm.re = 0 ↔
      ∀ φ : ℂ → ℂ, BijHolPresOrientContinuity zm (-(starRingEnd ℂ) zm) ε φ →
        (∮ z in C(zm, ε),
          (φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z
            - z * (deriv xiDecale z / xiDecale z))) = 0 := by
  constructor
  · intro hre φ hφ
    obtain ⟨hA, hB⟩ := hint φ hφ
    have hmom := (re_nulle_iff_moments_integrales zm ε hε hm hz0 hz1 hiso1 hiso2 hmult).mp hre
    have hGcont : ContinuousOn
        (fun w => (-Complex.I * w) * (deriv xiDecale w / xiDecale w))
        (Metric.sphere (-(starRingEnd ℂ) zm) ε) := by
      have h : ContinuousOn
          (fun w : ℂ => (-Complex.I) * (w * (deriv xiDecale w / xiDecale w)))
          (Metric.sphere (-(starRingEnd ℂ) zm) ε) :=
        (continuousOn_const (c := -Complex.I)).mul
          (continuousOn_log_deriv_sphere zm ε hε hiso2)
      refine h.congr ?_
      intro w _
      ring
    have hchg := hφ.chgt (fun w => (-Complex.I * w) * (deriv xiDecale w / xiDecale w)) hGcont
    rw [hchg] at hmom
    have hmom' :
        (∮ z in C(zm, ε), (-Complex.I) * (z * (deriv xiDecale z / xiDecale z))) =
        ∮ z in C(zm, ε), (-Complex.I) *
          (φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z) := by
      have e1 : (fun z : ℂ => (-Complex.I) * (z * (deriv xiDecale z / xiDecale z))) =
          fun z => -Complex.I * z * (deriv xiDecale z / xiDecale z) :=
        funext fun z => by ring
      have e2 : (fun z : ℂ => (-Complex.I) *
            (φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z)) =
          fun z => -Complex.I * φ z * (deriv xiDecale (φ z) / xiDecale (φ z))
            * deriv φ z :=
        funext fun z => by ring
      rw [e1, e2]
      exact hmom
    exact integrale_diff_nulle_of_moments hA hB hmom'
  · intro hall
    have hφ0 := translation_bijHolPresOrient zm (-(starRingEnd ℂ) zm - zm) ε
    have hc : zm + (-(starRingEnd ℂ) zm - zm) = -(starRingEnd ℂ) zm := by ring
    rw [hc] at hφ0
    have h0 := hall (fun z => z + (-(starRingEnd ℂ) zm - zm))
      (BijHolPresOrient.toContinuity hφ0)
    have hd : ∀ z : ℂ, deriv (fun z : ℂ => z + (-(starRingEnd ℂ) zm - zm)) z = 1 := by
      intro z; simp
    simp_rw [hd, mul_one] at h0
    exact (re_nulle_iff_integrale_translation zm ε hε hm hz0 hz1 hiso1 hiso2 hmult
      hintT hintB).mpr h0

theorem equivalence_riemann_parametree_general
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hm : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hz1 : xiDecale (-(starRingEnd ℂ) zm) = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (hmult : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat)
    (hint : ∀ φ : ℂ → ℂ, BijHolPresOrientContinuity zm (-(starRingEnd ℂ) zm) ε φ →
      CircleIntegrable
        (fun z => φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z) zm ε ∧
      CircleIntegrable (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hintT : CircleIntegrable
      (fun z => (z + (-(starRingEnd ℂ) zm - zm)) *
        (deriv xiDecale (z + (-(starRingEnd ℂ) zm - zm)) /
          xiDecale (z + (-(starRingEnd ℂ) zm - zm)))) zm ε)
    (hintB : CircleIntegrable
      (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε) :
    zm.re = 0 ↔
      ∀ (a : ℂ) (θ : ℝ), ‖a‖ < 1 →
        (∮ z in C(zm, ε),
          (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z *
              (deriv xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z) /
                xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z)) *
              deriv (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ) z
            - z * (deriv xiDecale z / xiDecale z))) = 0 := by
  have hcor := equivalence_riemann_invariance_geometrique_continuity zm ε hε hm hz0 hz1
    hiso1 hiso2 hmult hint hintT hintB
  constructor
  · intro hre a θ ha
    exact (hcor.mp hre) _ (mobiusDisque_bijHolPresOrient zm (-(starRingEnd ℂ) zm) hε a ha θ)
  · intro hall
    refine (re_nulle_iff_integrale_translation zm ε hε hm hz0 hz1 hiso1 hiso2 hmult
      hintT hintB).mpr ?_
    have h0 := hall 0 0 (by simp)
    have hT : mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε 0 0 =
        fun z => z + (-(starRingEnd ℂ) zm - zm) :=
      mobiusDisque_zero_zero zm (-(starRingEnd ℂ) zm) hε.ne'
    rw [hT] at h0
    have hd : ∀ z : ℂ, deriv (fun z : ℂ => z + (-(starRingEnd ℂ) zm - zm)) z = 1 := by
      intro z; simp
    simp_rw [hd, mul_one] at h0
    exact h0



theorem reduction_polaire_symetrie
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε) (hre : zm.re = 0)
    (a : ℂ) (ha : ‖a‖ < 1) (θ : ℝ)
    (hm : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hz1 : xiDecale (-(starRingEnd ℂ) zm) = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (hmult : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat)
    (hint : ∀ φ : ℂ → ℂ, BijHolPresOrientContinuity zm (-(starRingEnd ℂ) zm) ε φ →
      CircleIntegrable
        (fun z => φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z) zm ε ∧
      CircleIntegrable (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hintT : CircleIntegrable
      (fun z => (z + (-(starRingEnd ℂ) zm - zm)) *
        (deriv xiDecale (z + (-(starRingEnd ℂ) zm - zm)) /
          xiDecale (z + (-(starRingEnd ℂ) zm - zm)))) zm ε)
    (hintB : CircleIntegrable
      (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε) :
    ∮ z in C(zm, ε),
      (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z *
          (deriv xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z) /
            xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z)) *
          deriv (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ) z
        - z * (deriv xiDecale z / xiDecale z)) = 0 := by
  exact ((equivalence_riemann_parametree_general zm ε hε hm hz0 hz1 hiso1 hiso2
    hmult hint hintT hintB).mp hre) a θ ha

theorem re_zero_of_integrale_nulle
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hm : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hz1 : xiDecale (-(starRingEnd ℂ) zm) = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (hmult : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat)
    (hint : ∀ φ : ℂ → ℂ, BijHolPresOrientContinuity zm (-(starRingEnd ℂ) zm) ε φ →
      CircleIntegrable
        (fun z => φ z * (deriv xiDecale (φ z) / xiDecale (φ z)) * deriv φ z) zm ε ∧
      CircleIntegrable (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hintT : CircleIntegrable
      (fun z => (z + (-(starRingEnd ℂ) zm - zm)) *
        (deriv xiDecale (z + (-(starRingEnd ℂ) zm - zm)) /
          xiDecale (z + (-(starRingEnd ℂ) zm - zm)))) zm ε)
    (hintB : CircleIntegrable
      (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε)
    (hint0 : ∀ (a : ℂ) (θ : ℝ), ‖a‖ < 1 →
      (∮ z in C(zm, ε),
        (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z *
            (deriv xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z) /
              xiDecale (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ z)) *
            deriv (mobiusDisque zm (-(starRingEnd ℂ) zm) ε ε a θ) z
          - z * (deriv xiDecale z / xiDecale z))) = 0) :
    zm.re = 0 :=
  (equivalence_riemann_parametree_general zm ε hε hm hz0 hz1 hiso1 hiso2
    hmult hint hintT hintB).mpr hint0








end RiemannHypEnonce
