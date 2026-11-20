import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.ComplementRiemann.DecaleZeroProperty

/-! -/
namespace ZeroIntCarac

open Set Complex
open RiemannDef DecaleZeroProp

theorem partie_reelle_par_integrales
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε) (hm : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hz1 : xiDecale (-(starRingEnd ℂ) zm) = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (hmult : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat) :
    (zm.re : ℂ) =
      (Complex.I / (2 * ((analyticOrderAt xiDecale zm).toNat : ℂ))) *
        ((1 / (2 * ↑Real.pi * Complex.I)) *
            (∮ z in C(zm, ε), (-Complex.I * z) * (deriv xiDecale z / xiDecale z))
          - (1 / (2 * ↑Real.pi * Complex.I)) *
            (∮ z in C(-(starRingEnd ℂ) zm, ε),
              (-Complex.I * z) * (deriv xiDecale z / xiDecale z))) := by
  rw [moment1_cercle zm ε hε hz0 hiso1,
      moment1_cercle (-(starRingEnd ℂ) zm) ε hε hz1 hiso2, hmult]
  exact partie_reelle_par_moments _ hm zm


end ZeroIntCarac
