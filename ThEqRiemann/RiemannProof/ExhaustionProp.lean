import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.PosHankelFiniteExhaustion


/-! -/
namespace ExhaustProp

open Set Complex
open RiemannDef PosHankelFinExhaustion



variable (X : Exhaustion)

lemma posDef_iff_real (N : ℕ) :
    HankelFusionPosDef (X.E N) X.m (X.D N) ↔ ∀ γ ∈ X.E N, γ.im = 0 :=
  hankelFusion_posDef_iff_real (X.E N) X.m (X.hD N) (X.hE N) X.hm
    (fun δ hδ => X.hm_pos δ (X.hsub N hδ))

lemma all_posDef_iff_real :
    (∀ N, HankelFusionPosDef (X.E N) X.m (X.D N)) ↔ ∀ N, ∀ γ ∈ X.E N, γ.im = 0 :=
  ⟨fun h N => (posDef_iff_real X N).mp (h N),
   fun h N => (posDef_iff_real X N).mpr (h N)⟩


lemma all_real_iff :
    (∀ N, ∀ γ ∈ X.E N, γ.im = 0) ↔ ∀ γ ∈ X.Λ, γ.im = 0 :=
  ⟨fun h γ hγ => by
      obtain ⟨N, hN⟩ := X.hcov γ hγ
      exact h N γ hN,
   fun h N γ hγ => h γ (X.hsub N hγ)⟩

lemma all_posDef_iff_Lambda_real :
    (∀ N, HankelFusionPosDef (X.E N) X.m (X.D N)) ↔ ∀ γ ∈ X.Λ, γ.im = 0 :=
  (all_posDef_iff_real X).trans (all_real_iff X)

end ExhaustProp
