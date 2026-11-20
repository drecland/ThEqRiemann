import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.PosHankelFiniteExhaustion
import ThEqRiemann.RiemannProof.ExhaustionProp

/-! -/
namespace PosHankelCritGlobal

open Set Complex
open RiemannDef PosHankelFinExhaustion


theorem hankel_posDef_all_iff_zeros_real
    (Λ : Set ℂ) (E : ℕ → Finset ℂ) (D : ℕ → ℕ) (m : ℂ → ℕ)
    (hD : ∀ N, (E N).card = D N)
    (hE : ∀ N, ConjStable (E N)) (hm : MultSymm m)
    (hm_pos : ∀ γ ∈ Λ, 0 < m γ)
    (hsub : ∀ N, ↑(E N) ⊆ Λ) (hcov : ∀ γ ∈ Λ, ∃ N, γ ∈ E N) :
    (∀ N, HankelFusionPosDef (E N) m (D N)) ↔ ∀ γ ∈ Λ, γ.im = 0 := by
  constructor
  · intro h γ hγ
    obtain ⟨N, hN⟩ := hcov γ hγ
    have hpos_N := h N
    exact (hankelFusion_posDef_iff_real (E N) m (hD N) (hE N) hm
      (fun δ hδ => hm_pos δ (hsub N hδ))).mp hpos_N γ hN
  · intro h N
    exact (hankelFusion_posDef_iff_real (E N) m (hD N) (hE N) hm
      (fun δ hδ => hm_pos δ (hsub N hδ))).mpr
      (fun γ hγ => h γ (hsub N hγ))

theorem hankel_posDef_all_iff_RH
    (Λ : Set ℂ) (E : ℕ → Finset ℂ) (D : ℕ → ℕ) (m : ℂ → ℕ) (RH : Prop)
    (hD : ∀ N, (E N).card = D N)
    (hE : ∀ N, ConjStable (E N)) (hm : MultSymm m)
    (hm_pos : ∀ γ ∈ Λ, 0 < m γ)
    (hsub : ∀ N, ↑(E N) ⊆ Λ) (hcov : ∀ γ ∈ Λ, ∃ N, γ ∈ E N)
    (hRH : RH ↔ ∀ γ ∈ Λ, γ.im = 0) :
    (∀ N, HankelFusionPosDef (E N) m (D N)) ↔ RH := by
  rw [hRH]
  exact hankel_posDef_all_iff_zeros_real Λ E D m hD hE hm hm_pos hsub hcov


theorem corollaire_orthogonale_equiv
    (Λ : Set ℂ) (E : ℕ → Finset ℂ) (D : ℕ → ℕ) (m : ℂ → ℕ) (RH : Prop)
    (OrthRec : ℕ → Prop)
    (hD : ∀ N, (E N).card = D N)
    (hE : ∀ N, ConjStable (E N)) (hm : MultSymm m)
    (hm_pos : ∀ γ ∈ Λ, 0 < m γ)
    (hsub : ∀ N, (E N : Set ℂ) ⊆ Λ) (hcov : ∀ γ ∈ Λ, ∃ N, γ ∈ E N)
    (_ : ∀ N, E N ⊆ E (N + 1))
    (hRH : RH ↔ ∀ γ ∈ Λ, γ.im = 0)
    (hFav : ∀ N, OrthRec N ↔ HankelFusionPosDef (E N) m (D N)) :
    List.TFAE
      [ (∀ N, OrthRec N),
        (∀ N, HankelFusionPosDef (E N) m (D N)),
        (∀ N, ∀ γ ∈ E N, γ.im = 0),
        RH ] := by
  have h23 : (∀ N, HankelFusionPosDef (E N) m (D N)) ↔ (∀ N, ∀ γ ∈ E N, γ.im = 0) := by
    constructor
    · intro h N γ hγ
      exact (hankelFusion_posDef_iff_real (E N) m (hD N) (hE N) hm
        (fun δ hδ => hm_pos δ (hsub N hδ))).mp (h N) γ hγ
    · intro h N
      exact (hankelFusion_posDef_iff_real (E N) m (hD N) (hE N) hm
        (fun δ hδ => hm_pos δ (hsub N hδ))).mpr (h N)
  have h12 : (∀ N, OrthRec N) ↔ (∀ N, HankelFusionPosDef (E N) m (D N)) :=
    ⟨fun h N => (hFav N).mp (h N), fun h N => (hFav N).mpr (h N)⟩
  have h34 : (∀ N, ∀ γ ∈ E N, γ.im = 0) ↔ RH := by
    rw [hRH]
    constructor
    · intro h γ hγ
      obtain ⟨N, hN⟩ := hcov γ hγ
      exact h N γ hN
    · intro h N γ hγ
      exact h γ (hsub N hγ)
  tfae_have 1 ↔ 2 := h12
  tfae_have 2 ↔ 3 := h23
  tfae_have 3 ↔ 4 := h34
  tfae_finish

theorem corollaire_simplicite
    (Λ : Set ℂ) (E : ℕ → Finset ℂ) (D : ℕ → ℕ) (m : ℂ → ℕ)
    (DiagReal : ℕ → Prop)
    (hD : ∀ N, (E N).card = D N)
    (hE : ∀ N, ConjStable (E N)) (hm : MultSymm m)
    (hm_pos : ∀ γ ∈ Λ, 0 < m γ)
    (hsub : ∀ N, (E N : Set ℂ) ⊆ Λ) (hcov : ∀ γ ∈ Λ, ∃ N, γ ∈ E N)
    (hDiag : ∀ N, DiagReal N ↔ ((∀ γ ∈ E N, γ.im = 0) ∧ ∀ γ ∈ E N, m γ = 1)) :
    ((∀ γ ∈ Λ, γ.im = 0) ∧ (∀ γ ∈ Λ, m γ = 1)) ↔
      (∀ N, DiagReal N ∧ HankelFusionPosDef (E N) m (D N)) := by
  constructor
  · rintro ⟨hreal, hsimple⟩ N
    have hrealN : ∀ γ ∈ E N, γ.im = 0 := fun γ hγ => hreal γ (hsub N hγ)
    refine ⟨(hDiag N).mpr ⟨hrealN, fun γ hγ => hsimple γ (hsub N hγ)⟩, ?_⟩
    exact (hankelFusion_posDef_iff_real (E N) m (hD N) (hE N) hm
      (fun δ hδ => hm_pos δ (hsub N hδ))).mpr hrealN
  · intro h
    refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
    · obtain ⟨N, hN⟩ := hcov γ hγ
      exact ((hDiag N).mp (h N).1).1 γ hN
    · obtain ⟨N, hN⟩ := hcov γ hγ
      exact ((hDiag N).mp (h N).1).2 γ hN


open ExhaustProp


theorem exhaustion_posDef_tfae (X : Exhaustion) (RH : Prop)
    (hRH : RH ↔ ∀ γ ∈ X.Λ, γ.im = 0) :
    List.TFAE
      [ (∀ N, HankelFusionPosDef (X.E N) X.m (X.D N)),
        (∀ N, ∀ γ ∈ X.E N, γ.im = 0),
        RH ] := by
  tfae_have 1 ↔ 2 := all_posDef_iff_real X
  tfae_have 2 ↔ 3 := (all_real_iff X).trans hRH.symm
  tfae_finish

theorem exhaustion_simplicite (X : Exhaustion) (DiagReal : ℕ → Prop)
    (hDiag : ∀ N, DiagReal N ↔
      ((∀ γ ∈ X.E N, γ.im = 0) ∧ ∀ γ ∈ X.E N, X.m γ = 1)) :
    ((∀ γ ∈ X.Λ, γ.im = 0) ∧ (∀ γ ∈ X.Λ, X.m γ = 1)) ↔
      (∀ N, DiagReal N ∧ HankelFusionPosDef (X.E N) X.m (X.D N)) := by
  constructor
  · rintro ⟨hreal, hsimple⟩ N
    have hrealN : ∀ γ ∈ X.E N, γ.im = 0 := fun γ hγ => hreal γ (X.hsub N hγ)
    exact ⟨(hDiag N).mpr ⟨hrealN, fun γ hγ => hsimple γ (X.hsub N hγ)⟩,
      (posDef_iff_real X N).mpr hrealN⟩
  · intro h
    refine ⟨fun γ hγ => ?_, fun γ hγ => ?_⟩
    · obtain ⟨N, hN⟩ := X.hcov γ hγ
      exact ((hDiag N).mp (h N).1).1 γ hN
    · obtain ⟨N, hN⟩ := X.hcov γ hγ
      exact ((hDiag N).mp (h N).1).2 γ hN






end PosHankelCritGlobal
