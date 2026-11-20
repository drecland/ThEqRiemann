import mathlib
import ThEqRiemann.EqTheorem.DefThEq
/-! -/
namespace HarveyPolkingThEq

open Set Complex DefinitionsThEq


lemma masse_localement_finie_de_lelong
    {n : ℕ} (X : VarieteAnalytique n) {p : ℕ}
    (V : EnsembleAnalytiqueFerme X p) (z₀ : VarieteAnalytique n) :
    ∃ U ∈ nhds z₀, (courantIntegration V).masse U < ⊤ :=
  lelong_masse_localement_finie X V z₀

lemma masse_locale_lelong {n : ℕ} (X : VarieteAnalytique n) {p : ℕ}
    (Vbar : EnsembleAnalytiqueFerme X p) (z₀ : VarieteAnalytique n) :
    ∃ U ∈ nhds z₀, (courantIntegration Vbar).masse U < ⊤ :=
  masse_localement_finie_de_lelong X Vbar z₀

--------------------------------------------------------------------

lemma exists_open_nhds_disjoint_closure_V
    {f g : ℂ → ℂ} {Ω₁ Ω₂ : Set ℂ} {x₀ y₀ : ℂ}
    (h_not_mem : (x₀, y₀) ∉ closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
      z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0}) :
    ∃ U, IsOpen U ∧ (x₀, y₀) ∈ U ∧
      Disjoint U (closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
        z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0}) := by
  refine ⟨(closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
    z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0})ᶜ,
    isOpen_compl_iff.mpr isClosed_closure, h_not_mem, ?_⟩
  exact disjoint_compl_left

lemma preimage_isOpen_of_ofX_continuous
    {n : ℕ} (X : VarieteAnalytique n) {U : Set (ℂ × ℂ)} (hU : IsOpen U) :
    IsOpen (X.ofX ⁻¹' U) :=
  X.ofX_continuous.isOpen_preimage U hU

lemma disjoint_preimage_ofX_of_support_subset_closure
    {f g : ℂ → ℂ} {Ω₁ Ω₂ : Set ℂ}
    {n : ℕ} (X : VarieteAnalytique n) {p : ℕ} (Vbar : EnsembleAnalytiqueFerme X p)
    {U : Set (ℂ × ℂ)}
    (hU_disjoint : Disjoint U
      (closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
        z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0}))
    (h_support_subset_closure :
      X.ofX '' (courantIntegration Vbar).support ⊆
        closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
          z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0}) :
    Disjoint (X.ofX ⁻¹' U) (courantIntegration Vbar).support := by
  rw [Set.disjoint_left]
  intro x hxU hxsupp
  have h_image : X.ofX x ∈ X.ofX '' (courantIntegration Vbar).support :=
    Set.mem_image_of_mem X.ofX hxsupp
  have h_closure := h_support_subset_closure h_image
  exact Set.disjoint_left.mp hU_disjoint hxU h_closure

lemma masse_locale_lelong_ouvert {n : ℕ} (X : VarieteAnalytique n) {p : ℕ}
    (Vbar : EnsembleAnalytiqueFerme X p) (z₀ : VarieteAnalytique n) :
    ∃ W, IsOpen W ∧ z₀ ∈ W ∧ (courantIntegration Vbar).masse W < ⊤ := by
  obtain ⟨U, hU_nhds, hU_fin⟩ := masse_locale_lelong X Vbar z₀
  obtain ⟨W, hW_sub, hW_open, hW_mem⟩ := mem_nhds_iff.mp hU_nhds
  refine ⟨W, hW_open, hW_mem, ?_⟩
  calc (courantIntegration Vbar).masse W
      ≤ (courantIntegration Vbar).masse U :=
        Courant'.masse_mono (courantIntegration Vbar) hW_sub
    _ < ⊤ := hU_fin

-------------------------------------------------------------------

lemma masse_nulle_hors_indetermination
    {f g : ℂ → ℂ} {Ω₁ Ω₂ : Set ℂ} {x₀ y₀ : ℂ}
    (h_not_mem : (x₀, y₀) ∉ closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
      z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0})
    {n : ℕ} (X : VarieteAnalytique n) {p : ℕ}
    (Vbar : EnsembleAnalytiqueFerme X p)
    (h_support_subset_closure :
      X.ofX '' (courantIntegration Vbar).support ⊆
        closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
          z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0}) :
    ∃ U, IsOpen U ∧ (x₀, y₀) ∈ U ∧
      (courantIntegration Vbar).masse (X.ofX ⁻¹' U) = 0 := by
  obtain ⟨U, hU_open, hU_mem, hU_disjoint⟩ :=
    exists_open_nhds_disjoint_closure_V h_not_mem
  refine ⟨U, hU_open, hU_mem, ?_⟩
  have h_preimage_open : IsOpen (X.ofX ⁻¹' U) :=
    preimage_isOpen_of_ofX_continuous X hU_open
  have h_preimage_disjoint : Disjoint (X.ofX ⁻¹' U)
    (courantIntegration Vbar).support :=
    disjoint_preimage_ofX_of_support_subset_closure
      X Vbar hU_disjoint h_support_subset_closure
  exact masse_nulle_of_disjoint_support (courantIntegration Vbar)
    h_preimage_open h_preimage_disjoint

lemma masse_localement_finie_P_H
    {n : ℕ} (X : VarieteAnalytique n) {p : ℕ}
    (Vbar : EnsembleAnalytiqueFerme X p) (A : Set (VarieteAnalytique n))
    (hcas : ∀ x ∈ A,
      (∃ W, IsOpen W ∧ x ∈ W ∧ (courantIntegration Vbar).masse W < ⊤) ∨
      (∃ U, IsOpen U ∧ x ∈ U ∧ (courantIntegration Vbar).masse U = 0)) :
    ∀ x ∈ A, ∃ U ∈ nhds x, (courantIntegration Vbar).masse U < ⊤ := by
  intro x hx
  rcases hcas x hx with hfin | hnul
  · obtain ⟨W, hW_open, hxW, hW_fin⟩ := hfin
    exact ⟨W, mem_nhds_iff.mpr ⟨W, Subset.rfl, hW_open, hxW⟩, hW_fin⟩
  · obtain ⟨U, hU_open, hxU, hU_zero⟩ := hnul
    exact ⟨U, mem_nhds_iff.mpr ⟨U, Subset.rfl, hU_open, hxU⟩, by
    simp [hU_zero]⟩

lemma courantIntegration_positif_ferme {n : ℕ} (X : VarieteAnalytique n) {p : ℕ}
    (Vbar : EnsembleAnalytiqueFerme X p) :
    (courantIntegration Vbar).positif ∧ (courantIntegration Vbar).ferme :=
  lelong_theoreme X Vbar

lemma extension_harvey_polking_meromorphe {n : ℕ} (X : VarieteAnalytique n)
    {p : ℕ} (hp1 : 1 ≤ p) (Vbar : EnsembleAnalytiqueFerme X p)
    (A : Set (VarieteAnalytique n)) (hA_closed : IsClosed A)
    (hA_negligible : Prop)
    (hmasse_finie : ∀ x ∈ A, ∃ U ∈ nhds x, (courantIntegration Vbar).masse U < ⊤) :
    ∃! Pi0 : Courant' (VarieteAnalytique n) p Set.univ,
      Pi0.positif ∧ Pi0.ferme ∧
      Courant'.restrict (Ω' := Set.univ \ A) Set.sdiff_subset Pi0 =
      Courant'.restrict (Ω' := Set.univ \ A) Set.sdiff_subset
        (courantIntegration Vbar) := by
  obtain ⟨hT_pos, hT_ferme⟩ := courantIntegration_positif_ferme X Vbar
  exact harvey_polking_extension' (VarieteAnalytique n) p hp1 Set.univ isOpen_univ A
    (Set.subset_univ A) hA_closed hA_negligible (courantIntegration Vbar)
    hT_pos hT_ferme hmasse_finie




end HarveyPolkingThEq
