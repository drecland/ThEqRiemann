import mathlib
import ThEqRiemann.EqTheorem.DefThEq

/-! -/
namespace IndeterminationSetThEq

open Set Complex DefinitionsThEq


lemma order_nonneg_of_not_pole
    {g : ℂ → ℂ} {Ω₂ : Set ℂ} (_ : MeromorphicOn g Ω₂)
    {y₀ : ℂ} (hy₀ : y₀ ∈ Ω₂)
    (hy₀_not_pole : y₀ ∉ poles g Ω₂) :
    0 ≤ meromorphicOrderAt g y₀ := by
  by_contra h
  push Not at h
  have : y₀ ∈ poles g Ω₂ := by
    rw [poles]
    exact ⟨hy₀, h⟩
  exact hy₀_not_pole this

lemma continuousAt_norm_of_analyticAt
    {g : ℂ → ℂ} {y₀ : ℂ}
    (hanalytic : AnalyticAt ℂ g y₀) :
    ContinuousAt (fun y => ‖g y‖) y₀ :=
  hanalytic.continuousAt.norm

lemma norm_add_one_pos (f : ℂ → ℂ) (y₀ : ℂ) :
    0 < ‖f y₀‖ + 1 := by
  have h1 : 0 ≤ ‖f y₀‖ := norm_nonneg (f y₀)
  linarith

lemma extract_bounded_from_strict
    {f : ℂ → ℂ} {y₀ : ℂ} {V : Set ℂ} {M : ℝ}
    (hV_nhds : V ∈ nhds y₀)
    (hV_bound : ∀ y ∈ V, ‖f y‖ < M)
    (hM_pos : 0 < M) :
    ∃ V' ∈ nhds y₀, ∃ M' > 0, ∀ y ∈ V', ‖f y‖ ≤ M' := by
  exact ⟨V, hV_nhds, M, hM_pos, fun y hy =>
    le_of_lt (hV_bound y hy)⟩

lemma exists_bounded_nhds_of_continuousAt_norm
    {f : ℂ → ℂ} {y₀ : ℂ}
    (hcont : ContinuousAt (fun y => ‖f y‖) y₀) :
    ∃ V ∈ nhds y₀, ∃ M > 0, ∀ y ∈ V, ‖f y‖ ≤ M := by
  have hε : ∃ V ∈ nhds y₀, ∀ y ∈ V, ‖f y‖ < ‖f y₀‖ + 1 := by
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ_pos, hδ⟩ := hcont 1 (by norm_num)
    refine ⟨Metric.ball y₀ δ,
      Metric.ball_mem_nhds y₀ hδ_pos, fun y hy => ?_⟩
    rw [Metric.mem_ball] at hy
    have : |‖f y‖ - ‖f y₀‖| < 1 := by
      rw [← Real.dist_eq]
      exact hδ (by simpa [Metric.mem_ball] using hy)
    linarith [abs_sub_lt_iff.mp this]
  obtain ⟨V, hV_nhds, hV_bound⟩ := hε
  have hM_pos : 0 < ‖f y₀‖ + 1 := norm_add_one_pos f y₀
  exact extract_bounded_from_strict hV_nhds hV_bound hM_pos

lemma bounded_near_of_not_pole
    {g : ℂ → ℂ} {Ω₂ : Set ℂ} (hg : MeromorphicOn g Ω₂)
    {y₀ : ℂ} (hy₀ : y₀ ∈ Ω₂) (hy₀_not_pole : y₀ ∉ poles g Ω₂) :
    ∃ V ∈ nhds y₀, ∃ M > 0, ∀ y ∈ V, ‖g y‖ ≤ M := by
  have horder : 0 ≤ meromorphicOrderAt g y₀ :=
    order_nonneg_of_not_pole hg hy₀ hy₀_not_pole
  have hanalytic : AnalyticAt ℂ g y₀ :=
    canonical_extension hg y₀ hy₀ horder
  have hcont : ContinuousAt (fun y => ‖g y‖) y₀ :=
    continuousAt_norm_of_analyticAt hanalytic
  exact exists_bounded_nhds_of_continuousAt_norm hcont

lemma large_near_pole
    {f : ℂ → ℂ} {Ω₁ : Set ℂ} (hf : MeromorphicOn f Ω₁)
    {x₀ : ℂ} (hx₀ : x₀ ∈ poles f Ω₁) (M : ℝ) :
    ∃ V ∈ nhdsWithin x₀ {x₀}ᶜ, ∀ x ∈ V, M < ‖f x‖ := by
  have hx₀_ensemble : x₀ ∈ ensemblePoles f Ω₁ := by
    rw [← poles_eq_ensemblePoles hf]
    exact hx₀
  obtain ⟨_, hlim⟩ := hx₀_ensemble
  have hev : ∀ᶠ x in nhdsWithin x₀ {x₀}ᶜ, M < ‖f x‖ :=
    hlim.eventually (Filter.eventually_gt_atTop M)
  exact ⟨{x : ℂ | M < ‖f x‖}, hev, fun x hx => hx⟩


lemma ne_zero_of_norm_ne
    {f g : ℂ → ℂ} {x y : ℂ} (h : ‖f x‖ ≠ ‖g y‖) :
    f x - g y ≠ 0 := by
  intro heq
  apply h
  have : f x = g y := sub_eq_zero.mp heq
  rw [this]

lemma nhdsWithin_punctured_to_nhds
    {x₀ : ℂ} {V : Set ℂ}
    (hV : V ∈ nhdsWithin x₀ {x₀}ᶜ) :
    V ∪ {x₀} ∈ nhds x₀ := by
  obtain ⟨U, hU, hUV⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hV
  apply Filter.mem_of_superset hU
  intro x hx
  by_cases hxx : x = x₀
  · exact Or.inr (by simp [hxx])
  · exact Or.inl (hUV ⟨hx, hxx⟩)

lemma disjoint_of_pole_bound
    {f g : ℂ → ℂ} {Ω₁ Ω₂ : Set ℂ} {x₀ : ℂ} {Vx Vy : Set ℂ} {M : ℝ}
    (hx₀_pole : x₀ ∈ poles f Ω₁)
    (hVx_bound : ∀ x ∈ Vx, M < ‖f x‖)
    (hVy_bound : ∀ y ∈ Vy, ‖g y‖ ≤ M) :
    Disjoint ((Vx ∪ {x₀}) ×ˢ Vy)
      {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
        z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0} := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ ⟨hxW, hyW⟩ ⟨_, _, hxnp, _, hzero⟩
  by_cases hxx : x = x₀
  · exact hxnp (hxx ▸ hx₀_pole)
  · have hxV : x ∈ Vx := hxW.resolve_right
      (fun h => hxx (Set.mem_singleton_iff.mp h))
    have hfx : M < ‖f x‖ := hVx_bound x hxV
    have hgy : ‖g y‖ ≤ M := hVy_bound y hyW
    exact ne_zero_of_norm_ne (by linarith : ‖f x‖ ≠ ‖g y‖) hzero


lemma not_mem_closure_V_of_pole_not_indet
    {f g : ℂ → ℂ} {Ω₁ Ω₂ : Set ℂ}
    (hf : MeromorphicOn f Ω₁) (hg : MeromorphicOn g Ω₂)
    {x₀ y₀ : ℂ} (hx₀_pole : x₀ ∈ poles f Ω₁)
    (hy₀_not_pole : y₀ ∈ Ω₂ ∧ y₀ ∉ poles g Ω₂) :
    (x₀, y₀) ∉ closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
      z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0} := by
  obtain ⟨hy₀, hy₀_not_pole'⟩ := hy₀_not_pole
  obtain ⟨Vy, hVy, M, _, hVy_bound⟩ :=
    bounded_near_of_not_pole hg hy₀ hy₀_not_pole'
  obtain ⟨Vx, hVx, hVx_bound⟩ := large_near_pole hf hx₀_pole M
  have hVx_nhds : Vx ∪ {x₀} ∈ nhds x₀ :=
    nhdsWithin_punctured_to_nhds hVx
  have hW_nhds : ((Vx ∪ {x₀}) ×ˢ Vy) ∈ nhds (x₀, y₀) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hVx_nhds hVy
  have hW_disjoint :
      Disjoint ((Vx ∪ {x₀}) ×ˢ Vy)
        {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
          z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0} :=
    disjoint_of_pole_bound hx₀_pole hVx_bound hVy_bound
  intro hcl
  rw [mem_closure_iff_nhds] at hcl
  obtain ⟨z, hzW, hzS⟩ := hcl _ hW_nhds
  exact Set.disjoint_left.mp hW_disjoint hzW hzS


lemma disjoint_of_pole_bound'
    {f g : ℂ → ℂ} {Ω₁ Ω₂ : Set ℂ} {y₀ : ℂ} {Vx Vy : Set ℂ} {M : ℝ}
    (hy₀_pole : y₀ ∈ poles g Ω₂)
    (hVx_bound : ∀ x ∈ Vx, ‖f x‖ ≤ M)
    (hVy_bound : ∀ y ∈ Vy, M < ‖g y‖) :
    Disjoint (Vx ×ˢ (Vy ∪ {y₀}))
      {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
        z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0} := by
  rw [Set.disjoint_left]
  rintro ⟨x, y⟩ ⟨hxW, hyW⟩ ⟨_, _, _, hynp, hzero⟩
  by_cases hyy : y = y₀
  · exact hynp (hyy ▸ hy₀_pole)
  · have hyV : y ∈ Vy := hyW.resolve_right
      (fun h => hyy (Set.mem_singleton_iff.mp h))
    have hgy : M < ‖g y‖ := hVy_bound y hyV
    have hfx : ‖f x‖ ≤ M := hVx_bound x hxW
    exact ne_zero_of_norm_ne (by linarith : ‖f x‖ ≠ ‖g y‖) hzero

lemma not_mem_closure_V_of_pole_not_indet'
    {f g : ℂ → ℂ} {Ω₁ Ω₂ : Set ℂ}
    (hf : MeromorphicOn f Ω₁) (hg : MeromorphicOn g Ω₂)
    {x₀ y₀ : ℂ} (hx₀_not_pole : x₀ ∈ Ω₁ ∧ x₀ ∉ poles f Ω₁)
    (hy₀_pole : y₀ ∈ poles g Ω₂) :
    (x₀, y₀) ∉ closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
      z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0} := by
  obtain ⟨hx₀, hx₀_not_pole'⟩ := hx₀_not_pole
  obtain ⟨Vx, hVx, M, _, hVx_bound⟩ :=
    bounded_near_of_not_pole hf hx₀ hx₀_not_pole'
  obtain ⟨Vy, hVy, hVy_bound⟩ := large_near_pole hg hy₀_pole M
  have hVy_nhds : Vy ∪ {y₀} ∈ nhds y₀ :=
    nhdsWithin_punctured_to_nhds hVy
  have hW_nhds : (Vx ×ˢ (Vy ∪ {y₀})) ∈ nhds (x₀, y₀) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hVx hVy_nhds
  have hW_disjoint :
      Disjoint (Vx ×ˢ (Vy ∪ {y₀}))
        {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
          z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0} :=
    disjoint_of_pole_bound' hy₀_pole hVx_bound hVy_bound
  intro hcl
  rw [mem_closure_iff_nhds] at hcl
  obtain ⟨z, hzW, hzS⟩ := hcl _ hW_nhds
  exact Set.disjoint_left.mp hW_disjoint hzW hzS


lemma non_accumulation_poles
    {f g : ℂ → ℂ} {Ω₁ Ω₂ : Set ℂ}
    (hf : MeromorphicOn f Ω₁) (hg : MeromorphicOn g Ω₂) :
    Disjoint
      (closure {z : ℂ × ℂ | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
        z.1 ∉ poles f Ω₁ ∧ z.2 ∉ poles g Ω₂ ∧ f z.1 - g z.2 = 0})
      (((poles f Ω₁ ×ˢ Ω₂) ∪ (Ω₁ ×ˢ poles g Ω₂)) \
        (poles f Ω₁ ×ˢ poles g Ω₂)) := by
  rw [Set.disjoint_left]
  intro z hzclosure hzoutside
  obtain ⟨hzunion, hznotboth⟩ := hzoutside
  rcases hzunion with hzleft | hzright
  · have hx_pole : z.1 ∈ poles f Ω₁ := hzleft.1
    have hy_Ω₂ : z.2 ∈ Ω₂ := hzleft.2
    have hy_not_pole : z.2 ∉ poles g Ω₂ :=
      fun hy_pole => hznotboth ⟨hx_pole, hy_pole⟩
    exact not_mem_closure_V_of_pole_not_indet
      hf hg hx_pole ⟨hy_Ω₂, hy_not_pole⟩ hzclosure
  · have hx_Ω₁ : z.1 ∈ Ω₁ := hzright.1
    have hy_pole : z.2 ∈ poles g Ω₂ := hzright.2
    have hx_not_pole : z.1 ∉ poles f Ω₁ := fun hx_pole =>
      hznotboth ⟨hx_pole, hy_pole⟩
    exact not_mem_closure_V_of_pole_not_indet'
      hf hg ⟨hx_Ω₁, hx_not_pole⟩ hy_pole hzclosure





end IndeterminationSetThEq
