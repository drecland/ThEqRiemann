import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition

/-! -/
namespace ConvIntegration

open Set Complex
open RiemannDef


lemma differentiableOn_toSpanSingleton {U : Set ℂ} {f : ℂ → ℂ}
    (hfR : DifferentiableOn ℝ f U) :
    DifferentiableOn ℝ (fun a => ContinuousLinearMap.toSpanSingleton ℂ (f a)) U := by
  have hlin : Differentiable ℝ
      (fun c : ℂ => ContinuousLinearMap.toSpanSingleton ℂ c) := by
      let L : ℂ →ₗ[ℝ] (ℂ →L[ℂ] ℂ) :=
        { toFun := fun c => ContinuousLinearMap.toSpanSingleton ℂ c
          map_add' := fun c d => by ext; simp
          map_smul' := fun r c => by ext; simp }
      have hL : Differentiable ℝ (LinearMap.toContinuousLinearMap L) :=
        (LinearMap.toContinuousLinearMap L).differentiable
      exact hL
  exact hlin.comp_differentiableOn hfR

lemma Tspan_apply (c : ℂ) :
    Tspan c = ContinuousLinearMap.toSpanSingleton ℂ c := rfl

lemma fderiv_real_apply_of_differentiableAt {f : ℂ → ℂ} {a : ℂ}
    (hfa : DifferentiableAt ℂ f a) (v : ℂ) :
    (fderiv ℝ f a) v = v * deriv f a := by
  have h := hfa.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  rw [h.fderiv]
  simp [ContinuousLinearMap.restrictScalars]

lemma fderiv_toSpanSingleton_apply {f : ℂ → ℂ} {a : ℂ}
    (hfa : DifferentiableAt ℂ f a) (v : ℂ) :
    (fderiv ℝ (fun a => ContinuousLinearMap.toSpanSingleton ℂ (f a)) a) v =
    ContinuousLinearMap.toSpanSingleton ℂ (v * deriv f a) := by
  have hfun : (fun a => ContinuousLinearMap.toSpanSingleton ℂ (f a)) = fun a => Tspan (f a) := by
    funext a; rfl
  rw [hfun]
  have hfR : DifferentiableAt ℝ f a := hfa.restrictScalars ℝ
  have hcomp : HasFDerivAt (fun a => Tspan (f a)) (Tspan.comp (fderiv ℝ f a)) a :=
    Tspan.hasFDerivAt.comp a hfR.hasFDerivAt
  rw [hcomp.fderiv]
  simp [fderiv_real_apply_of_differentiableAt hfa v, Tspan_apply]

lemma fderiv_toSpanSingleton_symm {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {a : ℂ} (ha : a ∈ U) (x y : ℂ) :
    ((fderiv ℝ (fun a => ContinuousLinearMap.toSpanSingleton ℂ (f a)) a) x) y =
    ((fderiv ℝ (fun a => ContinuousLinearMap.toSpanSingleton ℂ (f a)) a) y) x := by
  have hfa : DifferentiableAt ℂ f a := hf.differentiableAt (hU.mem_nhds ha)
  rw [fderiv_toSpanSingleton_apply hfa x, fderiv_toSpanSingleton_apply hfa y]
  simp [ContinuousLinearMap.toSpanSingleton_apply]
  ring

lemma hasDerivAt_of_hasFDerivAt_toSpanSingleton {G : ℂ → ℂ} {c z : ℂ}
    (h : HasFDerivAt G (ContinuousLinearMap.toSpanSingleton ℂ c) z) :
    HasDerivAt G c z := by
  have h1 := h.hasDerivAt
  simpa using h1

lemma convex_bande : Convex ℝ {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2} := by
  have h_lower : Convex ℝ {z : ℂ | -(1/2 : ℝ) < z.re} :=
    convex_halfSpace_re_gt (-(1/2 : ℝ))
  have h_upper : Convex ℝ {z : ℂ | z.re < 1/2} :=
    convex_halfSpace_re_lt (1/2 : ℝ)
  have h_inter : Convex ℝ ({z : ℂ | -(1/2 : ℝ) < z.re} ∩ {z : ℂ | z.re < 1/2}) :=
    h_lower.inter h_upper
  exact h_inter

lemma differentiableOn_exists_primitive_convex {U : Set ℂ} (hU : IsOpen U)
    (hc : Convex ℝ U) {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    ∃ G : ℂ → ℂ, ∀ z ∈ U, HasDerivAt G (f z) z := by
  have hfR : DifferentiableOn ℝ f U := hf.restrictScalars ℝ
  have hω := differentiableOn_toSpanSingleton hfR
  have hsym : ∀ a ∈ U, ∀ x y : ℂ,
      ((fderiv ℝ (fun a => ContinuousLinearMap.toSpanSingleton ℂ (f a)) a) x) y =
      ((fderiv ℝ (fun a => ContinuousLinearMap.toSpanSingleton ℂ (f a)) a) y) x :=
    fun a ha x y => fderiv_toSpanSingleton_symm hU hf ha x y
  obtain ⟨G, hG⟩ := Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric hc hU hω hsym
  exact ⟨G, fun z hz => hasDerivAt_of_hasFDerivAt_toSpanSingleton (hG z hz)⟩

lemma isOpen_bande :
    IsOpen {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2} :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

lemma differentiableOn_exists_primitive_bande {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2}) :
    ∃ G : ℂ → ℂ, ∀ z ∈ {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2},
      HasDerivAt G (f z) z :=
  differentiableOn_exists_primitive_convex isOpen_bande convex_bande hf




lemma ball_subset_bande (t : ℝ) :
    Metric.ball ((Complex.I : ℂ) * (t : ℂ)) (1/2) ⊆
      {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2} := by
  intro z hz
  have h1 : |z.re| < 1/2 := by
    have h2 : |(z - Complex.I * (t : ℂ)).re| ≤ ‖z - Complex.I * (t : ℂ)‖ :=
      Complex.abs_re_le_norm _
    have h3 : (z - Complex.I * (t : ℂ)).re = z.re := by simp
    rw [h3] at h2
    have : ‖z - Complex.I * (t : ℂ)‖ < 1/2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    linarith
  exact ⟨by linarith [(abs_lt.mp h1).1], (abs_lt.mp h1).2⟩

lemma primitive_locale_bande {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | -(1/2 : ℝ) < z.re ∧ z.re < 1/2})
    (t : ℝ) :
    ∃ Φ : ℂ → ℂ, ∀ z ∈ Metric.ball ((Complex.I : ℂ) * (t : ℂ)) (1/2),
      HasDerivAt Φ (f z) z := by
  have hsub := ball_subset_bande t
  have hdiff : DifferentiableOn ℂ f (Metric.ball ((Complex.I : ℂ) * (t : ℂ)) (1/2)) :=
    hf.mono hsub
  obtain ⟨Φ, hΦ⟩ := hdiff.isExactOn_ball
  exact ⟨Φ, fun z hz => hΦ z hz⟩

lemma primitives_diff_constante {V : Set ℂ} (hV : IsOpen V)
    (hconn : IsPreconnected V)
    {G₁ G₂ f : ℂ → ℂ} (h₁ : ∀ z ∈ V, HasDerivAt G₁ (f z) z)
    (h₂ : ∀ z ∈ V, HasDerivAt G₂ (f z) z) :
    ∃ c : ℂ, ∀ z ∈ V, G₁ z = G₂ z + c := by
  rcases V.eq_empty_or_nonempty with hVe | ⟨z₀, hz₀⟩
  · exact ⟨0, fun z hz => by simp [hVe] at hz⟩
  have hH : ∀ z ∈ V, HasDerivAt (fun w => G₁ w - G₂ w) 0 z := by
    intro z hz
    have := (h₁ z hz).sub (h₂ z hz)
    convert this using 1
    simp []
  have hdiff : DifferentiableOn ℂ (fun w => G₁ w - G₂ w) V :=
    fun z hz => (hH z hz).differentiableAt.differentiableWithinAt
  have hderiv : V.EqOn (deriv (fun w => G₁ w - G₂ w)) 0 :=
    fun z hz => (hH z hz).deriv
  refine ⟨G₁ z₀ - G₂ z₀, fun z hz => ?_⟩
  have := hV.is_const_of_deriv_eq_zero hconn hdiff hderiv hz hz₀
  rw [← this]
  ring

lemma recollement_primitives' {V W : Set ℂ} (hV : IsOpen V) (hW : IsOpen W)
    (hVW : IsPreconnected (V ∩ W)) (_ : (V ∩ W).Nonempty) {f G₁ G₂ : ℂ → ℂ}
    (h₁ : ∀ z ∈ V, HasDerivAt G₁ (f z) z) (h₂ : ∀ z ∈ W, HasDerivAt G₂ (f z) z) :
    ∃ G : ℂ → ℂ, (∀ z ∈ V ∪ W, HasDerivAt G (f z) z) ∧ (∀ z ∈ V, G z = G₁ z) := by
  classical
  obtain ⟨c, hc⟩ := primitives_diff_constante (hV.inter hW) hVW
    (fun z hz => h₁ z hz.1) (fun z hz => h₂ z hz.2)
  have hGV : ∀ z ∈ V, (if z ∈ V then G₁ z else G₂ z + c) = G₁ z :=
    fun z hz => ite_eq_left hz
  have hGW : ∀ z ∈ W, (if z ∈ V then G₁ z else G₂ z + c) = G₂ z + c := by
    intro z hz
    by_cases hzV : z ∈ V
    · rw [ite_eq_left hzV]; exact hc z ⟨hzV, hz⟩
    · rw [ite_eq_right hzV]
  refine ⟨fun z => if z ∈ V then G₁ z else G₂ z + c, ?_, hGV⟩
  intro z hz
  rcases hz with hzV | hzW
  · have hev : G₁ =ᶠ[nhds z] (fun w => if w ∈ V then G₁ w else G₂ w + c) :=
      Filter.eventually_of_mem (hV.mem_nhds hzV) (fun w hw => (hGV w hw).symm)
    exact (h₁ z hzV).congr_of_eventuallyEq hev.symm
  · have hev : (fun w => G₂ w + c) =ᶠ[nhds z] (fun w => if w ∈ V then G₁ w else G₂ w + c) :=
      Filter.eventually_of_mem (hW.mem_nhds hzW) (fun w hw => (hGW w hw).symm)
    exact ((h₂ z hzW).add_const c).congr_of_eventuallyEq hev.symm


end ConvIntegration
