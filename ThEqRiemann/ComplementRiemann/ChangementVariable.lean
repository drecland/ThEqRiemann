import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition

/-! -/
namespace ChangementVar

open Set Complex intervalIntegral Real


theorem changement_variable_cercle
    {c : ℂ} {R : ℝ} (hR : 0 < R) {φ f : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hφ : DifferentiableOn ℂ φ U)
    (hcU : Metric.sphere c R ⊆ U)
    (_ : ∀ z ∈ Metric.sphere c R, φ z ∈ V) :
    ∫ t in (0 : ℝ)..2 * π,
        (φ (circleMap c R t) *
          (deriv f (φ (circleMap c R t)) / f (φ (circleMap c R t)))) *
          deriv (fun s => φ (circleMap c R s)) t
      = ∮ z in C(c, R),
          φ z * (deriv f (φ z) / f (φ z)) * deriv φ z := by
  rw [circleIntegral]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  have hz : circleMap c R t ∈ U := hcU (circleMap_mem_sphere c hR.le t)
  have hφd : HasDerivAt φ (deriv φ (circleMap c R t)) (circleMap c R t) :=
    (hφ.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have hcircle : HasDerivAt (circleMap c R) (circleMap 0 R t * Complex.I) t :=
    hasDerivAt_circleMap c R t
  have hcomp : HasDerivAt (fun s => φ (circleMap c R s))
      ((circleMap 0 R t * Complex.I) • deriv φ (circleMap c R t)) t :=
    hφd.scomp t hcircle
  rw [smul_eq_mul] at hcomp
  rw [hcomp.deriv, deriv_circleMap, smul_eq_mul]
  ring

theorem changement_variable_moments
    {a b : ℝ} {γ : ℝ → ℂ} {φ f : ℂ → ℂ} {U V : Set ℂ}
    (hγ : ContDiff ℝ 1 γ) (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U)
    (_ : DifferentiableOn ℂ f V) (_ : ∀ t ∈ Set.uIcc a b, φ (γ t) ∈ V)
    (_ : ∀ t ∈ Set.uIcc a b, f (φ (γ t)) ≠ 0) :
    ∫ t in a..b, (φ (γ t) * (deriv f (φ (γ t)) / f (φ (γ t)))) * deriv (φ ∘ γ) t
      = ∫ t in a..b, (φ (γ t) * (deriv f (φ (γ t)) / f (φ (γ t)))) *
          (deriv φ (γ t) * deriv γ t) := by
  apply intervalIntegral.integral_congr
  intro t ht
  simp only
  have hφd : HasDerivAt φ (deriv φ (γ t)) (γ t) :=
    (hφ.differentiableAt (hU.mem_nhds (hγU t ht))).hasDerivAt
  have hγd : HasDerivAt γ (deriv γ t) t :=
    ((hγ.differentiable one_ne_zero) t).hasDerivAt
  have hcomp : HasDerivAt (φ ∘ γ) (deriv γ t • deriv φ (γ t)) t :=
    hφd.scomp t hγd
  rw [hcomp.deriv, smul_eq_mul]
  ring

theorem ChangementVariableMoments
    {a b : ℝ} {γ : ℝ → ℂ} {φ f : ℂ → ℂ} {U V : Set ℂ}
    (hγ : ContDiff ℝ 1 γ) (hU : IsOpen U)
    (hφ : DifferentiableOn ℂ φ U) (hγU : ∀ t ∈ Set.uIcc a b, γ t ∈ U)
    (hf : DifferentiableOn ℂ f V) (hφV : ∀ t ∈ Set.uIcc a b, φ (γ t) ∈ V)
    (hf0 : ∀ t ∈ Set.uIcc a b, f (φ (γ t)) ≠ 0) :
    -- integrale on 𝒞₂ = φ ∘ γ
    ∫ t in a..b, ((φ ∘ γ) t * (deriv f ((φ ∘ γ) t) / f ((φ ∘ γ) t))) * deriv (φ ∘ γ) t
      -- integrale on 𝒞₁ with φ'(z) dz
      = ∫ t in a..b, (φ (γ t) * (deriv f (φ (γ t)) / f (φ (γ t)))) *
          (deriv φ (γ t) * deriv γ t) :=
  changement_variable_moments hγ hU hφ hγU hf hφV hf0

theorem intervalIntegral_reparam_periodic
    (f : ℝ → ℂ) (hf : Continuous f) (hper : Function.Periodic f (2 * π))
    (ψ ψ' : ℝ → ℝ) (hψd : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψc : Continuous ψ') (hψend : ψ (2 * π) = ψ 0 + 2 * π) :
    ∫ t in (0 : ℝ)..(2 * π), f (ψ t) * (ψ' t : ℂ)
      = ∫ t in (0 : ℝ)..(2 * π), f t := by
  set G : ℝ → ℂ := fun x => ∫ t in (0 : ℝ)..x, f t with hG
  have hGd : ∀ x, HasDerivAt G (f x) x := fun x =>
    (hf.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hcomp : ∀ t, HasDerivAt (fun t => G (ψ t)) (f (ψ t) * (ψ' t : ℂ)) t := by
    intro t
    have h1 := (hGd (ψ t)).scomp t (hψd t)
    have h2 : f (ψ t) * (ψ' t : ℂ) = ψ' t • f (ψ t) := by
      rw [Complex.real_smul, mul_comm]
    rw [h2]
    exact h1
  have hψcont : Continuous ψ :=
    continuous_iff_continuousAt.2 (fun t => (hψd t).continuousAt)
  have hint_ok : IntervalIntegrable (fun t => f (ψ t) * (ψ' t : ℂ))
      MeasureTheory.volume 0 (2 * π) :=
    ((hf.comp hψcont).mul (Complex.continuous_ofReal.comp hψc)).intervalIntegrable _ _
  have hint : ∫ t in (0 : ℝ)..(2 * π), f (ψ t) * (ψ' t : ℂ)
      = G (ψ (2 * π)) - G (ψ 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hcomp t) hint_ok
  rw [hint, hψend]
  have hdiff : G (ψ 0 + 2 * π) - G (ψ 0) = ∫ t in ψ 0..(ψ 0 + 2 * π), f t := by
    simp only [hG]
    rw [intervalIntegral.integral_interval_sub_left] <;>
      exact hf.intervalIntegrable _ _
  rw [hdiff, hper.intervalIntegral_add_eq (ψ 0) 0]
  simp

theorem circleIntegral_chgt_var_final (c₁ c₂ : ℂ) (ε : ℝ) (G M : ℂ → ℂ)
    (ψ ψ' : ℝ → ℝ)
    (hΓ : ∀ t, M (circleMap c₁ ε t) = circleMap c₂ ε (ψ t))
    (hψd : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hchain : ∀ t, deriv (fun s => circleMap c₂ ε (ψ s)) t
      = deriv M (circleMap c₁ ε t) * deriv (circleMap c₁ ε) t)
    (key : ∫ t in (0 : ℝ)..(2 * π),
        G (circleMap c₂ ε (ψ t)) * deriv (circleMap c₂ ε) (ψ t) * (ψ' t : ℂ)
      = ∫ t in (0 : ℝ)..(2 * π), G (circleMap c₂ ε t) * deriv (circleMap c₂ ε) t) :
    ∮ w in C(c₂, ε), G w = ∮ z in C(c₁, ε), G (M z) * deriv M z := by
  have hchain2 : ∀ t, deriv (fun s => circleMap c₂ ε (ψ s)) t
      = deriv (circleMap c₂ ε) (ψ t) * (ψ' t : ℂ) := by
    intro t
    have h1 : HasDerivAt (circleMap c₂ ε) (deriv (circleMap c₂ ε) (ψ t)) (ψ t) :=
      (hasDerivAt_circleMap c₂ ε (ψ t)).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun s => circleMap c₂ ε (ψ s))
        (ψ' t • deriv (circleMap c₂ ε) (ψ t)) t :=
      h1.scomp t (hψd t)
    rw [h2.deriv, Complex.real_smul, mul_comm]
  have hpt : ∀ t, deriv (circleMap c₁ ε) t • (G (M (circleMap c₁ ε t)) * deriv M (circleMap c₁ ε t))
      = G (circleMap c₂ ε (ψ t)) * deriv (circleMap c₂ ε) (ψ t) * (ψ' t : ℂ) := by
    intro t
    have e2 : deriv (circleMap c₂ ε) (ψ t) * (ψ' t : ℂ)
        = deriv M (circleMap c₁ ε t) * deriv (circleMap c₁ ε) t := by
      rw [← hchain2 t, hchain t]
    rw [hΓ t, smul_eq_mul]
    linear_combination (-(G (circleMap c₂ ε (ψ t)))) * e2
  simp only [circleIntegral]
  calc ∫ t in (0:ℝ)..(2*π), deriv (circleMap c₂ ε) t • G (circleMap c₂ ε t)
      = ∫ t in (0:ℝ)..(2*π), G (circleMap c₂ ε t) * deriv (circleMap c₂ ε) t := by
        congr 1; funext t; rw [smul_eq_mul, mul_comm]
    _ = ∫ t in (0:ℝ)..(2*π),
          G (circleMap c₂ ε (ψ t)) * deriv (circleMap c₂ ε) (ψ t) * (ψ' t : ℂ) := key.symm
    _ = _ := by congr 1; funext t; exact (hpt t).symm








end ChangementVar
