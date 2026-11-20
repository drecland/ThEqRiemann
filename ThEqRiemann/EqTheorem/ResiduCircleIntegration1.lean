import mathlib

import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.GeometricalZero

/-!  -/
namespace ResCircIntegration1

open Set Complex DefinitionsThEq GeoZero


lemma derivee_logarithmique_forme_normale
    (H ψ : ℂ → ℂ) (x_j : ℂ) (m_j : ℕ)
    (hψ_an : AnalyticAt ℂ ψ x_j)
    (hψ_nz : ψ x_j ≠ 0)
    (hHψ : H =ᶠ[nhds x_j] fun x => (x - x_j) ^ m_j * ψ x) :
    ∀ᶠ x in nhds x_j, x ≠ x_j →
      deriv H x / H x = (m_j : ℂ) / (x - x_j) + deriv ψ x / ψ x := by
  -- ψ différentiable sur tout un voisinage de x_j
  have hψ_diff_ev : ∀ᶠ x in nhds x_j, DifferentiableAt ℂ ψ x :=
    Complex.analyticAt_iff_eventually_differentiableAt.mp hψ_an
  -- ψ non nulle sur un voisinage (par continuité depuis ψ x_j ≠ 0)
  have hψ_ne_ev : ∀ᶠ x in nhds x_j, ψ x ≠ 0 :=
    hψ_an.continuousAt.eventually_ne hψ_nz
  filter_upwards [hHψ.eventually_nhds, hψ_diff_ev, hψ_ne_ev] with x hx_eq hψx_diff hψx_ne
  intro hx_ne
  -- H x = (x - x_j)^m_j * ψ x, via extraction du point central
  have hHx_eq : H x = (x - x_j) ^ m_j * ψ x :=
    extraction_point_central H ψ x_j m_j x hx_eq
  -- H différentiable en x
  have hH_diff : DifferentiableAt ℂ H x :=
    differentiabilite_H_locale H ψ x_j m_j x hψx_diff hx_eq
  -- les dérivées coïncident (fonctions égales sur un voisinage)
  have hderiv_eq : deriv H x = deriv (fun z => (z - x_j) ^ m_j * ψ z) x :=
    Filter.EventuallyEq.deriv_eq hx_eq
  -- calcul de la dérivée du produit
  have hderiv_prod :
      deriv (fun z => (z - x_j) ^ m_j * ψ z) x
        = (m_j : ℂ) * (x - x_j) ^ (m_j - 1) * ψ x + (x - x_j) ^ m_j * deriv ψ x :=
    deriv_produit_forme_normale ψ x_j m_j x hψx_diff
  have hxj_ne : (x - x_j) ≠ 0 := sub_ne_zero.mpr hx_ne
  rw [hderiv_eq, hderiv_prod, hHx_eq]
  -- distinction de cas sur m_j
  rcases eq_or_ne m_j 0 with hm0 | hm_ne
  · -- cas m_j = 0 : le terme polaire disparaît
    subst hm0
    simp
  · -- cas m_j ≠ 0 : identité algébrique générale
    exact identite_algebrique_deriv_log (x - x_j) (ψ x) (deriv ψ x) m_j hm_ne hxj_ne hψx_ne

lemma residu_terme_polaire_simple
    (x_j : ℂ) (k m_j : ℕ) (r : ℝ) (hr : 0 < r) :
    residu (fun z => (m_j : ℂ) * z ^ k / (z - x_j)) x_j r
      = (m_j : ℂ) * x_j ^ k := by
  unfold residu
  have hdiff : DifferentiableOn ℂ (fun z => (m_j : ℂ) * z ^ k)
      (Metric.closedBall x_j r) :=
    ((differentiable_const (m_j : ℂ)).mul (differentiable_pow k)).differentiableOn
  have hmem : x_j ∈ Metric.ball x_j r := Metric.mem_ball_self hr
  have hcauchy := hdiff.circleIntegral_sub_inv_smul hmem
  have heq : (fun z => (m_j : ℂ) * z ^ k / (z - x_j))
      = (fun z => (z - x_j)⁻¹ • ((m_j : ℂ) * z ^ k)) := by
    funext z
    rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, hcauchy, smul_eq_mul]
  field_simp


lemma residu_holomorphe_nul
    (φ : ℂ → ℂ) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (Metric.closedBall a r)) :
    residu φ a r = 0 := by
  unfold residu
  have hball_sub : Metric.ball a r ⊆ Metric.closedBall a r := Metric.ball_subset_closedBall
  have hclosure_sub : closure (Metric.ball a r) ⊆ Metric.closedBall a r :=
    Metric.closure_ball_subset_closedBall
  have hdcont : DiffContOnCl ℂ φ (Metric.ball a r) :=
    ⟨hφ.mono hball_sub, hφ.continuousOn.mono hclosure_sub⟩
  rw [hdcont.circleIntegral_eq_zero (le_of_lt hr)]
  simp

lemma residu_add
    (φ ψ : ℂ → ℂ) (a : ℂ) (r : ℝ)
    (hφ : CircleIntegrable φ a r) (hψ : CircleIntegrable ψ a r) :
    residu (fun z => φ z + ψ z) a r = residu φ a r + residu ψ a r := by
  unfold residu
  rw [circleIntegral.integral_add hφ hψ]
  ring

lemma decomposition_ponctuelle
    (f ψ : ℂ → ℂ) (w x_j : ℂ) (m_j k : ℕ) (x : ℂ)
    (_ : x ≠ x_j) (_ : ψ x ≠ 0)
    (heq : deriv f x / (f x - w) = (m_j : ℂ) / (x - x_j) + deriv ψ x / ψ x) :
    x ^ k * deriv f x / (f x - w)
      = (m_j : ℂ) * x ^ k / (x - x_j) + x ^ k * (deriv ψ x / ψ x) := by
  rw [show x ^ k * deriv f x / (f x - w) = x ^ k * (deriv f x / (f x - w)) by ring, heq]
  ring

lemma decomposition_sur_sphere
    (f ψ : ℂ → ℂ) (w x_j : ℂ) (m_j k : ℕ) (r : ℝ)
    (hclosedball_eq : ∀ x ∈ Metric.closedBall x_j r, x ≠ x_j →
      deriv f x / (f x - w) = (m_j : ℂ) / (x - x_j) + deriv ψ x / ψ x)
    (hψ_ne_closedball : ∀ x ∈ Metric.closedBall x_j r, ψ x ≠ 0) :
    Set.EqOn
      (fun x => x ^ k * deriv f x / (f x - w))
      (fun x => (m_j : ℂ) * x ^ k / (x - x_j) + x ^ k * (deriv ψ x / ψ x))
      (Metric.sphere x_j r \ {x_j}) := by
  intro x hx
  obtain ⟨hx_mem, hx_ne⟩ := hx
  simp only [Set.mem_singleton_iff] at hx_ne
  have hx_closedball : x ∈ Metric.closedBall x_j r := by
    rw [Metric.mem_sphere] at hx_mem
    rw [Metric.mem_closedBall]
    exact le_of_eq hx_mem
  exact decomposition_ponctuelle f ψ w x_j m_j k x hx_ne
    (hψ_ne_closedball x hx_closedball) (hclosedball_eq x hx_closedball hx_ne)


lemma xj_not_mem_sphere (x_j : ℂ) (r : ℝ) (hr : 0 < r) :
    x_j ∉ Metric.sphere x_j r := by
  intro h
  rw [Metric.mem_sphere, dist_self] at h
  linarith

lemma circleIntegral_congr_of_eqOn_sdiff
    (φ₁ φ₂ : ℂ → ℂ) (x_j : ℂ) (r : ℝ) (hr : 0 < r)
    (heqOn : Set.EqOn φ₁ φ₂ (Metric.sphere x_j r \ {x_j})) :
    (∮ z in C(x_j, r), φ₁ z) = ∮ z in C(x_j, r), φ₂ z := by
  apply circleIntegral.integral_congr (le_of_lt hr)
  intro x hx
  have hx_ne : x ≠ x_j := by
    intro h
    exact xj_not_mem_sphere x_j r hr (h ▸ hx)
  exact heqOn ⟨hx, hx_ne⟩

lemma residu_eq_of_decomposition
    (f ψ : ℂ → ℂ) (w x_j : ℂ) (m_j k : ℕ) (r : ℝ) (hr : 0 < r)
    (hclosedball_eq : ∀ x ∈ Metric.closedBall x_j r, x ≠ x_j →
      deriv f x / (f x - w) = (m_j : ℂ) / (x - x_j) + deriv ψ x / ψ x)
    (hψ_ne_closedball : ∀ x ∈ Metric.closedBall x_j r, ψ x ≠ 0) :
    residu (fun x => x ^ k * deriv f x / (f x - w)) x_j r
      = residu (fun x => (m_j : ℂ) * x ^ k / (x - x_j)
                  + x ^ k * (deriv ψ x / ψ x)) x_j r := by
  unfold residu
  congr 1
  exact circleIntegral_congr_of_eqOn_sdiff _ _ x_j r hr
    (decomposition_sur_sphere f ψ w x_j m_j k r hclosedball_eq hψ_ne_closedball)

lemma circleIntegrable_terme_polaire
    (x_j : ℂ) (m_j k : ℕ) (r : ℝ) (hr : 0 < r) :
    CircleIntegrable (fun x => (m_j : ℂ) * x ^ k / (x - x_j)) x_j r := by
  apply ContinuousOn.circleIntegrable (le_of_lt hr)
  apply ContinuousOn.div
  · exact (continuous_const.mul (continuous_pow k)).continuousOn
  · exact (continuous_id.sub continuous_const).continuousOn
  · intro x hx
    have hx_ne : x ≠ x_j := by
      intro h
      exact xj_not_mem_sphere x_j r hr (h ▸ hx)
    exact sub_ne_zero.mpr hx_ne


--------------------------------------------------------------------

lemma continuousOn_deriv_of_differentiableOn_of_subset_isOpen
    (ψ : ℂ → ℂ) (x_j : ℂ) (r : ℝ) (_ : 0 < r)
    (U : Set ℂ) (hU_open : IsOpen U)
    (hU_sub : Metric.closedBall x_j r ⊆ U)
    (hψ_diff : DifferentiableOn ℂ ψ U) :
    ContinuousOn (deriv ψ) (Metric.sphere x_j r) := by
  -- ψ holomorphe sur l'ouvert U ⟹ analytique sur U
  have hanalytic : AnalyticOnNhd ℂ ψ U :=
    hψ_diff.analyticOnNhd hU_open
  -- la dérivée d'une fonction analytique est analytique
  have hanalytic_deriv : AnalyticOnNhd ℂ (deriv ψ) U :=
    hanalytic.deriv
  -- une fonction analytique sur U est continue sur U
  have hcont_U : ContinuousOn (deriv ψ) U :=
    hanalytic_deriv.continuousOn
  -- la sphère est incluse dans U (car incluse dans closedBall ⊆ U)
  have hsphere_sub : Metric.sphere x_j r ⊆ U :=
    (Metric.sphere_subset_closedBall).trans hU_sub
  exact hcont_U.mono hsphere_sub

lemma circleIntegrable_terme_holomorphe
    (ψ : ℂ → ℂ) (x_j : ℂ) (r : ℝ) (hr : 0 < r) (k : ℕ)
    (U : Set ℂ) (hU_open : IsOpen U)
    (hU_sub : Metric.closedBall x_j r ⊆ U)
    (hψ_diff : DifferentiableOn ℂ ψ U)
    (hψ_ne_closedball : ∀ x ∈ Metric.closedBall x_j r, ψ x ≠ 0) :
    CircleIntegrable (fun x => x ^ k * (deriv ψ x / ψ x)) x_j r := by
  apply ContinuousOn.circleIntegrable (le_of_lt hr)
  have hderiv_cont : ContinuousOn (deriv ψ) (Metric.sphere x_j r) :=
    continuousOn_deriv_of_differentiableOn_of_subset_isOpen
      ψ x_j r hr U hU_open hU_sub hψ_diff
  have hψ_cont_sphere : ContinuousOn ψ (Metric.sphere x_j r) :=
    (hψ_diff.continuousOn).mono (Metric.sphere_subset_closedBall.trans hU_sub)
  apply ContinuousOn.mul
  · exact (continuous_pow k).continuousOn
  · apply ContinuousOn.div hderiv_cont hψ_cont_sphere
    intro x hx
    exact hψ_ne_closedball x (Metric.sphere_subset_closedBall hx)


lemma differentiableOn_terme_holomorphe
    (ψ : ℂ → ℂ) (x_j : ℂ) (r : ℝ) (_ : 0 < r) (k : ℕ)
    (U : Set ℂ) (hU_open : IsOpen U)
    (hU_sub : Metric.closedBall x_j r ⊆ U)
    (hψ_diff : DifferentiableOn ℂ ψ U)
    (hψ_ne_closedball : ∀ x ∈ Metric.closedBall x_j r, ψ x ≠ 0) :
    DifferentiableOn ℂ (fun x => x ^ k *
      (deriv ψ x / ψ x)) (Metric.closedBall x_j r) := by
  have hanalytic : AnalyticOnNhd ℂ ψ U := hψ_diff.analyticOnNhd hU_open
  have hanalytic_deriv : AnalyticOnNhd ℂ (deriv ψ) U := hanalytic.deriv
  have hderiv_diff_U : DifferentiableOn ℂ
    (deriv ψ) U := hanalytic_deriv.differentiableOn
  have hderiv_diff_closedball : DifferentiableOn ℂ
    (deriv ψ) (Metric.closedBall x_j r) :=
    hderiv_diff_U.mono hU_sub
  have hψ_diff_closedball : DifferentiableOn ℂ ψ (Metric.closedBall x_j r) :=
    hψ_diff.mono hU_sub
  apply DifferentiableOn.mul
  · exact (differentiable_pow k).differentiableOn
  · exact DifferentiableOn.div hderiv_diff_closedball
      hψ_diff_closedball hψ_ne_closedball


theorem residu_solution_moment
    (f ψ : ℂ → ℂ) (w x_j : ℂ) (m_j k : ℕ) (r : ℝ) (hr : 0 < r)
    (U : Set ℂ) (hU_open : IsOpen U) (hU_sub : Metric.closedBall x_j r ⊆ U)
    (_ : AnalyticAt ℂ ψ x_j)
    (_ : ψ x_j ≠ 0)
    (_ : (fun x => f x - w) =ᶠ[nhds x_j] fun x => (x - x_j) ^ m_j * ψ x)
    (hclosedball_eq : ∀ x ∈ Metric.closedBall x_j r, x ≠ x_j →
      deriv f x / (f x - w) = (m_j : ℂ) / (x - x_j) + deriv ψ x / ψ x)
    (hψ_diff : DifferentiableOn ℂ ψ U)
    (hψ_ne_closedball : ∀ x ∈ Metric.closedBall x_j r, ψ x ≠ 0) :
    residu (fun x => x ^ k * deriv f x / (f x - w)) x_j r
      = (m_j : ℂ) * x_j ^ k := by
  rw [residu_eq_of_decomposition f ψ w x_j m_j k r hr hclosedball_eq hψ_ne_closedball,
      residu_add _ _ x_j r
        (circleIntegrable_terme_polaire x_j m_j k r hr)
        (circleIntegrable_terme_holomorphe ψ x_j r hr k U hU_open hU_sub hψ_diff
          hψ_ne_closedball),
      residu_terme_polaire_simple x_j k m_j r hr]
  have hresidu_holo_nul :
      residu (fun x => x ^ k * (deriv ψ x / ψ x)) x_j r = 0 :=
    residu_holomorphe_nul _ x_j r hr
      (differentiableOn_terme_holomorphe ψ x_j r hr k U hU_open hU_sub hψ_diff
        hψ_ne_closedball)
  rw [hresidu_holo_nul, add_zero]

lemma forme_normale_de_pole
    (f : ℂ → ℂ) (p_q : ℂ) (n_q : ℕ)
    (hf_mero : MeromorphicAt f p_q)
    (hf_pole : meromorphicOrderAt f p_q = -(n_q : ℤ)) :
    ∃ φ : ℂ → ℂ, AnalyticAt ℂ φ p_q ∧ φ p_q ≠ 0 ∧
      f =ᶠ[nhdsWithin p_q {p_q}ᶜ]
        fun z => (z - p_q) ^ (meromorphicOrderAt f p_q).untop₀ • φ z := by
  have hne_top : meromorphicOrderAt f p_q ≠ ⊤ := by
    rw [hf_pole]
    exact WithTop.coe_ne_top
  exact (meromorphicOrderAt_ne_top_iff hf_mero).mp hne_top


lemma meromorphicAt_const_ℂ (w x : ℂ) : MeromorphicAt (fun _ : ℂ => w) x := by
  exact MeromorphicAt.const w x


lemma circleIntegrable_terme_polaire_pole
    (p_q : ℂ) (n_q k : ℕ) (r : ℝ) (hr : 0 < r) :
    CircleIntegrable (fun x => (-(n_q : ℂ)) * x ^ k / (x - p_q)) p_q r := by
  apply ContinuousOn.circleIntegrable (le_of_lt hr)
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_pow k)).continuousOn)
  · exact (continuous_id.sub continuous_const).continuousOn
  · intro x hx
    rw [Metric.mem_sphere] at hx
    exact sub_ne_zero.mpr (fun h => by simp [h] at hx; linarith [hr])


lemma decomposition_ponctuelle_pole
    (H φ : ℂ → ℂ) (p_q : ℂ) (n_q k : ℕ) (x : ℂ)
    (_ : x ≠ p_q) (_ : φ x ≠ 0)
    (heq : deriv H x / H x = (-(n_q : ℤ) : ℂ) / (x - p_q) + deriv φ x / φ x) :
    x ^ k * deriv H x / H x
      = (-(n_q : ℂ)) * x ^ k / (x - p_q) + x ^ k * (deriv φ x / φ x) := by
  rw [show x ^ k * deriv H x / H x = x ^ k * (deriv H x / H x) by ring, heq]
  norm_cast
  ring

lemma decomposition_sur_sphere_pole
    (H φ : ℂ → ℂ) (p_q : ℂ) (n_q k : ℕ) (r : ℝ) (_ : 0 < r)
    (hclosedball_eq : ∀ x ∈ Metric.closedBall p_q r, x ≠ p_q →
      deriv H x / H x = (-(n_q : ℤ) : ℂ) / (x - p_q) + deriv φ x / φ x)
    (hφ_ne_closedball : ∀ x ∈ Metric.closedBall p_q r, φ x ≠ 0) :
    Set.EqOn
      (fun x => x ^ k * deriv H x / H x)
      (fun x => (-(n_q : ℂ)) * x ^ k / (x - p_q) + x ^ k * (deriv φ x / φ x))
      (Metric.sphere p_q r \ {p_q}) := by
  intro x hx
  obtain ⟨hx_mem, hx_ne⟩ := hx
  simp only [Set.mem_singleton_iff] at hx_ne
  have hx_closedball : x ∈ Metric.closedBall p_q r := by
    rw [Metric.mem_sphere] at hx_mem
    rw [Metric.mem_closedBall]
    exact le_of_eq hx_mem
  have heq := hclosedball_eq x hx_closedball hx_ne
  exact decomposition_ponctuelle_pole H φ p_q n_q k x hx_ne
    (hφ_ne_closedball x hx_closedball) heq



lemma div_eq_smul_inv_terme_polaire
    (p_q : ℂ) (n_q k : ℕ) (x : ℂ) :
    (-(n_q : ℂ)) * x ^ k / (x - p_q) = (x - p_q)⁻¹ • ((-(n_q : ℂ)) * x ^ k) := by
  rw [smul_eq_mul, div_eq_mul_inv, mul_comm]


lemma fun_eq_smul_inv_terme_polaire
    (p_q : ℂ) (n_q k : ℕ) :
    (fun x => (-(n_q : ℂ)) * x ^ k / (x - p_q))
      = (fun x => (x - p_q)⁻¹ • ((-(n_q : ℂ)) * x ^ k)) := by
  funext x
  exact div_eq_smul_inv_terme_polaire p_q n_q k x


lemma differentiableOn_terme_polaire_numerateur
    (p_q : ℂ) (n_q k : ℕ) (r : ℝ) :
    DifferentiableOn ℂ (fun x => (-(n_q : ℂ)) * x ^ k) (Metric.closedBall p_q r) :=
  ((differentiable_const (-(n_q : ℂ))).mul (differentiable_pow k)).differentiableOn


lemma residu_terme_polaire_pole
    (p_q : ℂ) (n_q k : ℕ) (r : ℝ) (hr : 0 < r) :
    residu (fun x => (-(n_q : ℂ)) * x ^ k / (x - p_q)) p_q r
      = (-(n_q : ℂ)) * p_q ^ k := by
  unfold residu
  have hdiff := differentiableOn_terme_polaire_numerateur p_q n_q k r
  have hmem : p_q ∈ Metric.ball p_q r := Metric.mem_ball_self hr
  have hcauchy := hdiff.circleIntegral_sub_inv_smul hmem
  rw [fun_eq_smul_inv_terme_polaire p_q n_q k, hcauchy, smul_eq_mul]
  field_simp

lemma deriv_sub_const_eq (f : ℂ → ℂ) (w x : ℂ) :
    deriv (fun x => f x - w) x = deriv f x := by
  simp [deriv_sub_const]

lemma hclosedball_eq_shifted
    (f φ : ℂ → ℂ) (w p_q : ℂ) (n_q : ℕ) (r : ℝ)
    (hclosedball_eq : ∀ x ∈ Metric.closedBall p_q r, x ≠ p_q →
      deriv f x / (f x - w) = (-(n_q : ℤ) : ℂ) / (x - p_q) + deriv φ x / φ x) :
    ∀ x ∈ Metric.closedBall p_q r, x ≠ p_q →
      deriv (fun x => f x - w) x / (f x - w)
        = (-(n_q : ℤ) : ℂ) / (x - p_q) + deriv φ x / φ x := by
  intro x hx hxp
  rw [deriv_sub_const_eq f w x]
  exact hclosedball_eq x hx hxp

lemma hdecomp_shifted_to_f
    (f φ : ℂ → ℂ) (w p_q : ℂ) (n_q k : ℕ) (r : ℝ)
    (hdecomp : Set.EqOn
        (fun x => x ^ k * deriv (fun x => f x - w) x / (f x - w))
        (fun x => (-(n_q : ℂ)) * x ^ k / (x - p_q) + x ^ k * (deriv φ x / φ x))
        (Metric.sphere p_q r \ {p_q})) :
    Set.EqOn
      (fun x => x ^ k * deriv f x / (f x - w))
      (fun x => (-(n_q : ℂ)) * x ^ k / (x - p_q) + x ^ k * (deriv φ x / φ x))
      (Metric.sphere p_q r \ {p_q}) := by
  intro x hx
  have h := hdecomp hx
  simp only [deriv_sub_const_eq f w x] at h
  exact h

lemma mem_sphere_diff_point
    (p_q x : ℂ) (r : ℝ) (hx : x ∈ Metric.sphere p_q r) (hxp : x ≠ p_q) :
    x ∈ Metric.sphere p_q r \ {p_q} :=
  Set.mem_sdiff_of_mem hx (by simpa using hxp)


theorem residu_pole_moment
    (f φ : ℂ → ℂ) (w p_q : ℂ) (n_q k : ℕ) (r : ℝ) (hr : 0 < r) (_ : 0 < n_q)
    (U : Set ℂ) (hU_open : IsOpen U) (hU_sub : Metric.closedBall p_q r ⊆ U)
    (_ : meromorphicOrderAt f p_q = -(n_q : ℤ))
    (_ : AnalyticAt ℂ φ p_q)
    (_ : φ p_q ≠ 0)
    (_ : (fun x => f x - w) =ᶠ[nhds p_q]
            fun x => (x - p_q : ℂ) ^ (-(n_q : ℤ)) * φ x)
    (hclosedball_eq : ∀ x ∈ Metric.closedBall p_q r, x ≠ p_q →
      deriv f x / (f x - w) = (-(n_q : ℤ) : ℂ) / (x - p_q) + deriv φ x / φ x)
    (hφ_diff : DifferentiableOn ℂ φ U)
    (hφ_ne_closedball : ∀ x ∈ Metric.closedBall p_q r, φ x ≠ 0) :
    residu (fun x => x ^ k * deriv f x / (f x - w)) p_q r
      = (-(n_q : ℂ)) * p_q ^ k := by
  have hdecomp := decomposition_sur_sphere_pole (fun x => f x - w) φ p_q n_q k r hr
    (hclosedball_eq_shifted f φ w p_q n_q r hclosedball_eq) hφ_ne_closedball
  have hdecomp' := hdecomp_shifted_to_f f φ w p_q n_q k r hdecomp
  have hCI_pole := circleIntegrable_terme_polaire_pole p_q n_q k r hr
  have hCI_holo := circleIntegrable_terme_holomorphe φ p_q r hr k U hU_open hU_sub hφ_diff
    hφ_ne_closedball
  have hres_eq : residu (fun x => x ^ k * deriv f x / (f x - w)) p_q r
      = residu (fun x => (-(n_q : ℂ)) * x ^ k / (x - p_q)
                  + x ^ k * (deriv φ x / φ x)) p_q r := by
    unfold residu
    congr 1
    apply circleIntegral.integral_congr (le_of_lt hr)
    intro x hx
    by_cases hxp : x = p_q
    · exfalso
      rw [Metric.mem_sphere] at hx
      rw [hxp, dist_self] at hx
      linarith [hr]
    · exact hdecomp' (mem_sphere_diff_point p_q x r hx hxp)
  rw [hres_eq, residu_add _ _ p_q r hCI_pole hCI_holo,
      residu_terme_polaire_pole p_q n_q k r hr]
  have hresidu_holo_nul :
      residu (fun x => x ^ k * (deriv φ x / φ x)) p_q r = 0 :=
    residu_holomorphe_nul _ p_q r hr
      (differentiableOn_terme_holomorphe φ p_q r hr k U hU_open hU_sub hφ_diff
        hφ_ne_closedball)
  simp [hresidu_holo_nul]



lemma residu_const_mul (c : ℂ) (f : ℂ → ℂ) (a : ℂ) (r : ℝ) :
    residu (fun z => c * f z) a r = c * residu f a r := by
  unfold residu
  rw [circleIntegral.integral_const_mul]
  ring



end ResCircIntegration1
