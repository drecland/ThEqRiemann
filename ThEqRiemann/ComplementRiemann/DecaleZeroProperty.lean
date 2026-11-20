import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.XiEntiereProp
import ThEqRiemann.RiemannProof.XiDecaleProp
import ThEqRiemann.ComplementRiemann.ExistenceIsolatedZero
import ThEqRiemann.ComplementRiemann.RealPartCaracterisation
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.ObservableAnalytiqueSelection
import ThEqRiemann.EqTheorem.Vandermonde
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2
/-! -/
namespace DecaleZeroProp

open Set Complex
open RiemannDef ExistIsolatedZero
open XiDecalePropRiemann XiEntiereRiemann


lemma exists_voisinage_symetrique (zm : ℂ) (hzm : zm ∈ zerosXiDecale)
    (hre : |zm.re| < 1 / 2) :
    ∃ U : Set ℂ, zm ∈ U ∧ (∀ z ∈ U, -(starRingEnd ℂ) z ∈ U) ∧
      (∀ z ∈ zerosXiDecale, z ∈ U → z = zm ∨ z = -(starRingEnd ℂ) zm) := by
  have hdist : ∀ a b : ℂ,
      dist (-(starRingEnd ℂ) a) (-(starRingEnd ℂ) b) = dist a b := by
    intro a b
    have h : -(starRingEnd ℂ) a - -(starRingEnd ℂ) b = (starRingEnd ℂ) (b - a) := by
      simp [map_sub]
      ring
    rw [dist_eq_norm, dist_eq_norm, h, Complex.norm_conj, norm_sub_rev]
  have hinv : ∀ a : ℂ, -(starRingEnd ℂ) (-(starRingEnd ℂ) a) = a := by
    intro a; simp
  obtain ⟨R, hR, -, -, huniq, -⟩ := exists_contour_zero_isole
    (f := xiDecale) hre (xiDecale_differentiable.analyticAt zm) hzm
    (xiDecale_not_eventually_zero zm)
  refine ⟨Metric.ball zm R ∪ Metric.ball (-(starRingEnd ℂ) zm) R,
    Or.inl (Metric.mem_ball_self hR), ?_, ?_⟩
  · intro z hz
    rcases hz with hz | hz
    · right
      rw [Metric.mem_ball] at hz ⊢
      rw [← hdist] at hz
      exact hz
    · left
      rw [Metric.mem_ball] at hz ⊢
      have h := hdist z (-(starRingEnd ℂ) zm)
      rw [hinv] at h
      linarith
  · intro z hz hzU
    rcases hzU with hzU | hzU
    · left
      exact huniq z (Metric.ball_subset_closedBall hzU) hz
    · right
      have hσz : -(starRingEnd ℂ) z ∈ zerosXiDecale :=
        zerosXiDecale_neg _ (zerosXiDecale_conj _ hz)
      have hσball : -(starRingEnd ℂ) z ∈ Metric.ball zm R := by
        rw [Metric.mem_ball] at hzU ⊢
        have h := hdist z (-(starRingEnd ℂ) zm)
        rw [hinv] at h
        linarith
      have := huniq _ (Metric.ball_subset_closedBall hσball) hσz
      calc z = -(starRingEnd ℂ) (-(starRingEnd ℂ) z) := (hinv z).symm
        _ = -(starRingEnd ℂ) zm := by rw [this]

lemma synthese_contour_miroir (zm : ℂ) (hzm : zm ∈ zerosXiDecale)
    (hre : |zm.re| < 1 / 2) :
    ∃ U : Set ℂ, zm ∈ U ∧ (∀ z ∈ U, -(starRingEnd ℂ) z ∈ U) ∧
      (∀ z ∈ zerosXiDecale, z ∈ U → z = zm ∨ z = -(starRingEnd ℂ) zm) ∧
      ((zm.re = 0 ∧ -(starRingEnd ℂ) zm = zm) ∨
       (zm.re ≠ 0 ∧ -(starRingEnd ℂ) zm ≠ zm)) := by
  obtain ⟨U, hU, hsymm, huniq⟩ := exists_voisinage_symetrique zm hzm hre
  refine ⟨U, hU, hsymm, huniq, ?_⟩
  by_cases h : zm.re = 0
  · left
    refine ⟨h, ?_⟩
    apply Complex.ext <;> simp [h]
  · right
    refine ⟨h, ?_⟩
    intro heq
    apply h
    have h1 := congrArg Complex.re heq
    simp at h1
    linarith

lemma voisinage_symetrique_unique_of_re_zero (zm : ℂ) (hzm : zm ∈ zerosXiDecale)
    (hre : |zm.re| < 1 / 2) (h0 : zm.re = 0) :
    ∃ U : Set ℂ, zm ∈ U ∧ (∀ z ∈ U, -(starRingEnd ℂ) z ∈ U) ∧
      (∀ z ∈ zerosXiDecale, z ∈ U → z = zm) := by
  obtain ⟨U, hU, hsymm, huniq⟩ := exists_voisinage_symetrique zm hzm hre
  have hfix : -(starRingEnd ℂ) zm = zm := by
    apply Complex.ext <;> simp [h0]
  refine ⟨U, hU, hsymm, ?_⟩
  intro z hz hzU
  rcases huniq z hz hzU with h | h
  · exact h
  · rw [h, hfix]


open RealPartCarac in
lemma configuration_deux_zeros (zm : ℂ) (hzm : zm ∈ zerosXiDecale)
    (hre : |zm.re| < 1 / 2) (h0 : zm.re ≠ 0)
    (hsym : ∀ z, xiDecale (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (xiDecale z)) :
    ∃ U : Set ℂ, zm ∈ U ∧ (∀ z ∈ U, -(starRingEnd ℂ) z ∈ U) ∧
      (∀ z ∈ zerosXiDecale, z ∈ U → z = zm ∨ z = -(starRingEnd ℂ) zm) ∧
      -(starRingEnd ℂ) zm ≠ zm ∧
      analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)
        = analyticOrderAt xiDecale zm := by
  obtain ⟨U, hU, hsymm, huniq⟩ := exists_voisinage_symetrique zm hzm hre
  have hne : -(starRingEnd ℂ) zm ≠ zm := by
    intro heq
    apply h0
    have h1 := congrArg Complex.re heq
    simp at h1
    linarith
  exact ⟨U, hU, hsymm, huniq, hne,
    analyticOrderAt_symm_neg_conj
      (xiDecale_differentiable.analyticAt zm)
      (xiDecale_differentiable.analyticAt _) hsym⟩

lemma neg_conj_eq_self_iff (z : ℂ) : -(starRingEnd ℂ) z = z ↔ z.re = 0 := by
  constructor
  · intro h
    have h1 := congrArg Complex.re h
    simp at h1
    linarith
  · intro h
    apply Complex.ext
    · simp [h]
    · simp

lemma configuration_exclusion (zm : ℂ) (hzm : zm ∈ zerosXiDecale)
    (hre : |zm.re| < 1 / 2) (h0 : zm.re ≠ 0)
    (hsym : ∀ z, xiDecale (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (xiDecale z)) :
    -(starRingEnd ℂ) zm ≠ zm ∧
    analyticOrderAt xiDecale (-(starRingEnd ℂ) zm) = analyticOrderAt xiDecale zm := by
  obtain ⟨_, _, _, _, hne, hord⟩ := configuration_deux_zeros zm hzm hre h0 hsym
  exact ⟨hne, hord⟩

lemma ExclusionZerosAsymetriques (zm : ℂ) (hzm : zm ∈ zerosXiDecale)
    (hre : |zm.re| < 1 / 2)
    (hsym : ∀ z, xiDecale (-(starRingEnd ℂ) z) = (starRingEnd ℂ) (xiDecale z))
    (hM : ((analyticOrderAt xiDecale zm).toNat : ℂ) * zm =
          ((analyticOrderAt xiDecale zm).toNat : ℂ) * (-(starRingEnd ℂ) zm))
    (hmu : 1 ≤ (analyticOrderAt xiDecale zm).toNat) :
    zm.re = 0 := by
  by_contra h0
  obtain ⟨hne, hord⟩ := configuration_exclusion zm hzm hre h0 hsym
  have hμ : ((analyticOrderAt xiDecale zm).toNat : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : (analyticOrderAt xiDecale zm).toNat ≠ 0)
  have heq : zm = -(starRingEnd ℂ) zm := mul_left_cancel₀ hμ hM
  exact hne heq.symm



----------------------------------------------------------------------

lemma ContrainteSpectraleHankel (f : ℂ → ℂ) (zm : ℂ)
    (hμ : 1 ≤ (analyticOrderAt f zm).toNat)
    (hsym : analyticOrderAt f (-(starRingEnd ℂ) zm) = analyticOrderAt f zm)
    (hM : momentLocal f zm = momentLocal f (-(starRingEnd ℂ) zm)) :
    zm.re = 0 := by
  unfold momentLocal at hM
  rw [hsym] at hM
  have hμC : ((analyticOrderAt f zm).toNat : ℂ) ≠ 0 := by
    have : (analyticOrderAt f zm).toNat ≠ 0 := by omega
    exact_mod_cast this
  have heq : zm = -(starRingEnd ℂ) zm := mul_left_cancel₀ hμC hM
  exact (neg_conj_eq_self_iff zm).mp heq.symm

lemma deviation_eq_zero_iff (z : ℂ) (hz : z ≠ 0) :
    deviation z = 0 ↔ z.re = 0 := by
  unfold deviation
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [Real.arcsin_eq_zero_iff]
  constructor
  · intro h
    rcases div_eq_zero_iff.mp h with h | h
    · exact h
    · exact absurd h hn
  · intro h
    simp [h]

lemma deviation_sigma (z : ℂ) :
    deviation (-(starRingEnd ℂ) z) = -deviation z := by
  unfold deviation
  have h1 : (-(starRingEnd ℂ) z).re = -z.re := by simp
  have h2 : ‖-(starRingEnd ℂ) z‖ = ‖z‖ := by simp
  rw [h1, h2, neg_div, Real.arcsin_neg]

lemma re_eq_norm_mul_sin_deviation (z : ℂ) :
    z.re = ‖z‖ * Real.sin (deviation z) := by
  unfold deviation
  by_cases hz : z = 0
  · simp [hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hb : -1 ≤ z.re / ‖z‖ ∧ z.re / ‖z‖ ≤ 1 := by
      have := abs_re_le_norm z
      constructor
      · rw [le_div_iff₀ (norm_pos_iff.mpr hz)]
        have := neg_abs_le z.re
        linarith [abs_re_le_norm z]
      · rw [div_le_one (norm_pos_iff.mpr hz)]
        exact le_trans (le_abs_self _) (abs_re_le_norm z)
    rw [Real.sin_arcsin hb.1 hb.2]
    field_simp

lemma ExclusionParDeviation (zm : ℂ) (hz : zm ≠ 0) (F : ℝ → ℝ)
    (hF0 : F (deviation zm) = 0)
    (hinj : ∀ θ : ℝ, -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 → F θ = 0 → θ = 0) :
    zm.re = 0 := by
  have hb : -(Real.pi / 2) ≤ deviation zm ∧ deviation zm ≤ Real.pi / 2 :=
    ⟨Real.neg_pi_div_two_le_arcsin _, Real.arcsin_le_pi_div_two _⟩
  have h0 : deviation zm = 0 := hinj _ hb.1 hb.2 hF0
  exact (deviation_eq_zero_iff zm hz).mp h0

lemma sigma_devient_conj (z : ℂ) :
    (-Complex.I) * (-(starRingEnd ℂ) z) = (starRingEnd ℂ) ((-Complex.I) * z) := by
  simp [map_mul, map_neg, Complex.conj_I]

lemma noeud_reel_iff (z : ℂ) :
    (starRingEnd ℂ) ((-Complex.I) * z) = (-Complex.I) * z ↔ z.re = 0 := by
  constructor
  · intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  · intro h
    apply Complex.ext <;> simp [h]

lemma spectre_stable_conj
    {r : ℕ} (lam : Fin r → ℂ)
    (Mat : Matrix (Fin r) (Fin r) ℂ)
    (hspec : spectrum ℂ Mat = Set.range lam)
    (hstab : ∀ i, ∃ j, lam j = (starRingEnd ℂ) (lam i)) :
    ∀ μ ∈ spectrum ℂ Mat, (starRingEnd ℂ) μ ∈ spectrum ℂ Mat := by
  intro μ hμ
  rw [hspec] at hμ ⊢
  obtain ⟨i, rfl⟩ := hμ
  exact hstab i

open DefinitionsThEq ObservableSelectionTheorem VandermondeThEq in
theorem exclusion_cadre_spectral
    {K : ℕ} (zs : Fin K → ℂ) (m : Fin K → ℕ)
    (hm : ∀ j, 0 < m j)
    (hinj : Function.Injective (fun j => (-Complex.I) * zs j))
    (hsym : ∀ j, ∃ k, zs k = -(starRingEnd ℂ) (zs j)) :
    let lam : Fin K → ℂ := fun j => (-Complex.I) * zs j
    let w : Fin K → ℤ := fun j => (m j : ℤ)
    IsUnit (hankel0 lam w).det ∧
    spectrum ℂ (operateurM lam w) = Set.range lam ∧
    (∀ μ ∈ spectrum ℂ (operateurM lam w),
        (starRingEnd ℂ) μ ∈ spectrum ℂ (operateurM lam w)) ∧
    (∀ j, (zs j).re ≠ 0 →
        ∃ k, k ≠ j ∧ lam k = (starRingEnd ℂ) (lam j)) := by
  intro lam w
  have hw : ∀ r, w r ≠ 0 := by
    intro r
    simp only [w]
    exact_mod_cast (hm r).ne'
  have hspec : spectrum ℂ (operateurM lam w) = Set.range lam :=
    spectre_operateurM lam w hinj hw
  have hstab : ∀ i, ∃ j, lam j = (starRingEnd ℂ) (lam i) := by
    intro i
    obtain ⟨k, hk⟩ := hsym i
    refine ⟨k, ?_⟩
    simp only [lam]
    rw [hk]
    exact sigma_devient_conj (zs i)
  refine ⟨(hankel0_det_ne_zero lam w hinj hw).isUnit, hspec,
    spectre_stable_conj lam _ hspec hstab, ?_⟩
  intro j hre
  obtain ⟨k, hk⟩ := hstab j
  refine ⟨k, ?_, hk⟩
  intro hkj
  subst hkj
  have : (starRingEnd ℂ) ((-Complex.I) * zs k) = (-Complex.I) * zs k := hk.symm
  exact hre ((noeud_reel_iff (zs k)).1 this)

lemma moment1_sigma (m : ℕ) (z : ℂ) :
    moment1 m (-(starRingEnd ℂ) z) = (m : ℂ) * (Complex.I * (starRingEnd ℂ) z) := by
  unfold moment1
  ring

lemma difference_moments (m : ℕ) (z : ℂ) :
    moment1 m z - moment1 m (-(starRingEnd ℂ) z)
      = (-2 * Complex.I) * (m : ℂ) * (z.re : ℂ) := by
  rw [moment1_sigma]
  unfold moment1
  have h : z + (starRingEnd ℂ) z = 2 * (z.re : ℂ) := by
    have h0 := Complex.add_conj z
    push_cast at h0
    exact h0
  calc (m : ℂ) * (-Complex.I * z) - (m : ℂ) * (Complex.I * (starRingEnd ℂ) z)
      = (-Complex.I) * (m : ℂ) * (z + (starRingEnd ℂ) z) := by ring
    _ = (-2 * Complex.I) * (m : ℂ) * (z.re : ℂ) := by rw [h]; ring

theorem partie_reelle_par_moments (m : ℕ) (hm : 0 < m) (z : ℂ) :
    (z.re : ℂ) =
      (Complex.I / (2 * (m : ℂ))) *
        (moment1 m z - moment1 m (-(starRingEnd ℂ) z)) := by
  rw [difference_moments]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp
  simp only [Complex.I_sq]
  ring

open DefinitionsThEq ObservableSelectionTheorem in
lemma spectre_un_noeud (a : ℂ) (w : ℤ) (hw : w ≠ 0) :
    spectrum ℂ (operateurM (fun _ : Fin 1 => a) (fun _ => w)) = {a} := by
  have hinj : Function.Injective (fun _ : Fin 1 => a) := by
    intro i j _
    exact Subsingleton.elim i j
  have := spectre_operateurM (fun _ : Fin 1 => a) (fun _ => w) hinj (fun _ => hw)
  rw [this]
  ext x
  simp []

theorem exclusion_par_contours_disjoints
    (zm : ℂ) (m : ℕ) (hm : 0 < m) (hre : zm.re ≠ 0)
    (mu1 mu2 : ℂ)
    (hres1 : mu1 = moment1 m zm)
    (hres2 : mu2 = moment1 m (-(starRingEnd ℂ) zm)) :
    zm ≠ -(starRingEnd ℂ) zm ∧
    (zm.re : ℂ) = (Complex.I / (2 * (m : ℂ))) * (mu1 - mu2) := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 := congrArg Complex.re h
    simp at h1
    exact hre (by linarith)
  · rw [hres1, hres2]
    exact partie_reelle_par_moments m hm zm

lemma isolation_zero
    (f : ℂ → ℂ) (z0 z1 : ℂ) (_ : AnalyticAt ℂ f z0)
    (hne : ∀ᶠ z in nhdsWithin z0 {z0}ᶜ, f z ≠ 0) (h01 : z0 ≠ z1) :
    ∃ ε > 0, (∀ z, dist z z0 ≤ ε → z ≠ z0 → f z ≠ 0) ∧ ε < dist z0 z1 / 2 := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
  obtain ⟨δ, hδ, hball⟩ := hne
  have hd : 0 < dist z0 z1 := dist_pos.mpr h01
  refine ⟨min (δ / 2) (dist z0 z1 / 4), ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · intro z hz hzne
    have hε : min (δ / 2) (dist z0 z1 / 4) ≤ δ / 2 := min_le_left _ _
    have hlt : dist z z0 < δ := by linarith
    exact hball hlt hzne
  · have hε : min (δ / 2) (dist z0 z1 / 4) ≤ dist z0 z1 / 4 := min_le_right _ _
    linarith

open CircInt2 in
lemma moment1_cercle
    (z0 : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hz0 : xiDecale z0 = 0)
    (hiso : ∀ z, dist z z0 ≤ ε → xiDecale z = 0 → z = z0) :
    (1 / (2 * ↑Real.pi * Complex.I)) *
        ∮ z in C(z0, ε), (-Complex.I * z) * (deriv xiDecale z / xiDecale z)
      = moment1 (analyticOrderAt xiDecale z0).toNat z0 := by
  have hS : ∀ z, z ∈ ({z0} : Finset ℂ) ↔
      z ∈ Metric.ball z0 ε ∧ xiDecale z = 0 := by
    intro z
    simp only [Finset.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨Metric.mem_ball_self hε, hz0⟩
    · rintro ⟨hb, hz⟩
      exact hiso z (le_of_lt (Metric.mem_ball.1 hb)) hz
  have hne : ∀ z ∈ Metric.sphere z0 ε, xiDecale z ≠ 0 := by
    intro z hz hz'
    have hdist : dist z z0 = ε := Metric.mem_sphere.1 hz
    have := hiso z hdist.le hz'
    rw [this, dist_self] at hdist
    linarith
  have h := argument_principle_circle (f := xiDecale)
    (h := fun z => -Complex.I * z) hε xiDecale_differentiable
    (by fun_prop) hne {z0} hS
  rw [h]
  simp [moment1]

theorem existence_deux_cercles
    (zm : ℂ) (_ : xiDecale zm = 0) (hre : zm.re ≠ 0)
    (hne : ∀ᶠ z in nhdsWithin zm {zm}ᶜ, xiDecale z ≠ 0)
    (hne' : ∀ᶠ z in nhdsWithin (-(starRingEnd ℂ) zm) {-(starRingEnd ℂ) zm}ᶜ,
      xiDecale z ≠ 0) :
    ∃ ε > 0,
      zm ≠ -(starRingEnd ℂ) zm ∧
      2 * ε < dist zm (-(starRingEnd ℂ) zm) ∧
      (∀ z, dist z zm ≤ ε → z ≠ zm → xiDecale z ≠ 0) ∧
      (∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
        z ≠ -(starRingEnd ℂ) zm → xiDecale z ≠ 0) := by
  have hdiff : zm ≠ -(starRingEnd ℂ) zm := by
    intro h
    apply hre
    have := congrArg Complex.re h
    simp at this
    linarith
  obtain ⟨ε₁, hε₁, hiso₁, hlt₁⟩ :=
    isolation_zero xiDecale zm (-(starRingEnd ℂ) zm)
      (xiDecale_differentiable.analyticAt zm) hne hdiff
  obtain ⟨ε₂, hε₂, hiso₂, hlt₂⟩ :=
    isolation_zero xiDecale (-(starRingEnd ℂ) zm) zm
      (xiDecale_differentiable.analyticAt (-(starRingEnd ℂ) zm)) hne' hdiff.symm
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, hdiff, ?_, ?_, ?_⟩
  · have h1 : min ε₁ ε₂ ≤ ε₁ := min_le_left ε₁ ε₂
    linarith
  · intro z hz hzne
    exact hiso₁ z (le_trans hz (min_le_left _ _)) hzne
  · intro z hz hzne
    exact hiso₂ z (le_trans hz (min_le_right _ _)) hzne

theorem re_nulle_of_moments_egaux
    (m : ℕ) (hm : 0 < m) (zm : ℂ)
    (h : moment1 m zm = moment1 m (-(starRingEnd ℂ) zm)) :
    zm.re = 0 := by
  have h0 : moment1 m zm - moment1 m (-(starRingEnd ℂ) zm) = 0 := sub_eq_zero.mpr h
  rw [difference_moments] at h0
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have h2i : (-2 * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero]
  have hre : (zm.re : ℂ) = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h3 | h3
      · exact absurd h3 h2i
      · exact absurd h3 hm'
    · exact h1
  exact_mod_cast hre

theorem moments_distincts_of_re_ne_zero
    (m : ℕ) (hm : 0 < m) (zm : ℂ) (hre : zm.re ≠ 0) :
    moment1 m zm ≠ moment1 m (-(starRingEnd ℂ) zm) :=
  fun h => hre (re_nulle_of_moments_egaux m hm zm h)

theorem re_nulle_iff_moments_egaux (m : ℕ) (hm : 0 < m) (zm : ℂ) :
    zm.re = 0 ↔ moment1 m zm = moment1 m (-(starRingEnd ℂ) zm) := by
  constructor
  · intro hre
    have hσ : -(starRingEnd ℂ) zm = zm := by
      apply Complex.ext <;> simp [hre]
    rw [hσ]
  · exact fun h => re_nulle_of_moments_egaux m hm zm h

theorem re_nulle_iff_integrales_egales
    (m : ℕ) (hm : 0 < m) (zm : ℂ) (I1 I2 : ℂ)
    (h1 : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * I1 = moment1 m zm)
    (h2 : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * I2
            = moment1 m (-(starRingEnd ℂ) zm)) :
    zm.re = 0 ↔ I1 = I2 := by
  have hc : (1 / (2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    simp [Complex.I_ne_zero, hpi]
  rw [re_nulle_iff_moments_egaux m hm zm, ← h1, ← h2]
  constructor
  · intro h; exact mul_left_cancel₀ hc h
  · intro h; rw [h]

open CircInt2 in
theorem re_nulle_iff_integrale_translation
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hm : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hz1 : xiDecale (-(starRingEnd ℂ) zm) = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (hmult : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat)
    (hA : CircleIntegrable
      (fun z => (z + (-(starRingEnd ℂ) zm - zm)) *
        (deriv xiDecale (z + (-(starRingEnd ℂ) zm - zm)) /
          xiDecale (z + (-(starRingEnd ℂ) zm - zm)))) zm ε)
    (hB : CircleIntegrable
      (fun z => z * (deriv xiDecale z / xiDecale z)) zm ε) :
    zm.re = 0 ↔
      ∮ z in C(zm, ε),
        ((z + (-(starRingEnd ℂ) zm - zm)) *
            (deriv xiDecale (z + (-(starRingEnd ℂ) zm - zm)) /
              xiDecale (z + (-(starRingEnd ℂ) zm - zm)))
          - z * (deriv xiDecale z / xiDecale z)) = 0 := by
  let d : ℂ := -(starRingEnd ℂ) zm - zm
  let F : ℂ → ℂ := fun w =>
    (-Complex.I * w) * (deriv xiDecale w / xiDecale w)
  let I₁ : ℂ := ∮ z in C(zm, ε), F z
  let I₂ : ℂ := ∮ z in C(-(starRingEnd ℂ) zm, ε), F z
  have h1 : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * I₁ =
      moment1 (analyticOrderAt xiDecale zm).toNat zm := by
    dsimp [I₁, F]
    exact moment1_cercle zm ε hε hz0 hiso1
  have h2 : (1 / (2 * (Real.pi : ℂ) * Complex.I)) * I₂ =
      moment1 (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat
        (-(starRingEnd ℂ) zm) := by
    dsimp [I₂, F]
    exact moment1_cercle (-(starRingEnd ℂ) zm) ε hε hz1 hiso2
  have hEq : zm.re = 0 ↔ I₁ = I₂ := by
    rw [hmult] at h2
    exact re_nulle_iff_integrales_egales
      (analyticOrderAt xiDecale zm).toNat hm zm I₁ I₂ h1 h2
  have htrans : I₂ = ∮ z in C(zm, ε), F (z + d) := by
    have h := circleIntegral_translation_aux F zm d ε
    have hzd : zm + d = -(starRingEnd ℂ) zm := by
      simp only [d]; ring
    rw [hzd] at h
    exact h
  have hscaled :
      (∮ z in C(zm, ε),
        (-Complex.I * (z + d)) *
          (deriv xiDecale (z + d) / xiDecale (z + d))) = I₂ := by
    rw [htrans]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hpt1 : ∀ z : ℂ,
      (z + d) * (deriv xiDecale (z + d) / xiDecale (z + d)) =
      Complex.I * ((-Complex.I * (z + d)) *
        (deriv xiDecale (z + d) / xiDecale (z + d))) := by
    intro z
    ring_nf
    simp [Complex.I_sq]
  have hpt2 : ∀ z : ℂ,
      z * (deriv xiDecale z / xiDecale z) =
      Complex.I * ((-Complex.I * z) * (deriv xiDecale z / xiDecale z)) := by
    intro z
    ring_nf
    simp [Complex.I_sq]
  have hdiff :
      (∮ z in C(zm, ε),
        ((z + d) * (deriv xiDecale (z + d) / xiDecale (z + d))
          - z * (deriv xiDecale z / xiDecale z))) =
        Complex.I * (I₂ - I₁) := by
    rw [circleIntegral.integral_sub hA hB]
    have e1 : (∮ z in C(zm, ε),
        (z + d) * (deriv xiDecale (z + d) / xiDecale (z + d))) =
        Complex.I * I₂ := by
      rw [← hscaled]
      rw [← circleIntegral.integral_const_mul]
      exact circleIntegral.integral_congr hε.le (fun z _ => hpt1 z)
    have e2 : (∮ z in C(zm, ε),
        z * (deriv xiDecale z / xiDecale z)) = Complex.I * I₁ := by
      change _ = Complex.I * ∮ z in C(zm, ε), F z
      rw [← circleIntegral.integral_const_mul]
      exact circleIntegral.integral_congr hε.le (fun z _ => hpt2 z)
    rw [e1, e2]
    ring
  change zm.re = 0 ↔
    ∮ z in C(zm, ε),
      ((z + d) * (deriv xiDecale (z + d) / xiDecale (z + d))
        - z * (deriv xiDecale z / xiDecale z)) = 0
  rw [hdiff]
  constructor
  · intro hz
    have heq : I₁ = I₂ := hEq.mp hz
    rw [heq]
    ring
  · intro hi
    apply hEq.mpr
    have hI0 : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have h0 : I₂ - I₁ = 0 := (mul_eq_zero.mp hi).resolve_left hI0
    exact (sub_eq_zero.mp h0).symm


theorem re_nulle_iff_moments_integrales
    (zm : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hm : 0 < (analyticOrderAt xiDecale zm).toNat)
    (hz0 : xiDecale zm = 0)
    (hz1 : xiDecale (-(starRingEnd ℂ) zm) = 0)
    (hiso1 : ∀ z, dist z zm ≤ ε → xiDecale z = 0 → z = zm)
    (hiso2 : ∀ z, dist z (-(starRingEnd ℂ) zm) ≤ ε →
      xiDecale z = 0 → z = -(starRingEnd ℂ) zm)
    (hmult : (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat =
      (analyticOrderAt xiDecale zm).toNat) :
    zm.re = 0 ↔
      (∮ z in C(zm, ε), (-Complex.I * z) * (deriv xiDecale z / xiDecale z)) =
      ∮ z in C(-(starRingEnd ℂ) zm, ε),
        (-Complex.I * z) * (deriv xiDecale z / xiDecale z) := by
  have h1 : (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      (∮ z in C(zm, ε), (-Complex.I * z) * (deriv xiDecale z / xiDecale z)) =
      moment1 (analyticOrderAt xiDecale zm).toNat zm :=
    moment1_cercle zm ε hε hz0 hiso1
  have h2 : (1 / (2 * (Real.pi : ℂ) * Complex.I)) *
      (∮ z in C(-(starRingEnd ℂ) zm, ε),
        (-Complex.I * z) * (deriv xiDecale z / xiDecale z)) =
      moment1 (analyticOrderAt xiDecale (-(starRingEnd ℂ) zm)).toNat
        (-(starRingEnd ℂ) zm) :=
    moment1_cercle (-(starRingEnd ℂ) zm) ε hε hz1 hiso2
  rw [hmult] at h2
  exact re_nulle_iff_integrales_egales
    (analyticOrderAt xiDecale zm).toNat hm zm _ _ h1 h2








end DecaleZeroProp
