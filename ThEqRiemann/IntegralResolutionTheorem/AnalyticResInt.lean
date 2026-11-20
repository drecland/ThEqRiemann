import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef

/-! -/
namespace AnalyticRes

open Set Complex Module End ResDef




lemma local_factor {f : ℂ → ℂ} {μ : ℂ} {m : ℕ}
    (hf : AnalyticAt ℂ f μ) (hm : analyticOrderAt f μ = (m : ℕ∞)) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h μ ∧ h μ ≠ 0 ∧
      ∀ᶠ z in nhds μ, f z = (z - μ) ^ m • h z :=
  (hf.analyticOrderAt_eq_natCast).mp hm

lemma local_factor_le {f : ℂ → ℂ} {a : ℂ} {n : ℕ}
    (hf : AnalyticAt ℂ f a) (hn : (n : ℕ∞) ≤ analyticOrderAt f a) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧
      ∀ᶠ z in nhds a, f z = (z - a) ^ n • h z := by
  cases hord : analyticOrderAt f a with
  | top =>
    have hzero : ∀ᶠ z in nhds a, f z = 0 := by
      simpa using (analyticOrderAt_eq_top.mp hord)
    refine ⟨0, analyticAt_const, ?_⟩
    filter_upwards [hzero] with z hz
    simp [hz]
  | coe m =>
    rw [hord] at hn
    have hnm : n ≤ m := by exact_mod_cast hn
    obtain ⟨k, hk, hk0, hfk⟩ := local_factor hf hord
    refine ⟨fun z => (z - a) ^ (m - n) • k z, ?_, ?_⟩
    · exact ((analyticAt_id.sub analyticAt_const).pow _).smul hk
    · filter_upwards [hfk] with z hz
      rw [hz, smul_smul, ← pow_add, Nat.add_sub_cancel' hnm]

lemma divide_pow_analytic {f : ℂ → ℂ} {U : Set ℂ} (_ : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) {a : ℂ} (ha : a ∈ U) {n : ℕ}
    (hn : (n : ℕ∞) ≤ analyticOrderAt f a) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ ∀ z ∈ U, f z = (z - a) ^ n * g z := by
  classical
  obtain ⟨h, hh, hfh⟩ := local_factor_le (hf a ha) hn
  have hfh' : ∀ᶠ z in nhds a, f z = (z - a) ^ n * h z := by
    simpa [smul_eq_mul] using hfh
  set g : ℂ → ℂ := Function.update (fun z => f z / (z - a) ^ n) a (h a) with hg
  have hgh : g =ᶠ[nhds a] h := by
    filter_upwards [hfh'] with z hz
    by_cases hza : z = a
    · subst hza
      simp [hg]
    · have hpow : (z - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
      simp only [hg, Function.update_of_ne hza]
      rw [hz]
      field_simp
  refine ⟨g, ?_, ?_⟩
  · intro z hz
    by_cases hza : z = a
    · subst hza
      exact hh.congr hgh.symm
    · have hz_ne : ∀ᶠ w in nhds z, w ≠ a := eventually_ne_nhds hza
      have hpoint : AnalyticAt ℂ (fun w => f w / (w - a) ^ n) z := by
        refine (hf z hz).div ?_ ?_
        · exact (analyticAt_id.sub analyticAt_const).pow n
        · exact pow_ne_zero _ (sub_ne_zero.mpr hza)
      refine hpoint.congr ?_
      filter_upwards [hz_ne] with w hw
      simp [hg, Function.update_of_ne hw]
  · intro z hz
    by_cases hza : z = a
    · subst hza
      have := hfh'.self_of_nhds
      simpa [hg] using this
    · have hpow : (z - a) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
      simp only [hg, Function.update_of_ne hza]
      field_simp

lemma analyticOrderAt_pow_sub_ne_zero {a μ : ℂ} (n : ℕ) (hμa : μ ≠ a) :
    analyticOrderAt (fun z : ℂ => (z - a) ^ n) μ = 0 := by
  have hanal : AnalyticAt ℂ (fun z : ℂ => (z - a) ^ n) μ :=
    ((analyticAt_id.sub analyticAt_const).pow n)
  have hne : (fun z : ℂ => (z - a) ^ n) μ ≠ 0 := by
    simp only
    exact pow_ne_zero _ (sub_ne_zero.mpr hμa)
  exact hanal.analyticOrderAt_eq_zero.mpr hne

lemma analyticOrderAt_eq_of_mul_pow {a μ : ℂ} {k : ℂ → ℂ} {f : ℂ → ℂ} (n : ℕ)
    (hkμ : AnalyticAt ℂ k μ)
    (hpow : analyticOrderAt (fun z : ℂ => (z - a) ^ n) μ = 0)
    (hfeq : f =ᶠ[nhds μ] fun z => (z - a) ^ n * k z) :
    analyticOrderAt k μ = analyticOrderAt f μ := by
  have hcanal : AnalyticAt ℂ (fun z : ℂ => (z - a) ^ n) μ :=
    (analyticAt_id.sub analyticAt_const).pow n
  have hprod : analyticOrderAt (fun z : ℂ => (z - a) ^ n * k z) μ
      = analyticOrderAt k μ := by
    have h := analyticOrderAt_mul hcanal hkμ
    rw [hpow, zero_add] at h
    exact h
  rw [analyticOrderAt_congr hfeq, hprod]

lemma exists_g_aux {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (m : ℂ → ℕ) (s : Finset ℂ) (hsU : ↑s ⊆ U)
    (hord : ∀ μ ∈ s, analyticOrderAt f μ = (m μ : ℕ∞)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ∀ z ∈ U, f z = (∏ μ ∈ s, (z - μ) ^ m μ) * g z := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    exact ⟨f, hf, fun z _ => by simp⟩
  | insert a s ha ih =>
    have haU : a ∈ U := hsU (Finset.mem_insert_self a s)
    have hsU' : (↑s : Set ℂ) ⊆ U :=
      fun x hx => hsU (Finset.mem_insert_of_mem hx)
    have hord_a : (m a : ℕ∞) ≤ analyticOrderAt f a :=
      (hord a (Finset.mem_insert_self a s)).ge
    obtain ⟨k, hkU, hk⟩ := divide_pow_analytic hU hf haU hord_a
    have hk_ord : ∀ μ ∈ s, analyticOrderAt k μ = (m μ : ℕ∞) := by
      intro μ hμ
      have hμU : μ ∈ U := hsU' hμ
      have hμa : μ ≠ a := fun h => ha (h ▸ hμ)
      have hfeq : f =ᶠ[nhds μ] fun z => (z - a) ^ m a * k z :=
        Filter.eventually_of_mem (hU.mem_nhds hμU) (fun z hz => hk z hz)
      have hpow : analyticOrderAt ((fun z : ℂ => (z - a) ^ m a)) μ = 0 :=
        analyticOrderAt_pow_sub_ne_zero (m a) hμa
      have hkf : analyticOrderAt k μ = analyticOrderAt f μ :=
        analyticOrderAt_eq_of_mul_pow (m a) (hkU μ hμU) hpow hfeq
      rw [hkf, hord μ (Finset.mem_insert_of_mem hμ)]
    obtain ⟨g, hgU, hkg⟩ := ih hkU hsU' hk_ord
    refine ⟨g, hgU, fun z hz => ?_⟩
    rw [hk z hz, hkg z hz, Finset.prod_insert ha]
    ring

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


lemma exists_g_analytic (T : End ℂ V) {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hfan : AnalyticOnNhd ℂ f (Metric.ball c R))
    (hzeros : ∀ μ ∈ spec T, μ ∈ Metric.ball c R ∧ analyticOrderAt f μ = (mT T μ : ℕ∞)) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.ball c R) ∧
      ∀ z ∈ Metric.ball c R, f z = Pprod T z * g z := by
  obtain ⟨g, hg, hfg⟩ := exists_g_aux Metric.isOpen_ball hfan (mT T) (spec T)
    (fun μ hμ => (hzeros μ hμ).1) (fun μ hμ => (hzeros μ hμ).2)
  exact ⟨g, hg, fun z hz => by simpa [Pprod] using hfg z hz⟩

lemma exists_g_analytic_aux {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfan : AnalyticOnNhd ℂ f U) (m : ℂ → ℕ)
    (s : Finset ℂ) (hs : ∀ μ ∈ s, μ ∈ U ∧ analyticOrderAt f μ = (m μ : ℕ∞))
    (_hzero : ∀ z ∈ U, f z = 0 → z ∈ s) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧
      ∀ z ∈ U, f z = (∏ μ ∈ s, (z - μ) ^ m μ) * g z := by
  have hsU : (↑s : Set ℂ) ⊆ U := fun μ hμ => (hs μ hμ).1
  have hord : ∀ μ ∈ s, analyticOrderAt f μ = (m μ : ℕ∞) := fun μ hμ => (hs μ hμ).2
  exact exists_g_aux hU hfan m s hsU hord


------------------------------------------------------------------

lemma Pprod_ne_zero_of_notMem (T : End ℂ V) {z : ℂ} (hz : z ∉ spec T) :
    Pprod T z ≠ 0 := by
  unfold Pprod
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro μ hμ
  have : z - μ ≠ 0 := sub_ne_zero.mpr (fun h => hz (h ▸ hμ))
  exact pow_ne_zero _ this

lemma analyticOrderAt_Pprod (T : End ℂ V) {μ : ℂ} (hμ : μ ∈ spec T) :
    analyticOrderAt (Pprod T) μ = (mT T μ : ℕ∞) := by
  classical
  set Q : ℂ → ℂ := fun z => ∏ ν ∈ (spec T).erase μ, (z - ν) ^ mT T ν with hQdef
  have hfact : Pprod T = fun z => (z - μ) ^ mT T μ * Q z := by
    funext z
    unfold Pprod
    rw [hQdef]
    exact (Finset.mul_prod_erase (spec T) (fun ν => (z - ν) ^ mT T ν) hμ).symm
  have hA : AnalyticAt ℂ (fun z : ℂ => (z - μ) ^ mT T μ) μ :=
    (analyticAt_id.sub analyticAt_const).pow _
  have hQan : AnalyticAt ℂ Q μ := by
    have key : ∀ s : Finset ℂ,
        AnalyticAt ℂ (fun w : ℂ => ∏ ν ∈ s, (w - ν) ^ mT T ν) μ := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using analyticAt_const
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ((analyticAt_id.sub analyticAt_const).pow _).mul ih
    exact key _
  have hQne : Q μ ≠ 0 := by
    rw [hQdef]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro ν hν
    have hne : ν ≠ μ := Finset.ne_of_mem_erase hν
    exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hne))
  have hQ0 : analyticOrderAt Q μ = 0 := hQan.analyticOrderAt_eq_zero.mpr hQne
  have hpow : analyticOrderAt (fun z : ℂ => (z - μ) ^ mT T μ) μ = (mT T μ : ℕ∞) := by
    rw [hA.analyticOrderAt_eq_natCast]
    refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, ?_⟩
    exact Filter.Eventually.of_forall fun w => by simp
  have hmul : analyticOrderAt (fun z : ℂ => (z - μ) ^ mT T μ * Q z) μ
      = analyticOrderAt (fun z : ℂ => (z - μ) ^ mT T μ) μ + analyticOrderAt Q μ :=
    analyticOrderAt_mul hA hQan
  rw [hfact, hmul, hpow, hQ0, add_zero]

lemma g_ne_zero_ball (T : End ℂ V) {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hfg : ∀ z ∈ Metric.ball c R, f z = Pprod T z * g z)
    (hzeros : ∀ μ ∈ spec T, μ ∈ Metric.ball c R →
      analyticOrderAt f μ = (mT T μ : ℕ∞))
    (hgan : AnalyticOnNhd ℂ g (Metric.ball c R))
    (hall : ∀ z ∈ Metric.ball c R, f z = 0 → z ∈ spec T) :
    ∀ z ∈ Metric.ball c R, g z ≠ 0 := by
  intro z hz hgz
  by_cases hzs : z ∈ spec T
  · have hfeq : f =ᶠ[nhds z] fun w => Pprod T w * g w := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw using hfg w hw
    have hPan : AnalyticAt ℂ (Pprod T) z := by
      unfold Pprod
      have hfac : ∀ μ ∈ spec T,
          AnalyticAt ℂ (fun w : ℂ => (w - μ) ^ mT T μ) z := fun μ _ =>
        (analyticAt_id.sub analyticAt_const).pow _
      exact Finset.analyticAt_fun_prod (spec T) hfac
    have h1 : analyticOrderAt f z = (mT T z : ℕ∞) := hzeros z hzs hz
    have h2 : analyticOrderAt f z
        = analyticOrderAt (Pprod T) z + analyticOrderAt g z := by
      rw [analyticOrderAt_congr hfeq]
      exact analyticOrderAt_mul hPan (hgan z hz)
    rw [analyticOrderAt_Pprod T hzs, h1] at h2
    have hg0 : analyticOrderAt g z = 0 := by
      have hne : (mT T z : ℕ∞) ≠ ⊤ := ENat.natCast_ne_top _
      have h3 : (mT T z : ℕ∞) + analyticOrderAt g z = (mT T z : ℕ∞) + 0 := by
        rw [add_zero]; exact h2.symm
      exact (WithTop.add_left_cancel hne h3)
    have := (hgan z hz).analyticOrderAt_eq_zero.mp hg0
    exact this hgz
  · have hP := Pprod_ne_zero_of_notMem T hzs
    have : f z = 0 := by rw [hfg z hz, hgz, mul_zero]
    exact hzs (hall z hz this)

lemma factor_f (T : End ℂ V) (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (_ : 0 < R)
    (hf : AnalyticOnNhd ℂ f (Metric.closedBall c R))
    (hnz : ∀ z ∈ Metric.sphere c R, f z ≠ 0)
    (hzeros : ∀ μ ∈ spec T,
      μ ∈ Metric.ball c R ∧ f μ = 0 ∧ analyticOrderAt f μ = (mT T μ : ℕ∞))
    (hall : ∀ z ∈ Metric.ball c R, f z = 0 → z ∈ spec T) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Metric.closedBall c R) ∧
      (∀ z ∈ Metric.closedBall c R, g z ≠ 0) ∧
      (∀ z ∈ Metric.closedBall c R,
        f z = (∏ μ ∈ spec T, (z - μ) ^ mT T μ) * g z) ∧
      (∀ z ∈ Metric.closedBall c R,
        f =ᶠ[nhds z] fun w => (∏ μ ∈ spec T, (w - μ) ^ mT T μ) * g w) := by
  classical
  have hfan : AnalyticOnNhd ℂ f (Metric.ball c R) :=
    hf.mono Metric.ball_subset_closedBall
  obtain ⟨gB, hgBan, hgB⟩ := exists_g_analytic T hfan
    (fun μ hμ => ⟨(hzeros μ hμ).1, (hzeros μ hμ).2.2⟩)
  have hgBne : ∀ z ∈ Metric.ball c R, gB z ≠ 0 :=
    g_ne_zero_ball T hgB (fun μ hμ _ => (hzeros μ hμ).2.2) hgBan hall
  have hPsphere : ∀ z ∈ Metric.sphere c R, Pprod T z ≠ 0 := by
    intro z hz
    have hzs : z ∉ spec T := by
      intro h
      have := (hzeros z h).1
      rw [Metric.mem_ball] at this
      rw [Metric.mem_sphere] at hz
      linarith
    exact Pprod_ne_zero_of_notMem T hzs
  have hPan : AnalyticOnNhd ℂ (Pprod T) Set.univ := by
    intro z _
    unfold Pprod
    fun_prop
  have hsph : ∀ z ∈ Metric.closedBall c R, z ∉ Metric.ball c R →
      z ∈ Metric.sphere c R := by
    intro z hz hzb
    rw [Metric.mem_sphere]
    have h1 := Metric.mem_closedBall.mp hz
    have h2 : ¬ dist z c < R := fun h => hzb (Metric.mem_ball.mpr h)
    linarith [not_lt.mp h2]
  set g : ℂ → ℂ := fun z => if z ∈ Metric.ball
    c R then gB z else f z / Pprod T z
    with hgdef
  have hg_in : ∀ z, z ∈ Metric.ball c R → g z = gB z := by
    intro z hz
    change (if z ∈ Metric.ball c R then
      gB z else f z / Pprod T z) = gB z
    exact ite_eq_left hz
  have hg_out : ∀ z, z ∉ Metric.ball c R → g z = f z / Pprod T z := by
    intro z hz
    change (if z ∈ Metric.ball c R then gB z else f z / Pprod T z)
      = f z / Pprod T z
    exact ite_eq_right hz
  have hedge : ∀ z ∈ Metric.sphere c R, g =ᶠ[nhds z]
    fun w => f w / Pprod T w := by
    intro z hz
    have hPnhds : ∀ᶠ w in nhds z, Pprod T w ≠ 0 :=
      (hPan z (Set.mem_univ z)).continuousAt.eventually_ne
      (hPsphere z hz)
    filter_upwards [hPnhds] with w hw
    by_cases hwb : w ∈ Metric.ball c R
    · rw [hg_in w hwb, eq_div_iff hw, mul_comm]
      exact (hgB w hwb).symm
    · exact hg_out w hwb
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzb : z ∈ Metric.ball c R
    · have hev : g =ᶠ[nhds z] gB := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hzb] with w hw
        exact hg_in w hw
      exact (hgBan z hzb).congr hev.symm
    · have hzs := hsph z hz hzb
      exact ((hf z hz).div (hPan z (Set.mem_univ z))
        (hPsphere z hzs)).congr
        (hedge z hzs).symm
  · intro z hz
    by_cases hzb : z ∈ Metric.ball c R
    · rw [hg_in z hzb]
      exact hgBne z hzb
    · have hzs := hsph z hz hzb
      rw [hg_out z hzb]
      exact div_ne_zero (hnz z hzs) (hPsphere z hzs)
  · intro z hz
    by_cases hzb : z ∈ Metric.ball c R
    · rw [hg_in z hzb]
      exact hgB z hzb
    · have hzs := hsph z hz hzb
      rw [hg_out z hzb]
      have hP := hPsphere z hzs
      unfold Pprod at hP ⊢
      field_simp
  · intro z hz
    by_cases hzb : z ∈ Metric.ball c R
    · have h2 : ∀ᶠ w in nhds z, w ∈ Metric.ball c R :=
        Metric.isOpen_ball.mem_nhds hzb
      filter_upwards [h2] with w hw
      rw [hg_in w hw]
      exact hgB w hw
    · have hzs := hsph z hz hzb
      have hPnhds : ∀ᶠ w in nhds z, Pprod T w ≠ 0 :=
        (hPan z (Set.mem_univ z)).continuousAt.eventually_ne
        (hPsphere z hzs)
      filter_upwards [hedge z hzs, hPnhds] with w hw1 hw2
      rw [hw1]
      unfold Pprod at hw2 ⊢
      field_simp



end AnalyticRes
