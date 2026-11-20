import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.IntegralProp

/-! -/
namespace DefPosHankelRes

open MeasureTheory Finset Matrix Complex
open scoped ComplexConjugate
open ResDef

lemma integrableOn_pow (μ : Measure ℝ) [IsFiniteMeasure μ] (k : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k) (Set.Icc (0 : ℝ) 1) μ := by
  have hc : ContinuousOn (fun x : ℝ => x ^ k) (Set.Icc (0 : ℝ) 1) :=
    (continuous_pow k).continuousOn
  exact hc.integrableOn_compact isCompact_Icc

lemma continuous_pc {N : ℕ} (c : Fin (N + 1) → ℂ) : Continuous (pc c) := by
  unfold pc
  fun_prop

lemma continuous_normsq_pc {N : ℕ} (c : Fin (N + 1) → ℂ) :
    Continuous (fun x : ℝ => ‖pc c x‖ ^ 2) :=
  ((continuous_pc c).norm).pow 2

lemma integrableOn_normsq_pc (μ : Measure ℝ) [IsFiniteMeasure μ] {N : ℕ}
    (c : Fin (N + 1) → ℂ) :
    IntegrableOn (fun x : ℝ => ‖pc c x‖ ^ 2) (Set.Icc (0 : ℝ) 1) μ :=
  (continuous_normsq_pc c).continuousOn.integrableOn_compact isCompact_Icc

lemma normsq_pc_eq {N : ℕ} (c : Fin (N + 1) → ℂ) (x : ℝ) :
    ((‖pc c x‖ ^ 2 : ℝ) : ℂ)
      = ∑ i : Fin (N + 1), ∑ j : Fin (N + 1),
          conj (c i) * c j * ((x : ℂ) ^ (i.val + j.val)) := by
  have h1 : ((‖pc c x‖ ^ 2 : ℝ) : ℂ) = conj (pc c x) * pc c x := by
    rw [Complex.conj_mul']
    push_cast
    ring
  rw [h1]
  unfold pc
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [map_mul, map_pow, Complex.conj_ofReal]
  rw [pow_add]
  ring

lemma pc_eq_eval {N : ℕ} (c : Fin (N + 1) → ℂ) (x : ℝ) :
    pc c x = (polyOf c).eval (x : ℂ) := by
  unfold pc polyOf
  simp [Polynomial.eval_finsetSum]

lemma quadForm_eq_integral (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) {N : ℕ} (c : Fin (N + 1) → ℂ) :
    quadForm m N c
      = ((∫ x in Set.Icc (0:ℝ) 1, ‖pc c x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  have _ : IsFiniteMeasure μ := hμ.1.finite
  have hm : ∀ i j : Fin (N+1), ((m (i.val + j.val) : ℝ) : ℂ)
      = ∫ x in Set.Icc (0:ℝ) 1, ((x : ℂ) ^ (i.val + j.val)) ∂μ := by
    intro i j
    rw [hμ.2 (i.val + j.val)]
    rw [integral_complex_ofReal.symm]
    push_cast
    rfl
  rw [← integral_complex_ofReal]
  have hint : ∀ i j : Fin (N+1), Integrable
      (fun x : ℝ => conj (c i) * c j * ((x : ℂ) ^ (i.val + j.val)))
      (μ.restrict (Set.Icc (0:ℝ) 1)) := by
    intro i j
    have hc : ContinuousOn
        (fun x : ℝ => conj (c i) * c j * ((x : ℂ) ^ (i.val + j.val)))
        (Set.Icc (0:ℝ) 1) := by fun_prop
    exact hc.integrableOn_compact isCompact_Icc
  simp_rw [normsq_pc_eq]
  rw [MeasureTheory.integral_finsetSum]
  · unfold quadForm
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [integral_const_mul, ← hm i j]
    · intro j _; exact hint i j
  · intro i _
    exact MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j)


open scoped ComplexOrder

lemma hankel_isHermitian (m : ℕ → ℝ) (N : ℕ) : (hankel' m N).IsHermitian := by
  ext i j
  simp [hankel', Matrix.conjTranspose_apply, Nat.add_comm]

lemma dotProduct_hankel_eq_quadForm (m : ℕ → ℝ) (N : ℕ) (c : Fin (N + 1) → ℂ) :
    star c ⬝ᵥ (hankel' m N) *ᵥ c = quadForm m N c := by
  unfold quadForm hankel'
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  change star (c i) * (((m (i.val + j.val) : ℝ) : ℂ) * c j)
      = conj (c i) * c j * ((m (i.val + j.val) : ℝ) : ℂ)
  rw [Complex.star_def]
  ring

lemma posDef_iff_integral_pos (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (N : ℕ) :
    (hankel' m N).PosDef ↔
      ∀ c : Fin (N+1) → ℂ, c ≠ 0 →
        0 < ∫ x in Set.Icc (0:ℝ) 1, ‖pc c x‖ ^ 2 ∂μ := by
  have key : ∀ c : Fin (N+1) → ℂ,
      (star c ⬝ᵥ (hankel' m N) *ᵥ c)
        = ((∫ x in Set.Icc (0:ℝ) 1, ‖pc c x‖ ^ 2 ∂μ : ℝ) : ℂ) := fun c => by
    rw [dotProduct_hankel_eq_quadForm]
    exact quadForm_eq_integral m μ hμ c
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨_, hpd⟩ c hc
    have h1 : (0 : ℂ) < star c ⬝ᵥ (hankel' m N) *ᵥ c := hpd hc
    rw [key c] at h1
    exact_mod_cast h1
  · intro h
    refine ⟨hankel_isHermitian m N, fun c hc => ?_⟩
    rw [key c]
    exact_mod_cast h c hc

lemma ofReal_norm_sq_pc {N : ℕ} (c : Fin (N + 1) → ℂ) (x : ℝ) :
    ((‖pc c x‖ : ℝ) : ℂ) ^ 2
      = ∑ i : Fin (N + 1), ∑ j : Fin (N+1), conj (c i) * c j * (x : ℂ) ^ (i.val + j.val) := by
  have h1 : ((‖pc c x‖ : ℝ) : ℂ) ^ 2 = conj (pc c x) * pc c x :=
    (Complex.conj_mul' (pc c x)).symm
  rw [h1]
  simp only [pc, map_sum, map_mul, map_pow, Complex.conj_ofReal,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ =>
    Finset.sum_congr rfl (fun j _ => ?_))
  rw [pow_add]
  ring

lemma sum_normsq_pc_eq {N : ℕ} (c : Fin (N + 1) → ℂ) (q : ℕ)
    (x lam : Fin q → ℝ) :
    ((∑ r : Fin q, lam r * ‖pc c (x r)‖ ^ 2 : ℝ) : ℂ)
      = ∑ i : Fin (N+1), ∑ j : Fin (N+1),
          conj (c i) * c j * ((∑ r : Fin q, lam r * (x r) ^ (i.val + j.val) : ℝ) : ℂ) := by
  push_cast
  simp_rw [ofReal_norm_sq_pc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun r _ => ?_)
  ring

lemma tendsto_sum_normsq {m : ℕ → ℝ} {N : ℕ}
    {x lam : (q : ℕ) → Fin q → ℝ} (h : IsElementaryResolution m N x lam)
    (c : Fin (N + 1) → ℂ) :
    Filter.Tendsto (fun q : ℕ => ((∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2 : ℝ) : ℂ))
      Filter.atTop (nhds (quadForm m N c)) := by
  simp_rw [sum_normsq_pc_eq]
  unfold quadForm
  refine tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _ (fun j _ => ?_))
  refine Filter.Tendsto.const_mul _ ?_
  have hk : i.val + j.val ≤ 2 * N := by
    have := i.isLt; have := j.isLt; omega
  exact (Complex.continuous_ofReal.tendsto _).comp (h.2.2 _ hk)

------------------------------------------------------------------------

lemma polyOf_ne_zero {N : ℕ} {c : Fin (N + 1) → ℂ} (hc : c ≠ 0) : polyOf c ≠ 0 := by
  intro h
  apply hc
  funext j
  have hcoeff := congrArg (fun p : Polynomial ℂ => p.coeff j.val) h
  simp only [polyOf, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single j] at hcoeff
  · simpa using hcoeff
  · intro b _ hb
    have : j.val ≠ b.val := fun h' => hb (Fin.ext h').symm
    simp [this]
  · simp

lemma degree_polyOf_le {N : ℕ} (c : Fin (N + 1) → ℂ) : (polyOf c).natDegree ≤ N := by
  unfold polyOf
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  exact Nat.lt_succ_iff.mp j.isLt

lemma exists_c_of_natDegree_le {N : ℕ}
    (p : Polynomial ℂ) (hp : p.natDegree ≤ N) :
    ∃ c : Fin (N+1) → ℂ, polyOf c = p ∧ (p ≠ 0 → c ≠ 0) := by
  refine ⟨fun j => p.coeff j.val, ?_, ?_⟩
  · ext n
    unfold polyOf
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    by_cases hn : n ≤ N
    · rw [Finset.sum_eq_single ⟨n, Nat.lt_succ_of_le hn⟩]
      · simp
      · intro b _ hb
        have : n ≠ b.val := fun h' => hb (Fin.ext h'.symm)
        simp [this]
      · simp
    · have hsum : (∑ x : Fin (N+1), if n = x.val then
        p.coeff x.val else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro b _
        have hb : n ≠ b.val := by have := b.isLt; omega
        simp [hb]
      have hcoef : p.coeff n = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hsum, hcoef]
  · intro hp0 hc
    apply hp0
    ext n
    by_cases hn : n ≤ N
    · have := congrFun hc ⟨n, Nat.lt_succ_of_le hn⟩
      simpa using this
    · exact (Polynomial.coeff_eq_zero_of_natDegree_lt
        (by omega)).trans (by simp)


open IntProp in
theorem positivite_hankel_resolution (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (N : ℕ) :
    ((hankel' m N).PosDef ↔
        ∀ c : Fin (N+1) → ℂ, c ≠ 0 →
          0 < ∫ x in Set.Icc (0:ℝ) 1, ‖pc c x‖ ^ 2 ∂μ) ∧
    ((hankel' m N).PosDef ↔
        ∀ p : Polynomial ℂ, p ≠ 0 → p.natDegree ≤ N →
          μ ({x : ℝ | p.eval (x : ℂ) = 0} ∩ Set.Icc (0:ℝ) 1) < μ (Set.Icc (0:ℝ) 1)) := by
  refine ⟨posDef_iff_integral_pos m μ hμ N, ?_⟩
  rw [posDef_iff_integral_pos m μ hμ N]
  have _ : IsFiniteMeasure μ := hμ.1.finite
  have link : ∀ c : Fin (N+1) → ℂ,
      (0 < ∫ x in Set.Icc (0:ℝ) 1, ‖pc c x‖ ^ 2 ∂μ) ↔
      μ ({x : ℝ | (polyOf c).eval (x : ℂ) = 0} ∩ Set.Icc (0:ℝ) 1) < μ (Set.Icc (0:ℝ) 1) := by
    intro c
    have hnn : 0 ≤ ∫ x in Set.Icc (0:ℝ) 1, ‖pc c x‖ ^ 2 ∂μ :=
      setIntegral_nonneg measurableSet_Icc (fun x _ => by positivity)
    have h0 := integral_eq_zero_iff_ae μ (fun x => ‖pc c x‖ ^ 2)
      (continuous_normsq_pc c) (fun x => by positivity)
    have h1 := ae_zero_iff_measure_zeroSet μ (fun x => ‖pc c x‖ ^ 2) (continuous_normsq_pc c)
    have hset : {x : ℝ | ‖pc c x‖ ^ 2 = 0} = {x : ℝ | (polyOf c).eval (x : ℂ) = 0} := by
      ext x
      simp [pc_eq_eval]
    rw [hset] at h1
    have hle : μ ({x : ℝ | (polyOf c).eval (x : ℂ) = 0} ∩ Set.Icc (0:ℝ) 1)
        ≤ μ (Set.Icc (0:ℝ) 1) := measure_mono Set.inter_subset_right
    constructor
    · intro hpos
      refine lt_of_le_of_ne hle (fun heq => ?_)
      have hI0 : ∫ x in Set.Icc (0:ℝ) 1, ‖pc c x‖ ^ 2 ∂μ = 0 :=
        h0.mpr (h1.mpr heq)
      exact hpos.ne' hI0
    · intro hlt
      refine lt_of_le_of_ne hnn (fun heq => hlt.ne ?_)
      exact h1.mp (h0.mp heq.symm)
  constructor
  · intro h p hp hdeg
    obtain ⟨c, hcp, hc⟩ := exists_c_of_natDegree_le p hdeg
    rw [← hcp]
    exact (link c).mp (h c (hc hp))
  · intro h c hc
    exact (link c).mpr (h (polyOf c) (polyOf_ne_zero hc) (degree_polyOf_le c))


lemma posDef_dotProduct_pos {m : ℕ → ℝ} {N : ℕ} (hpd : (hankel' m N).PosDef)
    (c : Fin (N + 1) → ℂ) (hc : c ≠ 0) :
    0 < star c ⬝ᵥ (hankel' m N) *ᵥ c := by
  have h := hpd.dotProduct_mulVec_pos hc
  simpa using h

theorem posDef_imp_elementary (m : ℕ → ℝ) (N : ℕ)
    (hpd : (hankel' m N).PosDef)
    {x lam : (q : ℕ) → Fin q → ℝ} (h : IsElementaryResolution m N x lam)
    (c : Fin (N + 1) → ℂ) (hc : c ≠ 0) :
    ∃ L : ℝ, 0 < L ∧ Filter.Tendsto
      (fun q : ℕ => ∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2) Filter.atTop (nhds L) := by
  have hpos := posDef_dotProduct_pos hpd c hc
  rw [dotProduct_hankel_eq_quadForm] at hpos
  have hlim := tendsto_sum_normsq h c
  refine ⟨(quadForm m N c).re, ?_, ?_⟩
  · exact Complex.pos_iff.mp hpos |>.1
  · have h2 := (Complex.continuous_re.tendsto _).comp hlim
    have h3 : (Complex.re ∘ fun q : ℕ =>
        ((∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2 : ℝ) : ℂ))
        = fun q : ℕ => ∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2 := by
      funext q
      simp only [Function.comp_apply, Complex.ofReal_re]
    rw [h3] at h2
    exact h2


-----------------------------------------------------------------------

lemma moments_unique (S : ℕ → ℕ → ℝ) (m m' : ℕ → ℝ)
    (h1 : ∀ k, Filter.Tendsto (fun q => S k q) Filter.atTop (nhds (m k)))
    (h2 : ∀ k, Filter.Tendsto (fun q => S k q) Filter.atTop (nhds (m' k))) :
    m = m' := by
  funext k
  exact tendsto_nhds_unique (h1 k) (h2 k)

lemma Sq_eq_double_sum (x lam : (q : ℕ) → Fin q → ℝ) (N : ℕ)
    (c : Fin (N + 1) → ℂ) (q : ℕ) :
    ((∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2 : ℝ) : ℂ)
      = ∑ i : Fin (N+1), ∑ j : Fin (N+1),
          star (c i) * c j * ((∑ r : Fin q, lam q r * (x q r) ^ (i.val + j.val) : ℝ) : ℂ) := by
  have h := sum_normsq_pc_eq c q (x q) (lam q)
  simpa only [Complex.star_def] using h

lemma tendsto_Sq_quadForm (m : ℕ → ℝ) (N : ℕ)
    {x lam : (q : ℕ) → Fin q → ℝ} (h : IsElementaryResolution m N x lam)
    (c : Fin (N + 1) → ℂ) :
    Filter.Tendsto (fun q : ℕ => ∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2)
      Filter.atTop (nhds (quadForm m N c).re) := by
  have hlim := tendsto_sum_normsq h c
  have h2 := (Complex.continuous_re.tendsto _).comp hlim
  have h3 : (Complex.re ∘ fun q : ℕ =>
      ((∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2 : ℝ) : ℂ))
      = fun q : ℕ => ∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2 := by
    funext q
    simp only [Function.comp_apply, Complex.ofReal_re]
  rw [h3] at h2
  exact h2

lemma posDef_iff_limit_pos_vec (m : ℕ → ℝ) (N : ℕ)
    {x lam : (q : ℕ) → Fin q → ℝ} (h : IsElementaryResolution m N x lam) :
    (hankel' m N).PosDef ↔
      ∀ c : Fin (N+1) → ℂ, c ≠ 0 → ∃ L : ℝ, 0 < L ∧ Filter.Tendsto
        (fun q : ℕ => ∑ r : Fin q, lam q r *
        ‖pc c (x q r)‖ ^ 2) Filter.atTop (nhds L) := by
  constructor
  · intro hpd c hc
    exact posDef_imp_elementary m N hpd h c hc
  · intro hall
    refine ⟨hankel_isHermitian m N, fun c hc => ?_⟩
    have hc' : (⇑c : Fin (N+1) → ℂ) ≠ 0 := by
      intro h0
      apply hc
      ext i
      exact congrFun h0 i
    obtain ⟨L, hL, hlim⟩ := hall (⇑c) hc'
    have hlimC := tendsto_sum_normsq h (⇑c)
    have hre := (Complex.continuous_re.tendsto _).comp hlimC
    have hre' : Filter.Tendsto
        (fun q : ℕ => ∑ r : Fin q, lam q r * ‖pc (⇑c) (x q r)‖ ^ 2)
        Filter.atTop (nhds (quadForm m N (⇑c)).re) := by
      have h3 : (Complex.re ∘ fun q : ℕ =>
          (((∑ r : Fin q, lam q r * ‖pc (⇑c) (x q r)‖ ^ 2 : ℝ)) : ℂ)) =
          fun q : ℕ => ∑ r : Fin q, lam q r * ‖pc (⇑c) (x q r)‖ ^ 2 := by
        funext q
        simp only [Function.comp_apply, Complex.ofReal_re]
      rw [h3] at hre
      exact hre
    have hLeq : L = (quadForm m N (⇑c)).re := tendsto_nhds_unique hlim hre'
    have himq : (quadForm m N (⇑c)).im = 0 := by
      have him := (Complex.continuous_im.tendsto _).comp hlimC
      have h4 : (Complex.im ∘ fun q : ℕ =>
          (((∑ r : Fin q, lam q r * ‖pc (⇑c) (x q r)‖ ^ 2 : ℝ)) : ℂ)) =
          fun _ : ℕ => (0 : ℝ) := by
        funext q
        simp only [Function.comp_apply, Complex.ofReal_im]
      rw [h4] at him
      exact tendsto_nhds_unique him tendsto_const_nhds
    have hpos : 0 < quadForm m N (⇑c) := by
      rw [Complex.pos_iff]
      exact ⟨hLeq ▸ hL, himq.symm⟩
    rw [← dotProduct_hankel_eq_quadForm] at hpos
    have hsum : (c.sum fun i xi => c.sum fun j xj => star xi * hankel' m N i j * xj)
        = star ⇑c ⬝ᵥ hankel' m N *ᵥ ⇑c := by
      rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Finsupp.sum_fintype _ _ (by intro j; simp)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hsum]
    exact hpos

lemma posDef_iff_limit_pos_poly (m : ℕ → ℝ) (N : ℕ)
    {x lam : (q : ℕ) → Fin q → ℝ} (h : IsElementaryResolution m N x lam) :
    (hankel' m N).PosDef ↔
      ∀ P : Polynomial ℂ, P ≠ 0 → P.natDegree ≤ N →
        ∃ L : ℝ, 0 < L ∧ Filter.Tendsto (fun q : ℕ => Sq x lam P q) Filter.atTop (nhds L) := by
  rw [posDef_iff_limit_pos_vec m N h]
  constructor
  · intro hv P hP hdeg
    obtain ⟨c, hcp, hc⟩ := exists_c_of_natDegree_le P hdeg
    obtain ⟨L, hL, hlim⟩ := hv c (hc hP)
    refine ⟨L, hL, ?_⟩
    have hfun : (fun q : ℕ => Sq x lam P q)
        = fun q : ℕ => ∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2 := by
      funext q
      simp only [Sq, pc_eq_eval, hcp]
    rw [hfun]
    exact hlim
  · intro hp c hc
    obtain ⟨L, hL, hlim⟩ := hp (polyOf c) (polyOf_ne_zero hc) (degree_polyOf_le c)
    refine ⟨L, hL, ?_⟩
    have hfun : (fun q : ℕ => Sq x lam (polyOf c) q)
        = fun q : ℕ => ∑ r : Fin q, lam q r * ‖pc c (x q r)‖ ^ 2 := by
      funext q
      simp only [Sq, pc_eq_eval]
    rw [← hfun]
    exact hlim

lemma tendsto_of_sub_tendsto_zero (a b : ℕ → ℝ) (L : ℝ)
    (hab : Filter.Tendsto (fun q => a q - b q) Filter.atTop (nhds 0))
    (hb : Filter.Tendsto b Filter.atTop (nhds L)) :
    Filter.Tendsto a Filter.atTop (nhds L) := by
  have h2 := hab.add hb
  have h3 : (fun q => (a q - b q) + b q) = a := by
    funext q; simp
  rw [h3, zero_add] at h2
  exact h2

theorem suite_unique_positivite
    (m : ℕ → ℝ)
    (N : ℕ)
    {x lam : (q : ℕ) → Fin q → ℝ}
    (h : IsElementaryResolution m N x lam) :
    (∀ (S : ℕ → ℕ → ℝ) (m' : ℕ → ℝ),
        (∀ k, Filter.Tendsto (fun q => S k q)
          Filter.atTop (nhds (m k))) →
        (∀ k, Filter.Tendsto (fun q => S k q) Filter.atTop (nhds (m' k))) → m = m') ∧
    ((hankel' m N).PosDef ↔
      ∀ P : Polynomial ℂ, P ≠ 0 → P.natDegree ≤ N →
        ∃ L : ℝ, 0 < L ∧ Filter.Tendsto (fun q : ℕ => Sq x lam P q)
        Filter.atTop (nhds L)) :=
  ⟨fun S m' h1 h2 => moments_unique S m m' h1 h2,
  posDef_iff_limit_pos_poly m N h⟩




end DefPosHankelRes
