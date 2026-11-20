import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.ExistQ_Annulator
import ThEqRiemann.IntegralResolutionTheorem.DefPosHankelResInt
import ThEqRiemann.EqTheorem.Vandermonde

/-! -/
namespace SpecSupportHankel

open Matrix Complex
open scoped ComplexConjugate ComplexOrder
open ResDef


lemma rec_of_atoms_roots (m : ℕ → ℝ) (D : ℕ) (pts w a : Fin D → ℝ)
    (hm : ∀ k, m k = ∑ i, w i * pts i ^ k)
    (hroot : ∀ i : Fin D, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0) :
    ∀ n : ℕ, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ)) := by
  intro n
  have key : ∀ i : Fin D,
      w i * pts i ^ (n + D) = ∑ j : Fin D, a j * (w i * pts i ^ (n + (j : ℕ))) := by
    intro i
    have h' : pts i ^ D = ∑ j : Fin D, a j * pts i ^ (j : ℕ) := sub_eq_zero.mp (hroot i)
    calc w i * pts i ^ (n + D)
        = w i * pts i ^ n * pts i ^ D := by rw [pow_add]; ring
      _ = w i * pts i ^ n * ∑ j : Fin D, a j * pts i ^ (j : ℕ) := by rw [h']
      _ = ∑ j : Fin D, w i * pts i ^ n * (a j * pts i ^ (j : ℕ)) := by rw [Finset.mul_sum]
      _ = ∑ j : Fin D, a j * (w i * pts i ^ (n + (j : ℕ))) := by
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [pow_add]; ring
  calc m (n + D)
      = ∑ i, w i * pts i ^ (n + D) := hm _
    _ = ∑ i, ∑ j : Fin D, a j * (w i * pts i ^ (n + (j : ℕ))) :=
        Finset.sum_congr rfl (fun i _ => key i)
    _ = ∑ j : Fin D, ∑ i, a j * (w i * pts i ^ (n + (j : ℕ))) := Finset.sum_comm
    _ = ∑ j : Fin D, a j * m (n + (j : ℕ)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hm (n + (j : ℕ)), Finset.mul_sum]


lemma exists_coeffs_of_atoms (D : ℕ) (pts : Fin D → ℝ) :
    ∃ a : Fin D → ℝ, ∀ i : Fin D, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0 := by
  classical
  set P : Polynomial ℝ := ∏ i : Fin D, (Polynomial.X - Polynomial.C (pts i)) with hP
  have hmon : P.Monic := Polynomial.monic_prod_of_monic _ _
    (fun i _ => Polynomial.monic_X_sub_C (pts i))
  have hdeg : P.natDegree = D := by
    rw [hP, Polynomial.natDegree_prod_of_monic _ _
      (fun i _ => Polynomial.monic_X_sub_C (pts i))]
    simp
  refine ⟨fun j => - P.coeff (j : ℕ), fun i => ?_⟩
  have hev : P.eval (pts i) = 0 := by
    rw [hP, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  have hsum := Polynomial.eval_eq_sum_range (p := P) (pts i)
  have hlead : P.coeff D = 1 := by
    have := hmon.coeff_natDegree
    rwa [hdeg] at this
  have hfin : ∑ x ∈ Finset.range D, P.coeff x * pts i ^ x
      = ∑ j : Fin D, P.coeff (j : ℕ) * pts i ^ (j : ℕ) :=
    (Fin.sum_univ_eq_sum_range (fun x => P.coeff x * pts i ^ x) D).symm
  rw [hdeg] at hsum
  rw [hev, Finset.sum_range_succ, hlead, hfin] at hsum
  change pts i ^ D - ∑ j : Fin D, (-P.coeff (j : ℕ)) * pts i ^ (j : ℕ) = 0
  simp only [neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  linarith

lemma kernel_of_rec (m : ℕ → ℝ) (D : ℕ) (a : Fin D → ℝ)
    (hrec : ∀ n : ℕ, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ))) :
    ∀ i : Fin (D + 1),
      ∑ j : Fin (D + 1), m ((i : ℕ) + (j : ℕ)) *
        (if h : (j : ℕ) < D then - a ⟨j, h⟩ else 1) = 0 := by
  intro i
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.is_lt, dite_true, Fin.val_last, lt_irrefl, dite_false,
    mul_one]
  have h := hrec (i : ℕ)
  have this : ∑ j : Fin D, m ((i : ℕ) + (j : ℕ)) * (- a j)
      = - ∑ j : Fin D, a j * m ((i : ℕ) + (j : ℕ)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [this]
  linarith

open ExistQ MeasureTheory VandermondeThEq


theorem synthese_direct (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (D : ℕ) (hD : 1 ≤ D)
    (hpos : (hk m D).PosDef) (hdet : (hk m (D + 1)).det = 0) :
    ∃ (a : Fin D → ℝ) (pts w : Fin D → ℝ),
      Function.Injective pts ∧ (∀ i, pts i ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ i, 0 < w i) ∧ (∀ k, m k = ∑ i, w i * pts i ^ k) ∧
      (∀ i, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0) ∧
      (∀ n, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ))) := by
  obtain ⟨pts, w, hinj, hmem, hw, hm⟩ := critical_order_support m μ hμ D hD hpos hdet
  obtain ⟨a, ha, -⟩ := exists_unique_coeffs m D hpos
  obtain ⟨hroot, hrec⟩ :=
    atoms_root_and_rec m D pts w hw hm a ha (vandermonde_inj_zero D pts hinj)
  exact ⟨a, pts, w, hinj, hmem, hw, hm, hroot, hrec⟩

theorem synthese_reciproque_atomes (m : ℕ → ℝ) (D : ℕ) (pts w : Fin D → ℝ)
    (hm : ∀ k, m k = ∑ i, w i * pts i ^ k) :
    ∃ a : Fin D → ℝ,
      (∀ i, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0) ∧
      (∀ n, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ))) := by
  obtain ⟨a, hroot⟩ := exists_coeffs_of_atoms D pts
  exact ⟨a, hroot, rec_of_atoms_roots m D pts w a hm hroot⟩

lemma det_hk_eq_zero_of_rec (m : ℕ → ℝ) (D : ℕ) (a : Fin D → ℝ)
    (hrec : ∀ n : ℕ, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ))) :
    (hk m (D + 1)).det = 0 := by
  set v : Fin (D + 1) → ℂ :=
    fun j => ((if h : (j : ℕ) < D then - a ⟨j, h⟩ else 1 : ℝ) : ℂ) with hv
  have hvne : v ≠ 0 := by
    intro h
    have := congrFun h (Fin.last D)
    simp [hv] at this
  have hker : (hk m (D + 1)).mulVec v = 0 := by
    funext i
    have := kernel_of_rec m D a hrec i
    simp only [Matrix.mulVec, dotProduct, hk, Matrix.of_apply, Pi.zero_apply, hv]
    exact_mod_cast this
  exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, hker⟩

open DefPosHankelRes in
theorem hankel_posDef_iff_support (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (k : ℕ) :
    (hk m (k + 1)).PosDef ↔ ¬ ∃ T : Finset ℝ, T.card ≤ k ∧ μ (Set.Icc 0 1 \ (T : Set ℝ)) = 0 := by
  classical
  constructor
  · exact support_card_ge m μ hμ k
  · intro hno
    have hH := (positivite_hankel_resolution m μ hμ k).right
    rw [hk_succ_eq_hankel m k]
    refine hH.mpr ?_
    intro P hP0 hPdeg
    have hfin : μ (Set.Icc (0 : ℝ) 1) ≠ ⊤ := by
      have _ : IsFiniteMeasure μ := hμ.1.finite
      exact MeasureTheory.measure_ne_top μ _
    set Z : Finset ℝ :=
      (P.roots.toFinset.image Complex.re).filter
        (fun x => Polynomial.eval (x : ℂ) P = 0) with hZ
    have hZcard : Z.card ≤ k := by
      calc Z.card ≤ (P.roots.toFinset.image Complex.re).card := Finset.card_filter_le _ _
        _ ≤ P.roots.toFinset.card := Finset.card_image_le
        _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' P
        _ ≤ k := hPdeg
    have hZsub : {x : ℝ | Polynomial.eval (x : ℂ) P = 0} ⊆ (Z : Set ℝ) := by
      intro x hx
      simp only [Set.mem_ofPred_eq] at hx
      simp only [hZ, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_image,
        Multiset.mem_toFinset]
      refine ⟨⟨(x : ℂ), (Polynomial.mem_roots hP0).mpr hx, Complex.ofReal_re x⟩, hx⟩
    refine lt_of_le_of_ne (MeasureTheory.measure_mono Set.inter_subset_right) (fun heq => ?_)
    apply hno
    refine ⟨Z, hZcard, ?_⟩
    have hsplit := MeasureTheory.measure_sdiff_add_inter (μ := μ)
      (Set.Icc (0 : ℝ) 1) (Z.finite_toSet.measurableSet)
    have hle : μ (Set.Icc (0 : ℝ) 1) ≤ μ (Set.Icc (0 : ℝ) 1 ∩ (Z : Set ℝ)) := by
      calc μ (Set.Icc (0 : ℝ) 1)
          = μ ({x : ℝ | Polynomial.eval (x : ℂ) P = 0} ∩ Set.Icc 0 1) := heq.symm
        _ ≤ μ (Set.Icc (0 : ℝ) 1 ∩ (Z : Set ℝ)) := by
            apply MeasureTheory.measure_mono
            intro x hx
            exact ⟨hx.2, hZsub hx.1⟩
    have hge : μ (Set.Icc (0 : ℝ) 1 ∩ (Z : Set ℝ)) ≤ μ (Set.Icc (0 : ℝ) 1) :=
      MeasureTheory.measure_mono Set.inter_subset_left
    have heq2 : μ (Set.Icc (0 : ℝ) 1 ∩ (Z : Set ℝ)) = μ (Set.Icc (0 : ℝ) 1) :=
      le_antisymm hge hle
    rw [heq2] at hsplit
    have h0 : μ (Set.Icc (0 : ℝ) 1 \ (Z : Set ℝ)) + μ (Set.Icc (0 : ℝ) 1)
        = 0 + μ (Set.Icc (0 : ℝ) 1) := by rw [zero_add]; exact hsplit
    exact (ENNReal.add_left_inj hfin).mp h0

lemma hk_isHermitian (m : ℕ → ℝ) (D : ℕ) : (hk m D).IsHermitian := by
  ext i j
  simp [hk, Matrix.conjTranspose_apply, add_comm]


lemma posDef_of_atoms (m : ℕ → ℝ) (D : ℕ) (pts w : Fin D → ℝ)
    (hinj : Function.Injective pts) (hw : ∀ i, 0 < w i)
    (hm : ∀ k, m k = ∑ i, w i * pts i ^ k) :
    (hk m D).PosDef := by
  classical
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [hk, Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def,
      Complex.conj_ofReal, add_comm (i : ℕ) (j : ℕ)]
  · intro x hx0
    set c : Fin D → ℂ := fun i => x i with hc
    have hsum : (x.sum fun i xi => x.sum fun j xj => star xi * hk m D i j * xj)
        = ∑ i : Fin D, ∑ j : Fin D, star (c i) * ((m ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ) * c j := by
      rw [Finsupp.sum_fintype]
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finsupp.sum_fintype]
        · refine Finset.sum_congr rfl (fun j _ => ?_)
          simp only [hk, Matrix.of_apply, hc]
        · intro j; simp
      · intro i; simp
    have hq : ∑ i : Fin D, ∑ j : Fin D, star (c i) * ((m ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ) * c j
        = ∑ a : Fin D, (w a : ℂ) * ((Complex.normSq (∑ j : Fin D, c j *
          (pts a : ℂ) ^ (j : ℕ)) : ℝ) : ℂ) := by
      have hA : ∀ i j : Fin D, star (c i) * ((m ((i : ℕ) + (j : ℕ)) : ℝ) : ℂ) * c j
          = ∑ a : Fin D, (w a : ℂ) * (star (c i) * (pts a : ℂ) ^ (i : ℕ) *
            ((pts a : ℂ) ^ (j : ℕ) * c j)) := by
        intro i j
        rw [hm, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        push_cast
        ring
      simp_rw [hA]
      calc ∑ i : Fin D, ∑ j : Fin D, ∑ a : Fin D,
              (w a : ℂ) * (star (c i) * (pts a : ℂ) ^ (i : ℕ) *
                ((pts a : ℂ) ^ (j : ℕ) * c j))
          = ∑ i : Fin D, ∑ a : Fin D, ∑ j : Fin D,
              (w a : ℂ) * (star (c i) * (pts a : ℂ) ^ (i : ℕ) *
                ((pts a : ℂ) ^ (j : ℕ) * c j)) := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            exact Finset.sum_comm
        _ = ∑ a : Fin D, ∑ i : Fin D, ∑ j : Fin D,
              (w a : ℂ) * (star (c i) * (pts a : ℂ) ^ (i : ℕ) *
                ((pts a : ℂ) ^ (j : ℕ) * c j)) :=
            Finset.sum_comm
        _ = ∑ a : Fin D, (w a : ℂ) * ((Complex.normSq (∑ j : Fin D, c j *
          (pts a : ℂ) ^ (j : ℕ)) : ℝ) : ℂ) := by
            refine Finset.sum_congr rfl (fun a _ => ?_)
            rw [Complex.normSq_eq_conj_mul_self, map_sum]
            simp only [Complex.conj_ofReal, map_mul, map_pow,
              Finset.mul_sum, Finset.sum_mul]
            refine Eq.trans ?_ Finset.sum_comm
            refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
            rw [Complex.star_def]
            ring
    rw [hsum, hq]
    set s : Fin D → ℝ := fun a => w a * Complex.normSq (∑ j, c j * (pts a : ℂ) ^ (j : ℕ)) with hs
    have hcast : ∑ a, (w a : ℂ) * ((Complex.normSq (∑ j, c j * (pts a : ℂ) ^ (j : ℕ)) : ℝ) : ℂ)
        = ((∑ a, s a : ℝ) : ℂ) := by
      simp [hs, Complex.ofReal_sum]
    rw [hcast]
    have hpos : 0 < ∑ a, s a := by
      have hnn : ∀ a, 0 ≤ s a := fun a => mul_nonneg (hw a).le (Complex.normSq_nonneg _)
      by_contra hle
      push Not at hle
      have hz : ∀ a ∈ Finset.univ, s a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).mp
          (le_antisymm hle (Finset.sum_nonneg (fun a _ => hnn a)))
      have hroot : ∀ a, ∑ j : Fin D, c j * (pts a : ℂ) ^ (j : ℕ) = 0 := by
        intro a
        have h := hz a (Finset.mem_univ a)
        simp only [hs] at h
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h (hw a).ne'
        · exact Complex.normSq_eq_zero.mp h
      have hc0 : c = 0 := vandermonde_zero_of_roots_complex D pts hinj c hroot
      apply hx0
      ext i
      have := congrFun hc0 i
      simpa [hc] using this
    exact_mod_cast hpos

theorem equivalence_finale (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) (D : ℕ) (hD : 1 ≤ D) :
    let I : Prop := (hk m D).PosDef ∧ (hk m (D + 1)).det = 0
    let II : Prop := ∃ (pts w : Fin D → ℝ), Function.Injective pts ∧
        (∀ i, pts i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, 0 < w i) ∧
        ∀ k, m k = ∑ i, w i * pts i ^ k
    let III : Prop := (∃ a : Fin D → ℝ,
        ∀ n, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ))) ∧ (hk m D).PosDef
    (I → II) ∧ (II → III) ∧ (III → I) := by
  intro I II III
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨hpos, hdet⟩
    obtain ⟨a, pts, w, hinj, hmem, hw, hm, -, -⟩ := synthese_direct m μ hμ D hD hpos hdet
    exact ⟨pts, w, hinj, hmem, hw, hm⟩
  · rintro ⟨pts, w, hinj, hmem, hw, hm⟩
    obtain ⟨a, -, hrec⟩ := synthese_reciproque_atomes m D pts w hm
    refine ⟨⟨a, hrec⟩, posDef_of_atoms m D pts w hinj hw hm⟩
  · rintro ⟨⟨a, hrec⟩, hpos⟩
    refine ⟨hpos, ?_⟩
    exact det_hk_eq_zero_of_rec m D a hrec

theorem synthese_caracterisation_hankel (m : ℕ → ℝ) (μ : Measure ℝ)
    (hμ : IsIntegralResolution m μ) :
    (∀ k : ℕ, (hk m (k + 1)).PosDef ↔
      ¬ ∃ T : Finset ℝ, T.card ≤ k ∧ μ (Set.Icc 0 1 \ (T : Set ℝ)) = 0) ∧
    (∀ D : ℕ, 1 ≤ D → (hk m D).PosDef → (hk m (D + 1)).det = 0 →
      ∃ (a : Fin D → ℝ) (pts w : Fin D → ℝ),
        Function.Injective pts ∧ (∀ i, pts i ∈ Set.Icc (0 : ℝ) 1) ∧
        (∀ i, 0 < w i) ∧ (∀ k, m k = ∑ i, w i * pts i ^ k) ∧
        (∀ i, pts i ^ D - ∑ j : Fin D, a j * pts i ^ (j : ℕ) = 0) ∧
        (∀ n, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ)))) ∧
    (∀ D : ℕ, 1 ≤ D →
      (((hk m D).PosDef ∧ (hk m (D + 1)).det = 0) ↔
        (∃ (pts w : Fin D → ℝ), Function.Injective pts ∧
          (∀ i, pts i ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ i, 0 < w i) ∧
          ∀ k, m k = ∑ i, w i * pts i ^ k)) ∧
      (((hk m D).PosDef ∧ (hk m (D + 1)).det = 0) ↔
        ((∃ a : Fin D → ℝ,
            ∀ n, m (n + D) = ∑ j : Fin D, a j * m (n + (j : ℕ))) ∧ (hk m D).PosDef))) := by
  refine ⟨fun k => hankel_posDef_iff_support m μ hμ k, ?_, ?_⟩
  · intro D hD hpos hdet
    exact synthese_direct m μ hμ D hD hpos hdet
  · intro D hD
    obtain ⟨h12, h23, h31⟩ := equivalence_finale m μ hμ D hD
    exact ⟨⟨h12, fun h => h31 (h23 h)⟩, ⟨fun h => h23 (h12 h), h31⟩⟩


theorem synthese_hankel_alignement
    (m : ℕ → ℝ) (D : ℕ) (pts w : Fin D → ℝ)
    (hinj : Function.Injective pts) (hw : ∀ i, 0 < w i)
    (hm : ∀ k, m k = ∑ i, w i * pts i ^ k) :
    (hk m D).PosDef ∧
    ∃ Q : Polynomial ℝ, Q.Monic ∧ Q.natDegree = D ∧
      ∀ i, Q.IsRoot (pts i) := by
  refine ⟨posDef_of_atoms m D pts w hinj hw hm, ?_⟩
  refine ⟨∏ i : Fin D, (Polynomial.X - Polynomial.C (pts i)), ?_, ?_, ?_⟩
  · exact Polynomial.monic_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)
  · rw [Polynomial.natDegree_prod_of_monic _ _ (fun i _ => Polynomial.monic_X_sub_C _)]
    simp
  · intro i
    rw [Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)



end SpecSupportHankel
