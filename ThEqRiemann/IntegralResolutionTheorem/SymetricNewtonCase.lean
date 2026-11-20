import mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef

/-! -/
namespace SymNewtonCase

open Set Complex Module End
open ResDef

lemma summable_norm_pow {z : ℕ → ℂ} (hsum : Summable (fun j => ‖z j‖))
    {k : ℕ} (hk : 1 ≤ k) : Summable (fun j => ‖z j ^ k‖) := by
  have hlim : Filter.Tendsto (fun j => ‖z j‖) Filter.atTop (nhds 0) :=
    hsum.tendsto_atTop_zero
  have hev : ∀ᶠ j in Filter.atTop, ‖z j‖ ≤ 1 :=
    hlim.eventually (Iic_mem_nhds zero_lt_one)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  rw [← summable_nat_add_iff N]
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    ((summable_nat_add_iff N).mpr hsum)
  rw [norm_pow]
  exact pow_le_of_le_one (norm_nonneg _) (hN (j + N)
    (by omega)) (by omega)

lemma sum_eq_sum_re (s : Multiset ℂ) (hs : s.map (starRingEnd ℂ) = s) :
    s.sum = (((s.map Complex.re).sum : ℝ) : ℂ) := by
  have h1 : (starRingEnd ℂ) s.sum = s.sum := by
    have : (starRingEnd ℂ) s.sum = (s.map (starRingEnd ℂ)).sum :=
      map_multiset_sum (starRingEnd ℂ) s
    rw [this, hs]
  have h2 : s.sum.im = 0 := by
    have := congrArg Complex.im h1
    rw [Complex.conj_im] at this
    linarith
  have h3 : s.sum.re = (s.map Complex.re).sum :=
    map_multiset_sum Complex.reAddGroupHom s
  apply Complex.ext
  · simp [h3]
  · simp [h2]

lemma prod_X_sub_mem_realPoly' (s : Multiset ℂ) (hs : s.map (starRingEnd ℂ) = s) :
    ∃ Q : Polynomial ℝ, Q.map (algebraMap ℝ ℂ) =
      (s.map (fun z => Polynomial.X - Polynomial.C z)).prod := by
  set P : Polynomial ℂ := (s.map (fun z => Polynomial.X - Polynomial.C z)).prod with hP
  have hfix : P.map (starRingEnd ℂ) = P := by
    rw [hP, Polynomial.map_multiset_prod, Multiset.map_map]
    have h2 : s.map ((Polynomial.map (starRingEnd ℂ)) ∘
        fun z => Polynomial.X - Polynomial.C z) =
        (s.map (starRingEnd ℂ)).map (fun z => Polynomial.X - Polynomial.C z) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl (fun z _ => ?_)
      simp [Polynomial.map_sub]
    rw [h2, hs]
  have hreal : ∀ n, (starRingEnd ℂ) (P.coeff n) = P.coeff n := by
    intro n
    have := congrArg (fun q => Polynomial.coeff q n) hfix
    simpa [Polynomial.coeff_map] using this
  refine ⟨∑ n ∈ P.support, Polynomial.monomial n (P.coeff n).re, ?_⟩
  ext n
  simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n ∈ P.support
  · rw [Finset.sum_ite_eq' P.support n, ite_eq_left hn]
    exact Complex.conj_eq_iff_re.mp (hreal n)
  · rw [Finset.sum_ite_eq' P.support n, ite_eq_right hn]
    have h0 : P.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    rw [h0]
    simp

lemma prod_X_sub_coeff_real (s : Multiset ℂ) (hs : s.map (starRingEnd ℂ) = s) (n : ℕ) :
    ((s.map (fun z => Polynomial.X - Polynomial.C z)).prod).coeff n =
      (((s.map (fun z => Polynomial.X - Polynomial.C z)).prod.coeff n).re : ℂ) := by
  set P : Polynomial ℂ := (s.map (fun z => Polynomial.X - Polynomial.C z)).prod with hP
  have hfix : P.map (starRingEnd ℂ) = P := by
    rw [hP, Polynomial.map_multiset_prod, Multiset.map_map]
    have h2 : s.map ((Polynomial.map (starRingEnd ℂ)) ∘
        fun z => Polynomial.X - Polynomial.C z) =
        (s.map (starRingEnd ℂ)).map (fun z => Polynomial.X - Polynomial.C z) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl (fun z _ => ?_)
      simp [Polynomial.map_sub]
    rw [h2, hs]
  have h1 : (starRingEnd ℂ) (P.coeff n) = P.coeff n := by
    have := congrArg (fun q => Polynomial.coeff q n) hfix
    simpa [Polynomial.coeff_map] using this
  exact (Complex.conj_eq_iff_re.mp h1).symm


lemma prod_X_sub_mem_realPoly (s : Multiset ℂ) (hs : s.map (starRingEnd ℂ) = s) :
    ∃ Q : Polynomial ℝ, Q.map (algebraMap ℝ ℂ) =
      (s.map (fun z => Polynomial.X - Polynomial.C z)).prod := by
  set P : Polynomial ℂ := (s.map (fun z => Polynomial.X - Polynomial.C z)).prod with hP
  have hco : ∀ n, P.coeff n = ((P.coeff n).re : ℂ) := fun n =>
    prod_X_sub_coeff_real s hs n
  refine ⟨∑ n ∈ P.support, Polynomial.monomial n (P.coeff n).re, ?_⟩
  ext n
  simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  by_cases hn : n ∈ P.support
  · rw [Finset.sum_eq_single n (fun b _ hb => by simp [hb]) (fun h => absurd hn h)]
    rw [ite_eq_left rfl]
    exact (hco n).symm
  · have h0 : P.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    rw [Finset.sum_eq_zero (fun b hb => by
      have : b ≠ n := fun h => hn (h ▸ hb)
      simp [this])]
    simp [h0]


theorem symetrie_zeros_newton_reel
    {z : ℕ → ℂ} (hsum : Summable (fun j => ‖z j‖))
    {n : ℕ → ℕ} (hn : Filter.Tendsto n Filter.atTop Filter.atTop)
    (hconj : ∀ N, ((Finset.range (n N)).val.map z).map (starRingEnd ℂ) =
      (Finset.range (n N)).val.map z) :
    (∀ N m, (((Finset.range (n N)).val.map
        (fun w => Polynomial.X - Polynomial.C (z w))).prod.coeff m) =
      ((((Finset.range (n N)).val.map
        (fun w => Polynomial.X - Polynomial.C (z w))).prod.coeff m).re : ℂ)) ∧
    (∀ k ≥ 1, Summable (fun j => ‖z j ^ k‖)) ∧
    (∀ k ≥ 1, (starRingEnd ℂ) (∑' j, z j ^ k) = ∑' j, z j ^ k) ∧
    Filter.Tendsto
      (fun N => ∑ j ∈ Finset.range (n N), (z j).re) Filter.atTop
      (nhds (∑' j, (z j).re)) := by
  classical
  have hcoeff : ∀ N m,
      (((Finset.range (n N)).val.map
          (fun w => Polynomial.X - Polynomial.C (z w))).prod.coeff m) =
        ((((Finset.range (n N)).val.map
          (fun w => Polynomial.X - Polynomial.C (z w))).prod.coeff m).re : ℂ) := by
    intro N m
    simpa [Multiset.map_map, Function.comp_def] using
      (prod_X_sub_coeff_real ((Finset.range (n N)).val.map z) (hconj N) m)
  have hpow : ∀ k ≥ 1, Summable (fun j => z j ^ k) := by
    intro k hk
    exact (summable_norm_pow hsum hk).of_norm
  have hrealpow : ∀ k ≥ 1,
      (starRingEnd ℂ) (∑' j, z j ^ k) = ∑' j, z j ^ k := by
    intro k hk
    have hfin : ∀ N,
        (starRingEnd ℂ) (∑ j ∈ Finset.range (n N), z j ^ k) =
          ∑ j ∈ Finset.range (n N), z j ^ k := by
      intro N
      have hc := congrArg
        (fun s : Multiset ℂ => (s.map (fun w => w ^ k)).sum) (hconj N)
      simp only [Multiset.map_map, Function.comp_def] at hc
      rw [map_sum]
      simpa [map_pow, Finset.sum_eq_multiset_sum] using hc
    have ht : Filter.Tendsto
        (fun N => ∑ j ∈ Finset.range (n N), z j ^ k)
        Filter.atTop (nhds (∑' j, z j ^ k)) :=
      (hpow k hk).hasSum.tendsto_sum_nat.comp hn
    have ht' : Filter.Tendsto
        (fun N => (starRingEnd ℂ) (∑ j ∈ Finset.range (n N), z j ^ k))
        Filter.atTop (nhds ((starRingEnd ℂ) (∑' j, z j ^ k))) :=
      (Complex.continuous_conj.tendsto _).comp ht
    exact tendsto_nhds_unique ht' (by simpa [hfin] using ht)
  have hsum_re : Summable (fun j => (z j).re) := by
    refine Summable.of_norm_bounded hsum (fun j => ?_)
    simpa using Complex.abs_re_le_norm (z j)
  exact ⟨hcoeff, fun k hk => summable_norm_pow hsum hk, hrealpow,
    hsum_re.hasSum.tendsto_sum_nat.comp hn⟩








end SymNewtonCase
