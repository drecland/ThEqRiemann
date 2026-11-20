import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition


/-! -/
namespace PosHankelFinExhaustion

open Set Complex ComplexConjugate
open RiemannDef

lemma momentFusion_conj (E : Finset ℂ) (m : ℂ → ℕ)
    (hE : ConjStable E) (hm : MultSymm m) (k : ℕ) :
    conj (momentFusion E m k) = momentFusion E m k := by
  unfold momentFusion
  rw [map_sum]
  refine Finset.sum_bij (fun γ _ => conj γ) ?_ ?_ ?_ ?_
  · intro γ hγ
    exact hE γ hγ
  · intro a _ b _ hab
    exact (starRingEnd ℂ).injective hab
  · intro b hb
    exact ⟨conj b, hE b hb, by simp⟩
  · intro γ hγ
    simp [map_mul, map_pow, map_natCast, hm γ]

lemma moment_real (E : Finset ℂ) (m : ℂ → ℕ)
    (hE : ConjStable E) (hm : MultSymm m) (k : ℕ) :
    (momentFusion E m k).im = 0 := by
  have h := momentFusion_conj E m hE hm k
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

lemma trace_Tdiag_pow (E : Finset ℂ) (m : ℂ → ℕ) (k : ℕ) :
    Matrix.trace ((Tdiag E m) ^ k) = momentFusion E m k := by
  unfold Tdiag momentFusion
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Pi.pow_apply]
  exact Finset.sum_coe_sort E fun γ => (m γ : ℂ) * γ ^ k

lemma Nil_apply (E : Finset ℂ) (m : ℂ → ℕ) (p q : Idx E m) :
    Nil E m p q =
      if p.1 = q.1 ∧ (q.2 : ℕ) = (p.2 : ℕ) + 1 then 1 else 0 := by
  unfold Nil Tjordan Tdiag
  by_cases hc : p.1 = q.1 ∧ (q.2 : ℕ) = (p.2 : ℕ) + 1
  · have hpq : p ≠ q := by
      intro h
      subst h
      omega
    simp [Matrix.sub_apply, Matrix.of_apply, hpq, hc]
  · by_cases hpq : p = q
    · subst hpq
      simp
    · simp [Matrix.sub_apply, Matrix.of_apply, hpq, hc]

lemma Nil_pow_support (E : Finset ℂ) (m : ℂ → ℕ) (b : ℕ) (p q : Idx E m)
    (h : (Nil E m ^ b) p q ≠ 0) :
    p.1 = q.1 ∧ (q.2 : ℕ) = (p.2 : ℕ) + b := by
  induction b generalizing q with
  | zero =>
    rw [pow_zero, Matrix.one_apply] at h
    by_cases hpq : p = q
    · subst hpq; exact ⟨rfl, by simp⟩
    · simp [hpq] at h
  | succ b ih =>
    rw [pow_succ, Matrix.mul_apply] at h
    obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have h1 : (Nil E m ^ b) p r ≠ 0 := left_ne_zero_of_mul hr
    have h2 : Nil E m r q ≠ 0 := right_ne_zero_of_mul hr
    obtain ⟨hr1, hr2⟩ := ih r h1
    rw [Nil_apply] at h2
    by_cases hc : r.1 = q.1 ∧ (q.2 : ℕ) = (r.2 : ℕ) + 1
    · exact ⟨hr1.trans hc.1, by omega⟩
    · simp [hc] at h2

lemma Nil_pow_diag (E : Finset ℂ) (m : ℂ → ℕ) {b : ℕ} (hb : 1 ≤ b) (p : Idx E m) :
    (Nil E m ^ b) p p = 0 := by
  by_contra h
  have := (Nil_pow_support E m b p p h).2
  omega

lemma Tdiag_commute_Nil (E : Finset ℂ) (m : ℂ → ℕ) :
    Commute (Tdiag E m) (Nil E m) := by
  ext p q
  rw [Matrix.mul_apply, Matrix.mul_apply]
  unfold Tdiag
  simp only [Matrix.diagonal_apply, ite_mul, zero_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Nil_apply]
  by_cases hc : p.1 = q.1 ∧ (q.2 : ℕ) = (p.2 : ℕ) + 1
  · simp [hc]
  · simp [hc]

lemma trace_Tdiag_pow_mul_Nil_pow (E : Finset ℂ) (m : ℂ → ℕ) (a : ℕ) {b : ℕ}
    (hb : 1 ≤ b) :
    Matrix.trace (Tdiag E m ^ a * Nil E m ^ b) = 0 := by
  unfold Tdiag
  rw [Matrix.diagonal_pow, Matrix.trace]
  apply Finset.sum_eq_zero
  intro p _
  rw [Matrix.diag_apply, Matrix.diagonal_mul, Nil_pow_diag E m hb p, mul_zero]

lemma trace_Tjordan_pow (E : Finset ℂ) (m : ℂ → ℕ) (k : ℕ) :
    Matrix.trace ((Tjordan E m) ^ k) = momentFusion E m k := by
  have hsplit : Tjordan E m = Tdiag E m + Nil E m := by
    unfold Nil; abel
  rw [← trace_Tdiag_pow E m k, hsplit, (Tdiag_commute_Nil E m).add_pow, Matrix.trace_sum]
  rw [Finset.sum_eq_single k ?_ ?_]
  · simp [Nat.choose_self]
  · intro b hb hbk
    have hb1 : 1 ≤ k - b := by
      have := Finset.mem_range.1 hb; omega
    have h0 := trace_Tdiag_pow_mul_Nil_pow E m b hb1
    rw [← nsmul_eq_mul', Matrix.trace_smul, h0, smul_zero]
  · intro h; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self k)) h


open Polynomial

lemma charpoly_Tdiag (E : Finset ℂ) (m : ℂ → ℕ) :
    (Tdiag E m).charpoly = ∏ γ ∈ E, (X - C γ) ^ (m γ) := by
  unfold Tdiag
  rw [Matrix.charpoly_diagonal]
  -- 1) regrouper le produit sur le type sigma par la première composante
  rw [Fintype.prod_sigma]
  -- 2) chaque fibre est constante : ∏ _ : Fin (m γ), c = c ^ m γ
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- 3) produit sur le sous-type `E` → produit sur le Finset `E`
  exact Finset.prod_coe_sort E (fun γ => (X - C γ) ^ (m γ))

lemma hankelFusion_symm (E : Finset ℂ) (m : ℂ → ℕ) (D : ℕ) :
    (hankelFusion' E m D).transpose = hankelFusion' E m D := by
  ext i j
  simp [hankelFusion', Matrix.transpose_apply, add_comm]

lemma hankelFusion_real (E : Finset ℂ) (m : ℂ → ℕ) (hE : ConjStable E) (hm : MultSymm m) (D : ℕ) :
    (hankelFusion' E m D).map conj = hankelFusion' E m D := by
  ext i j
  simp only [Matrix.map_apply, hankelFusion', Matrix.of_apply]
  exact momentFusion_conj E m hE hm _

lemma quad_form_Fusion (E : Finset ℂ) (m : ℂ → ℕ) {D : ℕ} (c : Fin D → ℂ) :
    star c ⬝ᵥ (hankelFusion' E m D).mulVec c =
      ∑ γ ∈ E, (m γ : ℂ) * (polyTilde c).eval γ * (polyOf c).eval γ := by
  have hL : star c ⬝ᵥ (hankelFusion' E m D).mulVec c =
      ∑ k : Fin D, ∑ j : Fin D, ∑ γ ∈ E,
        (m γ : ℂ) * conj (c k) * c j * γ ^ ((k : ℕ) + (j : ℕ)) := by
    simp only [dotProduct, Matrix.mulVec, hankelFusion', Matrix.of_apply,
      momentFusion, Pi.star_apply, Complex.star_def]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    ring
  have hR : ∑ γ ∈ E, (m γ : ℂ) * (polyTilde c).eval γ * (polyOf c).eval γ =
      ∑ γ ∈ E, ∑ k : Fin D, ∑ j : Fin D,
        (m γ : ℂ) * conj (c k) * c j * γ ^ ((k : ℕ) + (j : ℕ)) := by
    refine Finset.sum_congr rfl fun γ _ => ?_
    simp only [polyTilde, polyOf, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    calc (m γ : ℂ) * (∑ k : Fin D, conj (c k) * γ ^ (k : ℕ)) *
            (∑ j : Fin D, c j * γ ^ (j : ℕ))
        = (m γ : ℂ) * ((∑ k : Fin D, conj (c k) * γ ^ (k : ℕ)) *
            (∑ j : Fin D, c j * γ ^ (j : ℕ))) := by ring
      _ = (m γ : ℂ) * ∑ k : Fin D, ∑ j : Fin D,
            (conj (c k) * γ ^ (k : ℕ)) * (c j * γ ^ (j : ℕ)) := by
          rw [Finset.sum_mul_sum]
      _ = ∑ k : Fin D, ∑ j : Fin D,
            (m γ : ℂ) * conj (c k) * c j * γ ^ ((k : ℕ) + (j : ℕ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [pow_add]; ring
  rw [hL, hR]
  calc ∑ k : Fin D, ∑ j : Fin D, ∑ γ ∈ E,
          (m γ : ℂ) * conj (c k) * c j * γ ^ ((k : ℕ) + (j : ℕ))
      = ∑ k : Fin D, ∑ γ ∈ E, ∑ j : Fin D,
          (m γ : ℂ) * conj (c k) * c j * γ ^ ((k : ℕ) + (j : ℕ)) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ γ ∈ E, ∑ k : Fin D, ∑ j : Fin D,
          (m γ : ℂ) * conj (c k) * c j * γ ^ ((k : ℕ) + (j : ℕ)) :=
        Finset.sum_comm

lemma polyTilde_eval_real {D : ℕ} (c : Fin D → ℂ) (γ : ℂ) (hγ : γ.im = 0) :
    (polyTilde c).eval γ = conj ((polyOf c).eval γ) := by
  have hγ' : conj γ = γ := Complex.conj_eq_iff_im.mpr hγ
  simp only [polyTilde, polyOf, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, map_sum, map_mul, map_pow, hγ']

lemma exists_nonroot (E : Finset ℂ) {D : ℕ} (hD : E.card = D)
    (P : ℂ[X]) (hP : P ≠ 0) (hdeg : P.degree < D) :
    ∃ γ ∈ E, P.eval γ ≠ 0 := by
  by_contra h
  push Not at h
  have hsub : E ⊆ P.roots.toFinset := by
    intro γ hγ
    simp [Multiset.mem_toFinset, Polynomial.mem_roots hP, h γ hγ]
  have h1 : E.card ≤ P.roots.toFinset.card := Finset.card_le_card hsub
  have h2 : P.roots.toFinset.card ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
  have h3 : Multiset.card P.roots ≤ P.natDegree := Polynomial.card_roots' P
  have h4 : P.natDegree < D := by
    have := Polynomial.natDegree_lt_iff_degree_lt hP |>.mpr hdeg
    exact this
  omega

lemma polyOf_coeff {D : ℕ} (c : Fin D → ℂ) (j : Fin D) :
    (polyOf c).coeff (j : ℕ) = c j := by
  unfold polyOf
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have : (j : ℕ) ≠ (i : ℕ) := fun h => hij (Fin.ext h).symm
    simp [this]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma polyOf_ne_zero {D : ℕ} (c : Fin D → ℂ) (hc : c ≠ 0) : polyOf c ≠ 0 := by
  intro h
  apply hc
  funext j
  have := polyOf_coeff c j
  rw [h, Polynomial.coeff_zero] at this
  simpa using this.symm

lemma polyOf_degree_lt {D : ℕ} (c : Fin D → ℂ) : (polyOf c).degree < D := by
  unfold polyOf
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (WithBot.bot_lt_coe D)).2 ?_
  intro j _
  refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le (j : ℕ) (c j)) ?_
  have hj : (j : ℕ) < D := j.isLt
  exact WithBot.coe_lt_coe.2 hj

lemma polyOf_eval {D : ℕ} (c : Fin D → ℂ) (γ : ℂ) :
    (polyOf c).eval γ = ∑ j : Fin D, c j * γ ^ (j : ℕ) := by
  unfold polyOf
  rw [Polynomial.eval_finsetSum]
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

lemma polyTilde_eval {D : ℕ} (c : Fin D → ℂ) (γ : ℂ) :
    (polyTilde c).eval γ = ∑ k : Fin D, conj (c k) * γ ^ (k : ℕ) := by
  unfold polyTilde
  rw [Polynomial.eval_finsetSum]
  simp [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]

lemma quad_form (E : Finset ℂ) (m : ℂ → ℕ) {D : ℕ} (c : Fin D → ℂ) :
    star c ⬝ᵥ (hankelFusion' E m D).mulVec c
      = ∑ γ ∈ E, (m γ : ℂ) * (polyTilde c).eval γ * (polyOf c).eval γ := by
  simp only [polyTilde_eval, polyOf_eval]
  simp only [dotProduct, Matrix.mulVec, hankelFusion', momentFusion, Matrix.of_apply]
  simp only [Finset.mul_sum, Finset.sum_mul]
  have h1 : ∀ x : Fin D,
      ∑ x_1 : Fin D, ∑ i ∈ E, star c x * (↑(m i) * i ^ ((x : ℕ) + (x_1 : ℕ)) * c x_1)
        = ∑ i ∈ E, ∑ x_1 : Fin D, star c x * (↑(m i) * i ^ ((x : ℕ) + (x_1 : ℕ)) * c x_1) :=
    fun x => Finset.sum_comm
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Pi.star_apply, Complex.star_def]
  rw [pow_add]
  ring

theorem posDef_of_real (E : Finset ℂ) (m : ℂ → ℕ) {D : ℕ} (hD : E.card = D)
    (hreal : ∀ γ ∈ E, γ.im = 0) (hm_pos : ∀ γ ∈ E, 1 ≤ m γ) :
    HankelFusionPosDef E m D := by
  intro c hc
  rw [quad_form]
  have hterm : ∀ γ ∈ E, (m γ : ℂ) * (polyTilde c).eval γ * (polyOf c).eval γ
      = ((m γ : ℝ) * (Complex.normSq ((polyOf c).eval γ)) : ℝ) := by
    intro γ hγ
    rw [polyTilde_eval_real c γ (hreal γ hγ), mul_assoc, ← Complex.normSq_eq_conj_mul_self]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm, Complex.re_sum]
  simp only [Complex.ofReal_re]
  obtain ⟨γs, hγs, hne⟩ := exists_nonroot E hD (polyOf c) (polyOf_ne_zero c hc) (polyOf_degree_lt c)
  apply Finset.sum_pos'
  · intro γ hγ
    have : (1 : ℝ) ≤ m γ := by exact_mod_cast hm_pos γ hγ
    exact mul_nonneg (by linarith) (Complex.normSq_nonneg _)
  · refine ⟨γs, hγs, ?_⟩
    have h1 : (1 : ℝ) ≤ m γs := by exact_mod_cast hm_pos γs hγs
    exact mul_pos (by linarith) (Complex.normSq_pos.mpr hne)

lemma not_posDef_of_nonreal (E : Finset ℂ) (m : ℂ → ℕ) {D : ℕ} (hD : E.card = D)
    (hE : ConjStable E) (hm : MultSymm m) (γ : ℂ) (hγ : γ ∈ E) (hne : ¬ γ.im = 0)
    (hpos : HankelFusionPosDef E m D) : False := by
  have hne' : (starRingEnd ℂ) γ ≠ γ := by
    intro h
    apply hne
    have := congrArg Complex.im h
    simp at this
    linarith
  have hγbar : (starRingEnd ℂ) γ ∈ E := hE γ hγ
  let v : ℂ → ℂ := fun x => if x = γ then 1 else if x = (starRingEnd ℂ) γ then -1 else 0
  obtain ⟨P, hPdeg, hPval⟩ : ∃ P : Polynomial ℂ, P.degree < D ∧ ∀ x ∈ E, P.eval x = v x := by
    refine ⟨Lagrange.interpolate E id v, ?_, ?_⟩
    · rw [← hD]
      exact Lagrange.degree_interpolate_lt v Function.injective_id.injOn
    · intro x hx
      exact Lagrange.eval_interpolate_at_node v Function.injective_id.injOn hx
  set c : Fin D → ℂ := fun j => P.coeff j with hc
  have hP : polyOf c = P := by
    have hnat : P.natDegree < D := by
      have hDpos : 0 < D := by
        rw [← hD]; exact Finset.card_pos.mpr ⟨γ, hγ⟩
      by_cases hP0 : P = 0
      · simp [hP0, hDpos]
      · exact (Polynomial.natDegree_lt_iff_degree_lt hP0).mpr hPdeg
    conv_rhs => rw [Polynomial.as_sum_range' P D hnat]
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [c, Polynomial.C_mul_X_pow_eq_monomial]
  have hc0 : c ≠ 0 := by
    intro h0
    have : polyOf c = 0 := by simp [polyOf, h0]
    rw [hP] at this
    have h1 : P.eval γ = 1 := by rw [hPval γ hγ]; simp [v]
    rw [this] at h1
    simp at h1
  have htilde : ∀ x : ℂ, (polyTilde c).eval x =
      (starRingEnd ℂ) ((polyOf c).eval ((starRingEnd ℂ) x)) := by
    intro x
    simp only [polyTilde, polyOf, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, map_sum, map_mul,
      map_pow, Complex.conj_conj]
  have hq := quad_form E m c
  have hv1 : P.eval γ = 1 := by rw [hPval γ hγ]; simp [v]
  have hv2 : P.eval ((starRingEnd ℂ) γ) = -1 := by
    rw [hPval _ hγbar]; simp [v, hne']
  have ht1 : (polyTilde c).eval γ = -1 := by
    rw [htilde, hP, hv2]; simp
  have ht2 : (polyTilde c).eval ((starRingEnd ℂ) γ) = 1 := by
    rw [htilde, Complex.conj_conj, hP, hv1]; simp
  have hsum : ∑ x ∈ E, (m x : ℂ) * (polyTilde c).eval x * (polyOf c).eval x
      = -(m γ : ℂ) - (m ((starRingEnd ℂ) γ) : ℂ) := by
    rw [Finset.sum_eq_add_of_mem γ ((starRingEnd ℂ) γ) hγ hγbar hne'.symm]
    · rw [hP, ht1, ht2, hv1, hv2]; ring
    · intro x hx hx'
      have hx1 : x ≠ γ := fun h => hx'.1 h
      have hx2 : x ≠ (starRingEnd ℂ) γ := fun h => hx'.2 h
      rw [hP, hPval x hx]
      simp [v, hx1, hx2]
  have hpos' := hpos c hc0
  rw [hq, hsum, hm γ] at hpos'
  simp at hpos'
  have : (0 : ℝ) ≤ (m γ : ℝ) := Nat.cast_nonneg _
  linarith

theorem hankelFusion_posDef_iff_real (E : Finset ℂ) (m : ℂ → ℕ) {D : ℕ} (hD : E.card = D)
    (hE : ConjStable E) (hm : MultSymm m) (hm_pos : ∀ γ ∈ E, 1 ≤ m γ) :
    HankelFusionPosDef E m D ↔ ∀ γ ∈ E, γ.im = 0 := by
  constructor
  · intro hpos γ hγ
    by_contra hne
    exact not_posDef_of_nonreal E m hD hE hm γ hγ hne hpos
  · intro hreal
    exact posDef_of_real E m hD hreal hm_pos

lemma card_Idx (E : Finset ℂ) (m : ℂ → ℕ) :
    Fintype.card (Idx E m) = ∑ γ ∈ E, m γ := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Finset.sum_coe_sort E m

lemma Tdiag_isDiag (E : Finset ℂ) (m : ℂ → ℕ) : (Tdiag E m).IsDiag :=
  Matrix.isDiag_diagonal _

lemma jordan_not_diag (E : Finset ℂ) (m : ℂ → ℕ) (γ : E) (h2 : 2 ≤ m γ) :
    ¬ (Tjordan E m).IsDiag := by
  intro hdiag
  have h0 : 0 < m γ := by omega
  have h1 : 1 < m γ := by omega
  have hne : (⟨γ, ⟨0, h0⟩⟩ : Idx E m) ≠ ⟨γ, ⟨1, h1⟩⟩ := by
    intro h
    simp only [Sigma.mk.inj_iff, Fin.mk.inj_iff, heq_eq_eq, true_and] at h
    exact absurd h (by decide)
  have hval : Tjordan E m ⟨γ, ⟨0, h0⟩⟩ ⟨γ, ⟨1, h1⟩⟩ = 1 := by
    simp [Tjordan]
  have h0' : Tjordan E m ⟨γ, ⟨0, h0⟩⟩ ⟨γ, ⟨1, h1⟩⟩ = 0 := by
    apply hdiag
    exact hne
  rw [hval] at h0'
  exact one_ne_zero h0'

theorem hankel_spectral_fusion (E : Finset ℂ) (m : ℂ → ℕ) {D : ℕ} (hD : E.card = D)
    (hE : ConjStable E) (hm : MultSymm m) (hm_pos : ∀ γ ∈ E, 1 ≤ m γ) :
    -- 1. real moment
    (∀ k, (momentFusion E m k).im = 0) ∧
    -- 2. construction and traces
    ((Tdiag E m).charpoly = ∏ γ ∈ E, (X - C γ) ^ (m γ) ∧
      ∀ k, Matrix.trace ((Tdiag E m) ^ k) = momentFusion E m k) ∧
    -- 3. symétric, reality, quad form
    ((hankelFusion' E m D).transpose = hankelFusion' E m D ∧
      (hankelFusion' E m D).map conj = hankelFusion' E m D ∧
      ∀ c : Fin D → ℂ, star c ⬝ᵥ (hankelFusion' E m D).mulVec c =
        ∑ γ ∈ E, (m γ : ℂ) * (polyTilde c).eval γ * (polyOf c).eval γ) ∧
    -- 4. criterium
    (HankelFusionPosDef E m D ↔ ∀ γ ∈ E, γ.im = 0) ∧
    -- 5. dimention and diagonality
    (Fintype.card (Idx E m) = ∑ γ ∈ E, m γ ∧ (Tdiag E m).IsDiag) := by
  refine ⟨moment_real E m hE hm, ⟨charpoly_Tdiag E m, trace_Tdiag_pow E m⟩,
    ⟨hankelFusion_symm E m D, hankelFusion_real E m hE hm D, fun c => quad_form E m c⟩,
    hankelFusion_posDef_iff_real E m hD hE hm hm_pos,
    ⟨card_Idx E m, Tdiag_isDiag E m⟩⟩





end PosHankelFinExhaustion
