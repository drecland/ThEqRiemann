import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannEndProof.RiemannEndDefinition
import ThEqRiemann.RiemannProof.XiEntiereProp

/-! -/
namespace PermutBlocConj

open Set Complex
open RiemannDef RiemannEndDef XiEntiereRiemann

lemma xiDecale_conj (z : ℂ) :
    xiDecale (starRingEnd ℂ z) = starRingEnd ℂ (xiDecale z) := by
  obtain ⟨Phi, _, _, hXi⟩ := exists_riemann_kernel
  rw [hXi (starRingEnd ℂ z), hXi z]
  rw [map_mul, map_ofNat]
  congr 1
  have h_int : (∫ u in Set.Ioi (0 : ℝ), (Phi u : ℂ) * Complex.cosh (starRingEnd ℂ z * (u : ℂ))) =
      ∫ u in Set.Ioi (0 : ℝ), starRingEnd ℂ ((Phi u : ℂ) * Complex.cosh (z * (u : ℂ))) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
    rw [map_mul, Complex.conj_ofReal, ← Complex.cosh_conj, map_mul, Complex.conj_ofReal]
  rw [h_int, ← integral_conj]

lemma xiDecale_neg (z : ℂ) : xiDecale (-z) = xiDecale z := by
  unfold xiDecale
  have h : (1 / 2 : ℂ) + -z = 1 - (1 / 2 + z) := by ring
  rw [h, xiEntiere_one_sub]

lemma XiRiemann_conj_zero (z : ℂ) (hz : XiRiemann z = 0) :
    XiRiemann (starRingEnd ℂ z) = 0 := by
  unfold XiRiemann at hz ⊢
  have h1 : Complex.I * (starRingEnd ℂ z) = - starRingEnd ℂ (Complex.I * z) := by
    rw [map_mul, Complex.conj_I]
    ring
  rw [h1, xiDecale_neg, xiDecale_conj, hz, map_zero]

lemma norm_strictMono_prefix (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ₀ m₀) (n₀ : ℕ)
    (h_real : ∀ j, 1 ≤ j → j < n₀ → (γ₀ j).im = 0) :
    ∀ j, 1 ≤ j → j < n₀ → ‖γ₀ j‖ < ‖γ₀ (j + 1)‖ := by
  intro j hj1 hjn0
  have h_le : ‖γ₀ j‖ ≤ ‖γ₀ (j + 1)‖ :=
    henum.mono_norm j (j + 1) hj1 (Nat.le_succ j)
  refine lt_of_le_of_ne h_le ?_
  intro h_eq
  have h_pal := (henum.palier_strict j hj1 h_eq.symm).1
  have h_conj : starRingEnd ℂ (γ₀ j) = γ₀ j :=
    Complex.conj_eq_iff_im.mpr (h_real j hj1 hjn0)
  rw [h_conj] at h_pal
  have h_inj := henum.injective (j + 1) j (by omega) hj1 h_pal
  omega

lemma analyse_paliers_recurrence (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ₀ m₀) (n₀ : ℕ) (hn₀ : 3 ≤ n₀)
    (h_real : ∀ j, 1 ≤ j → j < n₀ → (γ₀ j).im = 0)
    (h_non_real : ∀ n, n₀ ≤ n → (γ₀ n).im ≠ 0) :
    ∀ k : ℕ,
      ‖γ₀ (n₀ + 2 * k - 1)‖ < ‖γ₀ (n₀ + 2 * k)‖ ∧
      γ₀ (n₀ + 2 * k + 1) = starRingEnd ℂ (γ₀ (n₀ + 2 * k)) ∧
      m₀ (n₀ + 2 * k + 1) = m₀ (n₀ + 2 * k) ∧
      ‖γ₀ (n₀ + 2 * k)‖ < ‖γ₀ (n₀ + 2 * (k + 1))‖ := by
  have h_step : ∀ u : ℕ, n₀ ≤ u → ‖γ₀ (u - 1)‖ < ‖γ₀ u‖ →
      γ₀ (u + 1) = starRingEnd ℂ (γ₀ u) ∧
      m₀ (u + 1) = m₀ u ∧
      ‖γ₀ u‖ < ‖γ₀ (u + 2)‖ ∧
      ‖γ₀ (u + 1)‖ < ‖γ₀ (u + 2)‖ := by
    intro u hu h_prev
    have hu1 : 1 ≤ u := by omega
    have him : (γ₀ u).im ≠ 0 := h_non_real u hu
    have h_neq_conj : starRingEnd ℂ (γ₀ u) ≠ γ₀ u := by
      intro h_eq
      exact him (Complex.conj_eq_iff_im.mp h_eq)
    have hz_u : XiRiemann (γ₀ u) = 0 := henum.zero_mem u hu1
    have hz_conj : XiRiemann (starRingEnd ℂ (γ₀ u)) = 0 := XiRiemann_conj_zero (γ₀ u) hz_u
    obtain ⟨m, hm1, hm_eq⟩ := henum.exhaustive (starRingEnd ℂ (γ₀ u)) hz_conj
    have hm_norm : ‖γ₀ m‖ = ‖γ₀ u‖ := by
      rw [hm_eq, Complex.norm_conj]
    have hm_ge_u : u ≤ m := by
      by_contra h_lt
      push Not at h_lt
      have h_le_u1 : m ≤ u - 1 := by omega
      have h_m_le : ‖γ₀ m‖ ≤ ‖γ₀ (u - 1)‖ := henum.mono_norm m (u - 1) hm1 h_le_u1
      linarith
    have hm_ne_u : m ≠ u := by
      intro h_eq_m
      rw [h_eq_m] at hm_eq
      exact h_neq_conj hm_eq.symm
    have hm_ge_v : u + 1 ≤ m := by omega
    have h_norm_v : ‖γ₀ (u + 1)‖ = ‖γ₀ u‖ := by
      have h1 : ‖γ₀ u‖ ≤ ‖γ₀ (u + 1)‖ := henum.mono_norm u (u + 1) hu1 (Nat.le_succ u)
      have h2 : ‖γ₀ (u + 1)‖ ≤ ‖γ₀ m‖ := henum.mono_norm (u + 1) m (by omega) hm_ge_v
      linarith
    have h_pal := henum.palier_strict u hu1 h_norm_v
    have h_conj_v : γ₀ (u + 1) = starRingEnd ℂ (γ₀ u) := h_pal.1
    have h_mult_v : m₀ (u + 1) = m₀ u := henum.conj_mult u (u + 1) hu1 (by omega) h_conj_v
    have h_norm_u2_le : ‖γ₀ u‖ ≤ ‖γ₀ (u + 2)‖ := henum.mono_norm u (u + 2) hu1 (by omega)
    have h_norm_u2_lt : ‖γ₀ u‖ < ‖γ₀ (u + 2)‖ := lt_of_le_of_ne h_norm_u2_le (Ne.symm h_pal.2)
    have h_norm_v_lt : ‖γ₀ (u + 1)‖ < ‖γ₀ (u + 2)‖ := by linarith
    exact ⟨h_conj_v, h_mult_v, h_norm_u2_lt, h_norm_v_lt⟩
  intro k
  induction k with
  | zero =>
    simp only [Nat.mul_zero, add_zero]
    have h_base : ‖γ₀ (n₀ - 1)‖ < ‖γ₀ n₀‖ := by
      have h0 := norm_strictMono_prefix γ₀ m₀ henum n₀ h_real (n₀ - 1) (by omega) (by omega)
      have h_eq : n₀ - 1 + 1 = n₀ := by omega
      rwa [h_eq] at h0
    obtain ⟨h1, h2, h3, _⟩ := h_step n₀ (le_refl n₀) h_base
    exact ⟨h_base, h1, h2, h3⟩
  | succ k ih =>
    obtain ⟨h_prev_k, _, _, _⟩ := ih
    have h_prev_succ : ‖γ₀ (n₀ + 2 * (k + 1) - 1)‖ < ‖γ₀ (n₀ + 2 * (k + 1))‖ := by
      have h_prev_u := (h_step (n₀ + 2 * k) (by omega) h_prev_k).2.2.2
      have h_idx1 : n₀ + 2 * (k + 1) - 1 = n₀ + 2 * k + 1 := by omega
      have h_idx2 : n₀ + 2 * (k + 1) = n₀ + 2 * k + 2 := by omega
      rwa [h_idx1, h_idx2]
    obtain ⟨h1, h2, h3, _⟩ := h_step (n₀ + 2 * (k + 1)) (by omega) h_prev_succ
    have h_idx3 : n₀ + 2 * (k + 1) + 2 = n₀ + 2 * (k + 1 + 1) := by omega
    rw [h_idx3] at h3
    exact ⟨h_prev_succ, h1, h2, h3⟩

lemma analyse_reduction_sigma (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ₀ m₀) (n₀ : ℕ) (hn₀ : 3 ≤ n₀)
    (h_real : ∀ j, 1 ≤ j → j < n₀ → (γ₀ j).im = 0)
    (h_non_real : ∀ n, n₀ ≤ n → (γ₀ n).im ≠ 0)
    (σ : Equiv.Perm ℕ) (hσ0 : σ 0 = 0)
    (hσ_norm : ∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) :
    PermutationBlocsConjugues n₀ σ := by
  have h_pal := analyse_paliers_recurrence γ₀ m₀ henum n₀ hn₀ h_real h_non_real
  have hσ_pos : ∀ n, 1 ≤ n → 1 ≤ σ n := by
    intro n hn
    by_contra h_zero
    have h_eq0 : σ n = 0 := by omega
    rw [← hσ0] at h_eq0
    have h_n0 : n = 0 := σ.injective h_eq0
    omega
  constructor
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · exact hσ0
    · have h_norm_eq : ‖γ₀ (σ n)‖ = ‖γ₀ n‖ := hσ_norm n hn_pos
      have h_σn_pos : 1 ≤ σ n := hσ_pos n hn_pos
      by_contra h_ne
      rcases lt_or_gt_of_ne h_ne with h_lt | h_gt
      · have h1 : ‖γ₀ (σ n)‖ ≤ ‖γ₀ (n - 1)‖ := henum.mono_norm (σ n) (n - 1) h_σn_pos (by omega)
        have h2 : ‖γ₀ (n - 1)‖ < ‖γ₀ n‖ := by
          have h_step := norm_strictMono_prefix γ₀ m₀ henum n₀ h_real (n - 1) (by omega) (by omega)
          have h_idx : n - 1 + 1 = n := by omega
          rwa [h_idx] at h_step
        linarith
      · have h1 : ‖γ₀ n‖ < ‖γ₀ (n + 1)‖ := norm_strictMono_prefix γ₀ m₀ henum n₀ h_real n hn_pos hn
        have h2 : ‖γ₀ (n + 1)‖ ≤ ‖γ₀ (σ n)‖ := henum.mono_norm (n + 1) (σ n) (by omega) h_gt
        linarith
  · intro k
    set u := n₀ + 2 * k
    set v := n₀ + 2 * k + 1
    have h_fibre : ∀ m, 1 ≤ m → ‖γ₀ m‖ = ‖γ₀ u‖ → m = u ∨ m = v := by
      intro m hm h_eq
      by_contra h_not
      push Not at h_not
      rcases h_not with ⟨h_ne_u, h_ne_v⟩
      by_cases h_lt : m < u
      · have h1 : ‖γ₀ m‖ ≤ ‖γ₀ (u - 1)‖ := henum.mono_norm m (u - 1) hm (by omega)
        have h2 : ‖γ₀ (u - 1)‖ < ‖γ₀ u‖ := (h_pal k).1
        linarith
      · have h_ge : u + 2 ≤ m := by omega
        have h1 : ‖γ₀ u‖ < ‖γ₀ (n₀ + 2 * (k + 1))‖ := (h_pal k).2.2.2
        have h_idx : n₀ + 2 * (k + 1) = u + 2 := by omega
        rw [h_idx] at h1
        have h2 : ‖γ₀ (u + 2)‖ ≤ ‖γ₀ m‖ := henum.mono_norm (u + 2) m (by omega) h_ge
        linarith
    have hu_norm : ‖γ₀ (σ u)‖ = ‖γ₀ u‖ := hσ_norm u (by omega)
    have hv_norm : ‖γ₀ (σ v)‖ = ‖γ₀ u‖ := by
      rw [hσ_norm v (by omega), (h_pal k).2.1, Complex.norm_conj]
    have hu_mem : σ u = u ∨ σ u = v := h_fibre (σ u) (hσ_pos u (by omega)) hu_norm
    have hv_mem : σ v = u ∨ σ v = v := h_fibre (σ v) (hσ_pos v (by omega)) hv_norm
    have h_uv_ne : σ u ≠ σ v := σ.injective.ne (by omega)
    rcases hu_mem with h1 | h1 <;> rcases hv_mem with h2 | h2
    · exfalso; exact h_uv_ne (h1.trans h2.symm)
    · left; exact ⟨h1, h2⟩
    · right; exact ⟨h1, h2⟩
    · exfalso; exact h_uv_ne (h1.trans h2.symm)


lemma sigmaSyntheseFun_prefix (γ₀ : ℕ → ℂ) (n₀ n : ℕ) (hn : n < n₀) :
    sigmaSyntheseFun γ₀ n₀ n = n := by
  unfold sigmaSyntheseFun
  exact ite_eq_left hn

lemma sigmaSyntheseFun_even (γ₀ : ℕ → ℂ) (n₀ k : ℕ) :
    sigmaSyntheseFun γ₀ n₀ (n₀ + 2 * k) =
      if 0 < (γ₀ (n₀ + 2 * k)).im then n₀ + 2 * k else n₀ + 2 * k + 1 := by
  unfold sigmaSyntheseFun
  have h_not_lt : ¬ (n₀ + 2 * k < n₀) := by omega
  have h_div : (n₀ + 2 * k - n₀) / 2 = k := by omega
  have h_mod : (n₀ + 2 * k - n₀) % 2 = 0 := by omega
  simp only [h_not_lt, ↓reduceIte, h_div, h_mod]

lemma sigmaSyntheseFun_odd (γ₀ : ℕ → ℂ) (n₀ k : ℕ) :
    sigmaSyntheseFun γ₀ n₀ (n₀ + 2 * k + 1) =
      if 0 < (γ₀ (n₀ + 2 * k)).im then n₀ + 2 * k + 1 else n₀ + 2 * k := by
  unfold sigmaSyntheseFun
  have h_not_lt : ¬ (n₀ + 2 * k + 1 < n₀) := by omega
  have h_div : (n₀ + 2 * k + 1 - n₀) / 2 = k := by omega
  have h_mod : (n₀ + 2 * k + 1 - n₀) % 2 ≠ 0 := by omega
  simp only [h_not_lt, ↓reduceIte, h_div, h_mod]

lemma sigmaSyntheseFun_involutive (γ₀ : ℕ → ℂ) (n₀ : ℕ) :
    Function.Involutive (sigmaSyntheseFun γ₀ n₀) := by
  intro n
  by_cases hn : n < n₀
  · rw [sigmaSyntheseFun_prefix γ₀ n₀ n hn, sigmaSyntheseFun_prefix γ₀ n₀ n hn]
  · have h_decomp : n = n₀ + 2 * ((n - n₀) / 2) ∨ n = n₀ + 2 * ((n - n₀) / 2) + 1 := by omega
    set k := (n - n₀) / 2
    rcases h_decomp with h_ev | h_od
    · rw [h_ev, sigmaSyntheseFun_even]
      split_ifs with h_pos
      · rw [sigmaSyntheseFun_even, ite_eq_left h_pos]
      · rw [sigmaSyntheseFun_odd, ite_eq_right h_pos]
    · rw [h_od, sigmaSyntheseFun_odd]
      split_ifs with h_pos
      · rw [sigmaSyntheseFun_odd, ite_eq_left h_pos]
      · rw [sigmaSyntheseFun_even, ite_eq_right h_pos]

noncomputable def sigmaSynthese (γ₀ : ℕ → ℂ) (n₀ : ℕ) : Equiv.Perm ℕ :=
  (sigmaSyntheseFun_involutive γ₀ n₀).toPerm (sigmaSyntheseFun γ₀ n₀)

@[simp]
lemma sigmaSynthese_apply (γ₀ : ℕ → ℂ) (n₀ n : ℕ) :
    sigmaSynthese γ₀ n₀ n = sigmaSyntheseFun γ₀ n₀ n :=
  rfl

lemma permBlocs_palier_strict_conj (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ₀ m₀) (n₀ : ℕ) (hn₀ : 3 ≤ n₀)
    (h_real : ∀ j, 1 ≤ j → j < n₀ → (γ₀ j).im = 0)
    (h_non_real : ∀ n, n₀ ≤ n → (γ₀ n).im ≠ 0)
    (σ : Equiv.Perm ℕ) (hσ : PermutationBlocsConjugues n₀ σ)
    (n : ℕ) (hn : 1 ≤ n) (h_eq_norm : ‖γ₀ (n + 1)‖ = ‖γ₀ n‖) :
    γ₀ (σ (n + 1)) = starRingEnd ℂ (γ₀ (σ n)) := by
  have h_pal := analyse_paliers_recurrence γ₀ m₀ henum n₀ hn₀ h_real h_non_real
  have hn_ge : n₀ ≤ n := by
    by_contra h_lt
    push Not at h_lt
    have h_str := norm_strictMono_prefix γ₀ m₀ henum n₀ h_real n hn h_lt
    linarith
  have h_even : n = n₀ + 2 * ((n - n₀) / 2) := by
    have h_decomp : n = n₀ + 2 * ((n - n₀) / 2) ∨ n = n₀ + 2 * ((n - n₀) / 2) + 1 := by omega
    rcases h_decomp with h_ev | h_od
    · exact h_ev
    · exfalso
      set k := (n - n₀) / 2
      have h_n1 : n + 1 = n₀ + 2 * (k + 1) := by omega
      have h_lt2 : ‖γ₀ (n₀ + 2 * k)‖ < ‖γ₀ (n₀ + 2 * (k + 1))‖ := (h_pal k).2.2.2
      have h_eq_v : ‖γ₀ n‖ = ‖γ₀ (n₀ + 2 * k)‖ := by
        rw [h_od, (h_pal k).2.1, Complex.norm_conj]
      rw [← h_n1, ← h_eq_v, h_eq_norm] at h_lt2
      linarith
  set k := (n - n₀) / 2
  have h_n1 : n + 1 = n₀ + 2 * k + 1 := by omega
  have h_conj_k : γ₀ (n₀ + 2 * k + 1) = starRingEnd ℂ (γ₀ (n₀ + 2 * k)) := (h_pal k).2.1
  have h_lhs : γ₀ (σ (n + 1)) = γ₀ (σ (n₀ + 2 * k + 1)) := by rw [h_n1]
  have h_rhs : γ₀ (σ n) = γ₀ (σ (n₀ + 2 * k)) := by rw [h_even]
  rw [h_lhs, h_rhs]
  rcases hσ.action_paires k with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, h1, h_conj_k]
  · rw [h2, h1, h_conj_k, Complex.conj_conj]


lemma permBlocs_preserves_zeroEnumeration (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ₀ m₀) (n₀ : ℕ) (hn₀ : 3 ≤ n₀)
    (h_real : ∀ j, 1 ≤ j → j < n₀ → (γ₀ j).im = 0)
    (h_non_real : ∀ n, n₀ ≤ n → (γ₀ n).im ≠ 0)
    (σ : Equiv.Perm ℕ) (hσ : PermutationBlocsConjugues n₀ σ) :
    (∀ n : ℕ, ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
    (∀ n : ℕ, m₀ (σ n) = m₀ n) ∧
    ZeroEnumeration XiRiemann (γ₀ ∘ σ) (m₀ ∘ σ) := by
  have h_pal := analyse_paliers_recurrence γ₀ m₀ henum n₀ hn₀ h_real h_non_real
  have h_norm_mult : ∀ n : ℕ, ‖γ₀ (σ n)‖ = ‖γ₀ n‖ ∧ m₀ (σ n) = m₀ n := by
    intro n
    by_cases hn : n < n₀
    · rw [hσ.fix_prefix n hn]
      exact ⟨rfl, rfl⟩
    · have h_decomp : n = n₀ + 2 * ((n - n₀) / 2) ∨ n = n₀ + 2 * ((n - n₀) / 2) + 1 := by omega
      set k := (n - n₀) / 2
      have h_conj := (h_pal k).2.1
      have h_m := (h_pal k).2.2.1
      have h_n_eq : ‖γ₀ (n₀ + 2 * k + 1)‖ = ‖γ₀ (n₀ + 2 * k)‖ := by
        rw [h_conj, Complex.norm_conj]
      rcases h_decomp with h_ev | h_od
      · rw [h_ev]
        rcases hσ.action_paires k with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [h1]; exact ⟨rfl, rfl⟩
        · rw [h1]; exact ⟨h_n_eq, h_m⟩
      · rw [h_od]
        rcases hσ.action_paires k with ⟨_, h2⟩ | ⟨_, h2⟩
        · rw [h2]; exact ⟨rfl, rfl⟩
        · rw [h2]; exact ⟨h_n_eq.symm, h_m.symm⟩
  have h_norm : ∀ n, ‖γ₀ (σ n)‖ = ‖γ₀ n‖ := fun n => (h_norm_mult n).1
  have h_mult : ∀ n, m₀ (σ n) = m₀ n := fun n => (h_norm_mult n).2
  have hσ_pos : ∀ n, 1 ≤ n → 1 ≤ σ n := by
    intro n hn
    by_contra h0
    have h_eq0 : σ n = 0 := by omega
    have h_fix0 : σ 0 = 0 := hσ.fix_prefix 0 (by omega)
    rw [← h_fix0] at h_eq0
    have := σ.injective h_eq0
    omega
  refine ⟨h_norm, h_mult, ?_⟩
  constructor
  · intro n hn
    exact henum.zero_mem (σ n) (hσ_pos n hn)
  · intro m n hm hn h_eq
    have h_σ_eq := henum.injective (σ m) (σ n) (hσ_pos m hm) (hσ_pos n hn) h_eq
    exact σ.injective h_σ_eq
  · intro z hz
    obtain ⟨n, hn1, rfl⟩ := henum.exhaustive z hz
    refine ⟨σ.symm n, ?_, by simp [Function.comp]⟩
    by_contra h0
    have h_eq0 : σ.symm n = 0 := by omega
    have h_n0 : n = σ 0 := by rw [← h_eq0, Equiv.apply_symm_apply]
    rw [hσ.fix_prefix 0 (by omega)] at h_n0
    omega
  · intro m n hm hmn
    simp only [Function.comp_apply, h_norm]
    exact henum.mono_norm m n hm hmn
  · intro n hn h_eq_norm
    simp only [Function.comp_apply] at h_eq_norm ⊢
    rw [h_norm (n + 1), h_norm n] at h_eq_norm
    have h_orig := henum.palier_strict n hn h_eq_norm
    refine ⟨?_, ?_⟩
    · exact permBlocs_palier_strict_conj γ₀ m₀ henum n₀ hn₀ h_real h_non_real σ hσ n hn h_eq_norm
    · rw [h_norm (n + 2), h_norm n]
      exact h_orig.2
  · intro n hn
    simp only [Function.comp_apply, h_mult]
    exact henum.mult_pos n hn
  · simp only [Function.comp_apply, hσ.fix_prefix 1 (by omega)]
    exact henum.real_one
  · simp only [Function.comp_apply, hσ.fix_prefix 2 (by omega)]
    exact henum.real_two
  · intro i j hi hj h_eq
    simp only [Function.comp_apply] at h_eq ⊢
    exact henum.conj_mult (σ i) (σ j) (hσ_pos i hi) (hσ_pos j hj) h_eq




lemma permBlocs_eq_of_sign_align (γ₀ : ℕ → ℂ) (n₀ : ℕ)
    (τ σ : Equiv.Perm ℕ)
    (hτ_blocs : PermutationBlocsConjugues n₀ τ)
    (hσ_blocs : PermutationBlocsConjugues n₀ σ)
    (hτ_sign : ∀ k : ℕ, 0 < ((γ₀ ∘ τ) (n₀ + 2 * k)).im ∧ ((γ₀ ∘ τ) (n₀ + 2 * k + 1)).im < 0)
    (hσ_sign : ∀ k : ℕ, 0 < ((γ₀ ∘ σ) (n₀ + 2 * k)).im ∧ ((γ₀ ∘ σ) (n₀ + 2 * k + 1)).im < 0)
    (n : ℕ) (hn : ¬ n < n₀) :
    τ n = σ n := by
  have hn_ge : n₀ ≤ n := not_lt.mp hn
  have h_decomp : n = n₀ + 2 * ((n - n₀) / 2) ∨ n = n₀ + 2 * ((n - n₀) / 2) + 1 := by omega
  have hτ_k := hτ_sign ((n - n₀) / 2)
  have hσ_k := hσ_sign ((n - n₀) / 2)
  simp only [Function.comp_apply] at hτ_k hσ_k
  rcases hτ_blocs.action_paires ((n - n₀) / 2) with ⟨hτ1, hτ2⟩ | ⟨hτ1, hτ2⟩ <;>
  rcases hσ_blocs.action_paires ((n - n₀) / 2) with ⟨hσ1, hσ2⟩ | ⟨hσ1, hσ2⟩
  · rcases h_decomp with h_ev | h_od
    · rw [h_ev, hτ1, hσ1]
    · rw [h_od, hτ2, hσ2]
  · exfalso
    rw [hτ1] at hτ_k
    rw [hσ2] at hσ_k
    linarith [hτ_k.1, hσ_k.2]
  · exfalso
    rw [hτ2] at hτ_k
    rw [hσ1] at hσ_k
    linarith [hτ_k.2, hσ_k.1]
  · rcases h_decomp with h_ev | h_od
    · rw [h_ev, hτ1, hσ1]
    · rw [h_od, hτ2, hσ2]




theorem analyse_synthese_permutation_sigma (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ₀ m₀) (n₀ : ℕ) (hn₀ : 3 ≤ n₀)
    (h_real : ∀ j, 1 ≤ j → j < n₀ → (γ₀ j).im = 0)
    (h_non_real : ∀ n, n₀ ≤ n → (γ₀ n).im ≠ 0) :
    -- 1. analysis phase
    ((∀ k : ℕ,
        γ₀ (n₀ + 2 * k + 1) = starRingEnd ℂ (γ₀ (n₀ + 2 * k)) ∧
        m₀ (n₀ + 2 * k + 1) = m₀ (n₀ + 2 * k) ∧
        ‖γ₀ (n₀ + 2 * k)‖ < ‖γ₀ (n₀ + 2 * (k + 1))‖) ∧
      (∀ σ : Equiv.Perm ℕ, σ 0 = 0 → (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) →
        PermutationBlocsConjugues n₀ σ)) ∧
    -- 2. Synthesis phase
    (∃! σ : Equiv.Perm ℕ,
      PermutationBlocsConjugues n₀ σ ∧
      (∀ k : ℕ, 0 < ((γ₀ ∘ σ) (n₀ + 2 * k)).im ∧ ((γ₀ ∘ σ) (n₀ + 2 * k + 1)).im < 0) ∧
      (∀ n ≤ 2, σ n = n) ∧
      (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
      ZeroEnumeration XiRiemann (γ₀ ∘ σ) (m₀ ∘ σ)) := by
  have h_pal := analyse_paliers_recurrence γ₀ m₀ henum n₀ hn₀ h_real h_non_real
  constructor
  · refine ⟨fun k => ⟨(h_pal k).2.1, (h_pal k).2.2.1, (h_pal k).2.2.2⟩, ?_⟩
    intro σ hσ0 hσ_norm
    exact analyse_reduction_sigma γ₀ m₀ henum n₀ hn₀ h_real h_non_real σ hσ0 hσ_norm
  · use sigmaSynthese γ₀ n₀
    have h_blocs : PermutationBlocsConjugues n₀ (sigmaSynthese γ₀ n₀) := by
      constructor
      · intro n hn
        simp [sigmaSynthese_apply, sigmaSyntheseFun_prefix γ₀ n₀ n hn]
      · intro k
        simp only [sigmaSynthese_apply, sigmaSyntheseFun_even, sigmaSyntheseFun_odd]
        split_ifs with h_pos
        · left; exact ⟨rfl, rfl⟩
        · right; exact ⟨rfl, rfl⟩
    have h_pres := permBlocs_preserves_zeroEnumeration γ₀ m₀ henum n₀ hn₀ h_real h_non_real
      (sigmaSynthese γ₀ n₀) h_blocs
    have h_sign : ∀ k : ℕ,
        0 < ((γ₀ ∘ sigmaSynthese γ₀ n₀) (n₀ + 2 * k)).im ∧
        ((γ₀ ∘ sigmaSynthese γ₀ n₀) (n₀ + 2 * k + 1)).im < 0 := by
      intro k
      simp only [Function.comp_apply, sigmaSynthese_apply,
        sigmaSyntheseFun_even, sigmaSyntheseFun_odd]
      have h_conj_k : γ₀ (n₀ + 2 * k + 1) = starRingEnd ℂ (γ₀ (n₀ + 2 * k)) := (h_pal k).2.1
      have h_im_ne : (γ₀ (n₀ + 2 * k)).im ≠ 0 := h_non_real (n₀ + 2 * k) (by omega)
      split_ifs with h_pos
      · refine ⟨h_pos, ?_⟩
        rw [h_conj_k, Complex.conj_im]
        linarith
      · have h_neg : (γ₀ (n₀ + 2 * k)).im < 0 := lt_of_le_of_ne (not_lt.mp h_pos) h_im_ne
        rw [h_conj_k, Complex.conj_im]
        refine ⟨by linarith, h_neg⟩
    refine ⟨⟨h_blocs, h_sign, fun n hn => h_blocs.fix_prefix n (by omega),
      fun n _ => h_pres.1 n, h_pres.2.2⟩, ?_⟩
    intro τ ⟨hτ_blocs, hτ_sign, _, _, _⟩
    ext n
    by_cases hn : n < n₀
    · rw [hτ_blocs.fix_prefix n hn, h_blocs.fix_prefix n hn]
    · exact permBlocs_eq_of_sign_align γ₀ n₀ τ
        (sigmaSynthese γ₀ n₀) hτ_blocs h_blocs hτ_sign h_sign n hn


lemma selectFibre_spec_before (Xi : ℂ → ℂ)
    (h_symm : ∀ z : ℂ, Xi (starRingEnd ℂ z) = starRingEnd ℂ (Xi z))
    (h_paliers : PaliersStricts Xi)
    (D : DecompositionFibresSpectrales Xi) (j : ℕ) (hj : j < D.j₀) :
    selectFibre Xi h_symm h_paliers D j ∈ fibreModule Xi (D.r j) ∧
    (selectFibre Xi h_symm h_paliers D j).im = 0 := by
  unfold selectFibre
  rw [dite_eq_left hj]
  exact Classical.choose_spec (D.h_real_before j hj)

lemma selectFibre_spec_after (Xi : ℂ → ℂ)
    (h_symm : ∀ z : ℂ, Xi (starRingEnd ℂ z) = starRingEnd ℂ (Xi z))
    (h_paliers : PaliersStricts Xi)
    (D : DecompositionFibresSpectrales Xi) (j : ℕ) (hj : D.j₀ ≤ j) :
    selectFibre Xi h_symm h_paliers D j ∈ fibreModule Xi (D.r j) ∧
    0 < (selectFibre Xi h_symm h_paliers D j).im := by
  unfold selectFibre
  have hj_not : ¬ (j < D.j₀) := not_lt.mpr hj
  rw [dite_eq_right hj_not]
  have h_non_real : ¬ ∃ x ∈ fibreModule Xi (D.r j), x.im = 0 := by
    rintro ⟨x, hx_mem, hx_im⟩
    exact D.h_non_real_after j hj x hx_mem hx_im
  have h_pos : ∃ z_pos : ℂ, z_pos ∈ fibreModule Xi (D.r j) ∧ 0 < z_pos.im := by
    rcases dichotomie_fibreModule
      Xi h_symm h_paliers (D.r j) (D.h_mem j)
      with ⟨x, hx, _⟩ | ⟨z, hz, _⟩
    · exfalso; exact h_non_real ⟨x, hx.1, hx.2⟩
    · exact ⟨z, hz⟩
  exact Classical.choose_spec h_pos



theorem construction_enumeration_admissible_choix (Xi : ℂ → ℂ)
    (h_symm : ∀ z : ℂ, Xi (starRingEnd ℂ z) = starRingEnd ℂ (Xi z))
    (h_paliers : PaliersStricts Xi)
    (D : DecompositionFibresSpectrales Xi) :
    ∃ (n₀ : ℕ) (γ : ℕ → ℂ) (m : ℕ → ℕ),
      3 ≤ n₀ ∧
      ZeroEnumeration Xi γ m ∧
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) ∧
      (∀ k : ℕ,
        0 < (γ (n₀ + 2 * k)).im ∧
        γ (n₀ + 2 * k + 1) = starRingEnd ℂ (γ (n₀ + 2 * k)) ∧
        m (n₀ + 2 * k + 1) = m (n₀ + 2 * k)) := by
  let n₀ := D.j₀ + 1
  let γ := gammaChoix Xi h_symm h_paliers D
  let m := mChoix Xi h_symm h_paliers D
  have hn₀ : 3 ≤ n₀ := by
    have := D.hj₀
    omega
  have hγ_prefix : ∀ j, 1 ≤ j → j < n₀ → γ j = selectFibre Xi h_symm h_paliers D (j - 1) := by
    intro j hj1 hjn
    dsimp [γ, gammaChoix]
    rw [ite_eq_right (by omega), ite_eq_left hjn]
  have hγ_even : ∀ k : ℕ, γ (n₀ + 2 * k) = selectFibre Xi h_symm h_paliers D (D.j₀ + k) := by
    intro k
    dsimp [γ, gammaChoix]
    have h1 : n₀ + 2 * k ≠ 0 := by omega
    have h2 : ¬ (n₀ + 2 * k < D.j₀ + 1) := by omega
    have h3 : (n₀ + 2 * k - (D.j₀ + 1)) / 2 = k := by omega
    have h4 : (n₀ + 2 * k - (D.j₀ + 1)) % 2 = 0 := by omega
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h4, h3]
  have hγ_odd : ∀ k : ℕ, γ (n₀ + 2 * k + 1) =
      starRingEnd ℂ (selectFibre Xi h_symm h_paliers D (D.j₀ + k)) := by
    intro k
    dsimp [γ, gammaChoix]
    have h2 : ¬ (n₀ + 2 * k + 1 < D.j₀ + 1) := by omega
    have h3 : (n₀ + 2 * k + 1 - (D.j₀ + 1)) / 2 = k := by omega
    have h4 : ¬ ((n₀ + 2 * k + 1 - (D.j₀ + 1)) % 2 = 0) := by omega
    rw [ite_eq_right h2, ite_eq_right h4, h3]
  let idxFibre : ℕ → ℕ := fun n => if n < n₀ then n - 1 else D.j₀ + (n - n₀) / 2
  have h_norm_eq_r : ∀ n, 1 ≤ n → ‖γ n‖ = D.r (idxFibre n) := by
    intro n hn1
    dsimp [idxFibre]
    by_cases hn : n < n₀
    · rw [ite_eq_left hn, hγ_prefix n hn1 hn]
      exact (selectFibre_spec_before Xi h_symm h_paliers D (n - 1) (by omega)).1.2
    · rw [ite_eq_right hn]
      have h_decomp : n = n₀ + 2 * ((n - n₀) / 2) ∨ n = n₀ + 2 * ((n - n₀) / 2) + 1 := by omega
      set k := (n - n₀) / 2
      have h_spec := (selectFibre_spec_after Xi h_symm h_paliers D (D.j₀ + k) (by omega)).1.2
      rcases h_decomp with h_ev | h_od
      · nth_rw 1 [h_ev]
        rw [hγ_even k]
        exact h_spec
      · nth_rw 1 [h_od]
        rw [hγ_odd k, Complex.norm_conj]
        exact h_spec
  refine ⟨n₀, γ, m, hn₀, ?_, ?_, ?_⟩
  · constructor
    · intro n hn1
      by_cases hn : n < n₀
      · rw [hγ_prefix n hn1 hn]
        exact (selectFibre_spec_before Xi h_symm h_paliers D (n - 1) (by omega)).1.1
      · have h_decomp : n = n₀ + 2 * ((n - n₀) / 2) ∨ n = n₀ + 2 * ((n - n₀) / 2) + 1 := by omega
        let k := (n - n₀) / 2
        have h_z := (selectFibre_spec_after Xi h_symm h_paliers D (D.j₀ + k) (by omega)).1.1
        rcases h_decomp with h_ev | h_od
        · rw [h_ev, hγ_even k]; exact h_z
        · rw [h_od, hγ_odd k, h_symm, h_z, map_zero]
    · intro n₁ n₂ hn₁ hn₂ h_eq
      have h_r_eq : D.r (idxFibre n₁) = D.r (idxFibre n₂) := by
        rw [← h_norm_eq_r n₁ hn₁, ← h_norm_eq_r n₂ hn₂, h_eq]
      have h_idx_eq : idxFibre n₁ = idxFibre n₂ := D.h_strictMono.injective h_r_eq
      dsimp [idxFibre] at h_idx_eq
      by_cases h1 : n₁ < n₀ <;> by_cases h2 : n₂ < n₀
      · rw [ite_eq_left h1, ite_eq_left h2] at h_idx_eq; omega
      · rw [ite_eq_left h1, ite_eq_right h2] at h_idx_eq; omega
      · rw [ite_eq_right h1, ite_eq_left h2] at h_idx_eq; omega
      · rw [ite_eq_right h1, ite_eq_right h2] at h_idx_eq
        let k := (n₁ - n₀) / 2
        have hk_eq : (n₂ - n₀) / 2 = k := by omega
        have h_pos_k := (selectFibre_spec_after Xi h_symm h_paliers D (D.j₀ + k) (by omega)).2
        have h_d1 : n₁ = n₀ + 2 * k ∨ n₁ = n₀ + 2 * k + 1 := by omega
        have h_d2 : n₂ = n₀ + 2 * k ∨ n₂ = n₀ + 2 * k + 1 := by omega
        rcases h_d1 with hd1 | hd1 <;> rcases h_d2 with hd2 | hd2
        · rw [hd1, hd2]
        · exfalso
          rw [hd1, hd2, hγ_even k, hγ_odd k] at h_eq
          have h_im := congrArg Complex.im h_eq
          rw [Complex.conj_im] at h_im
          linarith
        · exfalso
          rw [hd1, hd2, hγ_even k, hγ_odd k] at h_eq
          have h_im := congrArg Complex.im h_eq
          rw [Complex.conj_im] at h_im
          linarith
        · rw [hd1, hd2]
    · intro z hz
      obtain ⟨j, hj_norm⟩ := D.h_exhaust z hz
      have hz_fibre : z ∈ fibreModule Xi (D.r j) := ⟨hz, hj_norm⟩
      by_cases hj : j < D.j₀
      · refine ⟨j + 1, by omega, ?_⟩
        rw [hγ_prefix (j + 1) (by omega) (by omega)]
        simp only [Nat.add_sub_cancel]
        have h_spec := selectFibre_spec_before Xi h_symm h_paliers D j hj
        by_contra h_ne
        have h_eq_conj := h_paliers _ z h_spec.1.1 hz h_ne (h_spec.1.2.trans hj_norm.symm)
        rw [Complex.conj_eq_iff_im.mpr h_spec.2] at h_eq_conj
        exact h_ne h_eq_conj.symm
      · let k := j - D.j₀
        have hj_eq : j = D.j₀ + k := by omega
        rw [hj_eq] at hz_fibre
        have h_spec := selectFibre_spec_after Xi h_symm h_paliers D (D.j₀ + k) (by omega)
        by_cases h_eq : z = selectFibre Xi h_symm h_paliers D (D.j₀ + k)
        · refine ⟨n₀ + 2 * k, by omega, ?_⟩
          rw [hγ_even k, h_eq]
        · refine ⟨n₀ + 2 * k + 1, by omega, ?_⟩
          rw [hγ_odd k]
          have h_conj := h_paliers _ z h_spec.1.1 hz (Ne.symm h_eq)
            (h_spec.1.2.trans hz_fibre.2.symm)
          exact h_conj.symm
    · intro n₁ n₂ hn₁ h_le
      rw [h_norm_eq_r n₁ hn₁, h_norm_eq_r n₂ (by omega)]
      refine D.h_strictMono.monotone ?_
      dsimp [idxFibre]
      split_ifs <;> omega
    · intro n hn1 h_norm_eq
      rw [h_norm_eq_r (n + 1) (by omega), h_norm_eq_r n hn1] at h_norm_eq
      have h_idx_eq : idxFibre (n + 1) = idxFibre n := D.h_strictMono.injective h_norm_eq
      dsimp [idxFibre] at h_idx_eq
      have hn_ge : n₀ ≤ n := by
        by_contra h_lt
        have : idxFibre (n + 1) ≠ idxFibre n := by
          dsimp [idxFibre]; split_ifs <;> omega
        exact this h_idx_eq
      have h_even : n = n₀ + 2 * ((n - n₀) / 2) := by
        split_ifs at h_idx_eq <;> omega
      let k := (n - n₀) / 2
      have hn1_eq : n + 1 = n₀ + 2 * k + 1 := by omega
      refine ⟨?_, ?_⟩
      · rw [hn1_eq, h_even, hγ_odd k, hγ_even k]
      · rw [h_norm_eq_r (n + 2) (by omega), h_norm_eq_r n hn1]
        intro h_eq2
        have h_idx2 : idxFibre (n + 2) = idxFibre n := D.h_strictMono.injective h_eq2
        dsimp [idxFibre] at h_idx2
        split_ifs at h_idx2 <;> omega
    · intro n _
      dsimp [m, mChoix, multXi]
      split_ifs <;> exact le_max_left 1 _
    · rw [hγ_prefix 1 (by omega) (by omega)]
      exact (selectFibre_spec_before Xi h_symm h_paliers D 0 (by omega)).2
    · rw [hγ_prefix 2 (by omega) (by omega)]
      exact (selectFibre_spec_before Xi h_symm h_paliers D 1 (by omega)).2
    · intro n₁ n₂ hn₁ hn₂ h_conj
      have h_norm : ‖γ n₂‖ = ‖γ n₁‖ := by rw [h_conj, Complex.norm_conj]
      rw [h_norm_eq_r n₂ hn₂, h_norm_eq_r n₁ hn₁] at h_norm
      have h_idx : idxFibre n₂ = idxFibre n₁ := D.h_strictMono.injective h_norm
      dsimp [m, mChoix]
      dsimp [idxFibre] at h_idx
      by_cases h1 : n₁ < D.j₀ + 1 <;> by_cases h2 : n₂ < D.j₀ + 1
      · rw [ite_eq_left h1, ite_eq_left h2] at h_idx ⊢
        have : n₁ = n₂ := by omega
        rw [this]
      · rw [ite_eq_left h1, ite_eq_right h2] at h_idx; omega
      · rw [ite_eq_right h1, ite_eq_left h2] at h_idx; omega
      · rw [ite_eq_right h1, ite_eq_right h2] at h_idx ⊢
        have hk : (n₂ - (D.j₀ + 1)) / 2 = (n₁ - (D.j₀ + 1)) / 2 := by omega
        rw [hk]
  · intro j hj1 hjn
    rw [hγ_prefix j hj1 hjn]
    exact (selectFibre_spec_before Xi h_symm h_paliers D (j - 1) (by omega)).2
  · intro k
    refine ⟨?_, ?_, ?_⟩
    · rw [hγ_even k]
      exact (selectFibre_spec_after Xi h_symm h_paliers D (D.j₀ + k) (by omega)).2
    · rw [hγ_odd k, hγ_even k]
    · dsimp [m, mChoix]
      have h1 : ¬ (n₀ + 2 * k + 1 < D.j₀ + 1) := by omega
      have h2 : ¬ (n₀ + 2 * k < D.j₀ + 1) := by omega
      have h3 : (n₀ + 2 * k + 1 - (D.j₀ + 1)) / 2 = k := by omega
      have h4 : (n₀ + 2 * k - (D.j₀ + 1)) / 2 = k := by omega
      rw [ite_eq_right h1, ite_eq_right h2, h3, h4]


-- Prochaine étape: montrer que (D : DecompositionFibresSpectrales Xi)
-- est une conséquence de la défintion de la fonction xi, pour venir
-- obtenir le résultat avec uniquement
-- (h_paliers : PaliersStricts Xi) en paramètres

lemma xiEntiere_symm :
    ∀ z : ℂ, xiEntiere (starRingEnd ℂ z) = starRingEnd ℂ (xiEntiere z) :=
  fun z => xiEntiere_conj z


lemma norm_mem_rayonsSpectraux_of_zero {Xi : ℂ → ℂ} {z : ℂ} (hz : Xi z = 0) :
    ‖z‖ ∈ rayonsSpectraux Xi := by
  unfold rayonsSpectraux fibreModule
  rw [Set.mem_ofPred_eq]
  exact ⟨z, hz, rfl⟩


/-!
### Partie I : Construction de la suite `r : ℕ → ℝ` par l'Axiome du Choix

**Objectif humain :**
Énoncer les deux propriétés d'existence ponctuelle sur `rayonsSpectraux xiEntiere`
auxquelles on applique l'Axiome du Choix (`Classical.choose`) :
1. Il existe un plus petit rayon spectral.
2. Pour tout réel `a`, il existe un plus petit rayon spectral strictement supérieur à `a`.

**Entrées :** `a : ℝ` pour le second lemme.
**Sorties :** Existence du minimum global et du successeur spectral local.
-/
lemma exists_min_rayonSpectral_xiEntiere :
    ∃ x₀ ∈ rayonsSpectraux xiEntiere, ∀ y ∈ rayonsSpectraux xiEntiere, x₀ ≤ y := by
  sorry

lemma exists_next_rayonSpectral_xiEntiere (a : ℝ) :
    ∃ x ∈ rayonsSpectraux xiEntiere, a < x ∧ ∀ y ∈ rayonsSpectraux xiEntiere, a < y → x ≤ y := by
  sorry

noncomputable def suiteRayonsXiEntiere : ℕ → ℝ
  | 0 => Classical.choose exists_min_rayonSpectral_xiEntiere
  | n + 1 => Classical.choose (exists_next_rayonSpectral_xiEntiere (suiteRayonsXiEntiere n))

lemma suiteRayonsXiEntiere_mem (n : ℕ) :
    suiteRayonsXiEntiere n ∈ rayonsSpectraux xiEntiere := by
  cases n with
  | zero =>
    unfold suiteRayonsXiEntiere
    exact (Classical.choose_spec exists_min_rayonSpectral_xiEntiere).1
  | succ k =>
    unfold suiteRayonsXiEntiere
    exact (Classical.choose_spec
      (exists_next_rayonSpectral_xiEntiere (suiteRayonsXiEntiere k))).1

lemma suiteRayonsXiEntiere_lt_succ (n : ℕ) :
    suiteRayonsXiEntiere n < suiteRayonsXiEntiere (n + 1) := by
  change suiteRayonsXiEntiere n <
    Classical.choose (exists_next_rayonSpectral_xiEntiere
      (suiteRayonsXiEntiere n))
  exact (Classical.choose_spec
    (exists_next_rayonSpectral_xiEntiere (suiteRayonsXiEntiere n))).2.1

lemma suiteRayonsXiEntiere_strictMono :
    StrictMono suiteRayonsXiEntiere :=
  strictMono_nat_of_lt_succ suiteRayonsXiEntiere_lt_succ

/-!
**Objectif :**
Montrer que tout rayon spectral `y ∈ rayonsSpectraux xiEntiere` est atteint par la suite
`suiteRayonsXiEntiere` à un certain rang `n`, en déduire l'égalité d'ensembles
`Set.range suiteRayonsXiEntiere = rayonsSpectraux xiEntiere`, et conclure
`exists_enumeration_rayonsSpectraux_xiEntiere`.

**Entrées :** `y : ℝ` et `hy : y ∈ rayonsSpectraux xiEntiere` pour le premier lemme.
**Sortie :** `∃ r : ℕ → ℝ, StrictMono r ∧ Set.range r = rayonsSpectraux xiEntiere`.
-/
lemma exists_index_suiteRayonsXiEntiere {y : ℝ} (hy : y ∈ rayonsSpectraux xiEntiere) :
    ∃ n : ℕ, suiteRayonsXiEntiere n = y := by
  sorry

lemma range_suiteRayonsXiEntiere_eq :
    Set.range suiteRayonsXiEntiere = rayonsSpectraux xiEntiere := by
  apply Set.Subset.antisymm
  · rintro y ⟨n, rfl⟩
    exact suiteRayonsXiEntiere_mem n
  · intro y hy
    rw [Set.mem_range]
    exact exists_index_suiteRayonsXiEntiere hy

lemma exists_enumeration_rayonsSpectraux_xiEntiere :
    ∃ r : ℕ → ℝ, StrictMono r ∧ Set.range r =
    rayonsSpectraux xiEntiere :=
  ⟨suiteRayonsXiEntiere, suiteRayonsXiEntiere_strictMono,
    range_suiteRayonsXiEntiere_eq⟩

lemma exists_zero_reel_of_not_fibreNonReelle {Xi : ℂ → ℂ} {rad : ℝ}
    (h_not : ¬ FibreNonReelle Xi rad) :
    ∃ x ∈ fibreModule Xi rad, x.im = 0 := by
  unfold FibreNonReelle at h_not
  push Not at h_not
  exact h_not


/-!
**Objectif :**
Énoncer les trois propriétés de régime spectral le long de la suite `r` :
1. Existence d'au moins une fibre purement non-réelle.
2. Les deux premières fibres (`j < 2`) ne sont pas purement non-réelles.
3. Le caractère purement non-réel persiste pour tout indice `j₂ ≥ j₁`.

**Entrées :** `r : ℕ → ℝ`, `hr_mono : StrictMono r`, `hr_range : Set.range r = rayonsSpectraux xiEntiere`.
**Sorties :** Les trois propriétés ci-dessus.
-/
lemma exists_fibreNonReelle_xiEntiere (r : ℕ → ℝ)
    (hr_mono : StrictMono r) (hr_range : Set.range r = rayonsSpectraux xiEntiere) :
    ∃ j : ℕ, FibreNonReelle xiEntiere (r j) := by
  sorry

lemma not_fibreNonReelle_of_lt_two_xiEntiere (r : ℕ → ℝ)
    (hr_mono : StrictMono r) (hr_range : Set.range r = rayonsSpectraux xiEntiere)
    {j : ℕ} (hj : j < 2) :
    ¬ FibreNonReelle xiEntiere (r j) := by
  sorry

lemma fibreNonReelle_of_ge_xiEntiere (r : ℕ → ℝ)
    (hr_mono : StrictMono r) (hr_range : Set.range r = rayonsSpectraux xiEntiere)
    {j₁ j₂ : ℕ} (h_le : j₁ ≤ j₂) (h₁ : FibreNonReelle xiEntiere (r j₁)) :
    FibreNonReelle xiEntiere (r j₂) := by
  sorry


lemma exists_seuil_fibres_xiEntiere (r : ℕ → ℝ)
    (hr_mono : StrictMono r) (hr_range : Set.range r = rayonsSpectraux xiEntiere) :
    ∃ j₀ : ℕ,
      2 ≤ j₀ ∧
      (∀ j < j₀, ∃ x ∈ fibreModule xiEntiere (r j), x.im = 0) ∧
      (∀ j ≥ j₀, ∀ z ∈ fibreModule xiEntiere (r j), z.im ≠ 0) := by
  classical
  have h_ex : ∃ j : ℕ, FibreNonReelle xiEntiere (r j) :=
    exists_fibreNonReelle_xiEntiere r hr_mono hr_range
  let j₀ : ℕ := Nat.find h_ex
  have hj₀_spec : FibreNonReelle xiEntiere (r j₀) := Nat.find_spec h_ex
  refine ⟨j₀, ?_, ?_, ?_⟩
  · rw [Nat.le_find_iff h_ex 2]
    intro k hk
    exact not_fibreNonReelle_of_lt_two_xiEntiere r hr_mono hr_range hk
  · intro j hj
    have h_not : ¬ FibreNonReelle xiEntiere (r j) := Nat.find_min h_ex hj
    exact exists_zero_reel_of_not_fibreNonReelle h_not
  · intro j hj z hz
    have h_non_real : FibreNonReelle xiEntiere (r j) :=
      fibreNonReelle_of_ge_xiEntiere r hr_mono hr_range hj hj₀_spec
    exact h_non_real z hz

lemma mem_rayonsSpectraux_of_range_eq {Xi : ℂ → ℂ} {r : ℕ → ℝ}
    (hr_range : Set.range r = rayonsSpectraux Xi) (j : ℕ) :
    r j ∈ rayonsSpectraux Xi := by
  rw [← hr_range]
  exact Set.mem_range_self j

lemma exhaust_rayonsSpectraux_of_range_eq {Xi : ℂ → ℂ} {r : ℕ → ℝ}
    (hr_range : Set.range r = rayonsSpectraux Xi) (z : ℂ) (hz : Xi z = 0) :
    ∃ j : ℕ, ‖z‖ = r j := by
  have h_mem : ‖z‖ ∈ Set.range r := by
    rw [hr_range]
    exact norm_mem_rayonsSpectraux_of_zero hz
  rcases Set.mem_range.mp h_mem with ⟨j, hj⟩
  exact ⟨j, hj.symm⟩

lemma exists_spectre_ordonne_xiEntiere :
    ∃ (r : ℕ → ℝ) (j₀ : ℕ),
      2 ≤ j₀ ∧
      StrictMono r ∧
      (∀ j : ℕ, r j ∈ rayonsSpectraux xiEntiere) ∧
      (∀ z : ℂ, xiEntiere z = 0 → ∃ j : ℕ, ‖z‖ = r j) ∧
      (∀ j < j₀, ∃ x ∈ fibreModule xiEntiere (r j), x.im = 0) ∧
      (∀ j ≥ j₀, ∀ z ∈ fibreModule xiEntiere (r j), z.im ≠ 0) := by
  rcases exists_enumeration_rayonsSpectraux_xiEntiere with ⟨r, hr_mono, hr_range⟩
  rcases exists_seuil_fibres_xiEntiere r hr_mono hr_range with
    ⟨j₀, hj₀, h_real_before, h_non_real_after⟩
  refine ⟨r, j₀, hj₀, hr_mono, ?_, ?_, h_real_before, h_non_real_after⟩
  · intro j
    exact mem_rayonsSpectraux_of_range_eq hr_range j
  · intro z hz
    exact exhaust_rayonsSpectraux_of_range_eq hr_range z hz


noncomputable def decompositionSpectraleXiEntiere :
    DecompositionFibresSpectrales xiEntiere :=
  let r_seq : ℕ → ℝ := Classical.choose exists_spectre_ordonne_xiEntiere
  let h_r := Classical.choose_spec exists_spectre_ordonne_xiEntiere
  let j₀_val : ℕ := Classical.choose h_r
  let h_spec := Classical.choose_spec h_r
  { r := r_seq
    j₀ := j₀_val
    hj₀ := h_spec.1
    h_strictMono := h_spec.2.1
    h_mem := h_spec.2.2.1
    h_exhaust := h_spec.2.2.2.1
    h_real_before := h_spec.2.2.2.2.1
    h_non_real_after := h_spec.2.2.2.2.2 }


theorem construction_enumeration_admissible_xiEntiere
    (h_paliers : PaliersStricts xiEntiere) :
    ∃ (n₀ : ℕ) (γ : ℕ → ℂ) (m : ℕ → ℕ),
      3 ≤ n₀ ∧
      ZeroEnumeration xiEntiere γ m ∧
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) ∧
      (∀ k : ℕ,
        0 < (γ (n₀ + 2 * k)).im ∧
        γ (n₀ + 2 * k + 1) = starRingEnd ℂ (γ (n₀ + 2 * k)) ∧
        m (n₀ + 2 * k + 1) = m (n₀ + 2 * k)) := by
  exact construction_enumeration_admissible_choix
    xiEntiere
    xiEntiere_symm
    h_paliers
    decompositionSpectraleXiEntiere


end PermutBlocConj
