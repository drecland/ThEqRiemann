import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.InductionRiemannZero
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.BrainrotLemma
import ThEqRiemann.RiemannProof.XiEntiereProp

/-! -/
namespace RiemannConditionnal

open Set Complex
open RiemannDef InducRiemannZero


theorem etape1_param_init
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration xiEntiere γ m) :
    (∀ n, 1 ≤ n → ((sZero γ n).re = 1 / 2 ↔ (γ n).im = 0)) ∧
    (sZero γ 1).re = 1 / 2 ∧ (sZero γ 2).re = 1 / 2 ∧
    (0 < (Delta γ m 2 1).re ∧ (Delta γ m 2 1).im = 0 ∧
      Delta γ m 2 1 = (m 1 : ℂ) + (m 2 : ℂ)) ∧
    (Delta γ m 2 2 = (m 1 : ℂ) * (m 2 : ℂ) * (γ 2 - γ 1) ^ 2 ∧
      0 < (Delta γ m 2 2).re ∧ (Delta γ m 2 2).im = 0) := by
  have h2 := (recurrence_zeros_hankel_riemann xiEntiere γ m henum).2.1
  obtain ⟨_, hD1pos, hD1im, hD1eq, hD2eq, hD2pos, hD2im, _⟩ := h2
  refine ⟨fun n _ => re_sZero_eq_half_iff γ n, ?_, ?_, ⟨hD1pos, hD1im, hD1eq⟩,
    ⟨hD2eq, hD2pos, hD2im⟩⟩
  · exact (re_sZero_eq_half_iff γ 1).2 henum.real_one
  · exact (re_sZero_eq_half_iff γ 2).2 henum.real_two

theorem etape2_rang_minimal
    (γ : ℕ → ℂ)
    (h1 : (γ 1).im = 0) (h2 : (γ 2).im = 0)
    (hΩ : (Omega γ).Nonempty) :
    ∃ n₀, 3 ≤ n₀ ∧ (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) ∧ (γ n₀).im ≠ 0 := by
  classical
  have hex : ∃ n, 1 ≤ n ∧ (γ n).im ≠ 0 := by
    obtain ⟨n, hn1, hn2⟩ := hΩ
    exact ⟨n, hn1, fun h => hn2 ((re_sZero_eq_half_iff γ n).2 h)⟩
  refine ⟨Nat.find hex, ?_, ?_, (Nat.find_spec hex).2⟩
  · by_contra hlt
    push Not at hlt
    have hspec := Nat.find_spec hex
    have hge := hspec.1
    interval_cases hv : Nat.find hex
    · exact hspec.2 h1
    · exact hspec.2 h2
  · intro j hj1 hjlt
    by_contra hne
    exact Nat.find_min hex hjlt ⟨hj1, hne⟩

theorem etape2_positivite_avant
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration xiEntiere γ m)
    (n₀ : ℕ) (hn₀ : 3 ≤ n₀)
    (hreal : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) :
    (∀ r, 1 ≤ r → r ≤ n₀ - 1 →
        0 < (Delta γ m (n₀ - 1) r).re ∧ (Delta γ m (n₀ - 1) r).im = 0) := by
  have h3 := (recurrence_zeros_hankel_riemann xiEntiere γ m henum).2.2.1
  have := h3 n₀ hn₀ (fun j hj1 hj2 => hreal j hj1 (by omega))
  exact this.1

theorem etape3_palier_critique
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration xiEntiere γ m)
    (n₀ : ℕ) (hn₀ : 3 ≤ n₀)
    (hreal : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0)
    (hnr : (γ n₀).im ≠ 0)
    (hc : ConjugueSuit γ m n₀) :
    PalierCritique γ m n₀ := by
  refine ⟨hn₀, hreal, hnr, hc.1, ?_, hc.2, ?_⟩
  · intro j hj1 _
    exact henum.mult_pos j hj1
  · intro i j hi1 hi2 hj1 hj2 hij
    exact henum.injective i j hi1 hj1 hij

open BrainrotLemma_Riemann in
theorem etape3_rupture
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration xiEntiere γ m)
    (n₀ : ℕ) (h : PalierCritique γ m n₀) :
    (Delta γ m (n₀ + 1) (n₀ + 1)).re < 0 ∧
    ¬ ∃ B : Matrix (Fin (n₀ + 1)) (Fin (n₀ + 1)) ℝ, B.PosDef ∧
        ∀ p q, (B p q : ℂ) = newton γ m (n₀ + 1) (p + q) := by
  have hb := brainrot_Lemma_xi γ m henum n₀ h
  exact ⟨hb.2.1.2.1, hb.2.1.2.2.2⟩

theorem delta_pos_si_reels
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration xiEntiere γ m)
    (N : ℕ) (hN : 1 ≤ N)
    (hreal : ∀ j, 1 ≤ j → j ≤ N → (γ j).im = 0) :
    0 < (Delta γ m N N).re ∧ (Delta γ m N N).im = 0 := by
  refine Delta_pos_of_real γ m N N hN le_rfl ?_ hreal ?_
  · intro j hj
    exact henum.mult_pos j (Finset.mem_Icc.1 hj).1
  · intro i hi j hj hij
    exact henum.injective i j
      (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hj).1 hij

theorem etape3_finitude
    (γ : ℕ → ℂ) (n₀ : ℕ)
    (hprop : PropagationDefaut γ n₀) :
    (zCritEnum γ).Finite := by
  have hsub : zCritEnum γ ⊆ (fun n => sZero γ n) ''
    (Finset.Icc 1 (n₀ - 1) : Set ℕ) := by
    rintro s ⟨n, hn1, hnre, rfl⟩
    refine ⟨n, ?_, rfl⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨hn1, ?_⟩
    by_contra hlt
    push Not at hlt
    exact hprop n (by omega) hnre
  exact Set.Finite.subset
    ((Finset.Icc 1 (n₀ - 1)).finite_toSet.image _) hsub

lemma XiRiemann_zero_of_zeta_zero (s : ℂ) (hxi : xiEntiere s = 0) :
    XiRiemann (-Complex.I * (s - 1 / 2)) = 0 := by
  rw [XiRiemann_eq]
  have : (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := by
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2))
        = 1 / 2 + (-(Complex.I * Complex.I)) * (s - 1 / 2) := by ring
      _ = 1 / 2 + (s - 1 / 2) := by rw [hI]; ring
      _ = s := by ring
  rw [this]; exact hxi

lemma gamma_real_of_re_half (s : ℂ) (hre : s.re = 1 / 2) :
    (-Complex.I * (s - 1 / 2)).im = 0 := by
  simp [Complex.mul_im, hre]

open XiEntiereRiemann in
theorem zerosCritiques_sub_zCritEnum
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ m) :
    zerosCritiques ⊆ zCritEnum γ := by
  rintro s ⟨hζ, hre⟩
  have hxi : xiEntiere s = 0 := (zeta_zero_iff_xiEntiere_zero s hre).1 hζ
  have hΞ : XiRiemann (-Complex.I * (s - 1 / 2)) = 0 :=
    XiRiemann_zero_of_zeta_zero s hxi
  have hreal : (-Complex.I * (s - 1 / 2)).im = 0 := gamma_real_of_re_half s hre
  obtain ⟨n, hn1, hγn⟩ := henum.exhaustive _ hΞ
  refine ⟨n, hn1, ?_, ?_⟩
  · rw [hγn]; exact hreal
  · unfold sZero
    rw [hγn]
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    calc s = 1 / 2 + (-(Complex.I * Complex.I)) * (s - 1 / 2) := by rw [hI]; ring
      _ = 1 / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) := by ring

open ComplexConjugate
open XiEntiereRiemann BrainrotLemma_Riemann in
lemma XiRiemann_conj : ∀ z : ℂ, XiRiemann (conj z) = conj (XiRiemann z) := by
  intro z
  simp only [XiRiemann_eq]
  have h1 : (1 : ℂ) / 2 + Complex.I * conj z
      = 1 - conj ((1 : ℂ) / 2 + Complex.I * z) := by
    apply Complex.ext <;> simp ; ring
  rw [h1, xiEntiere_one_sub]
  exact xiEntiere_conj_forall _

lemma xiEntiere_zero_of_zeta_zero_bande (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1)
    (hζ : riemannZeta s = 0) : xiEntiere s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h; rw [h] at h0; simp at h0
  have hs1 : s ≠ 1 := by
    intro h; rw [h] at h1; simp at h1
  have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  have hdef : riemannZeta s = completedRiemannZeta s / Complex.Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  have hΛ : completedRiemannZeta s = 0 := by
    rw [hdef] at hζ
    rcases div_eq_zero_iff.mp hζ with h | h
    · exact h
    · exact absurd h hΓ
  have hxi : xi s = 0 := by
    unfold xi
    rw [hΛ]; ring
  rw [← xi_eq_xiEntiere s hs0 hs1]
  exact hxi

theorem localisation_zeros_droite_critique
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ m)
    (hHardy : HardyTheorem)
    (_ : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → ConjugueSuit γ m n₀)
    (hprop : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → PropagationDefaut γ n₀) :
    ∀ s ∈ zerosNonTriviaux, s.re = 1 / 2:= by
  classical
  by_contra hcontra
  push Not at hcontra
  have hΩ : (Omega γ).Nonempty := by
    obtain ⟨s, hs, hsre⟩ := hcontra
    have hxi : xiEntiere s = 0 := by
      have hs' := hs
      unfold zerosNonTriviaux at hs'
      simp only [Set.mem_ofPred_eq] at hs'
      obtain ⟨h0, h1, hζ⟩ := hs'
      exact xiEntiere_zero_of_zeta_zero_bande s h0 h1 hζ
    have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
    have hΞ : XiRiemann (-Complex.I * (s - 1 / 2)) = 0 := by
      rw [XiRiemann_eq]
      have : (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := by
        linear_combination (-(s - 1 / 2)) * hI
      rw [this]; exact hxi
    obtain ⟨n, hn1, hγn⟩ := henum.exhaustive _ hΞ
    refine ⟨n, hn1, ?_⟩
    intro him
    apply hsre
    have hs_eq : s = sZero γ n := by
      unfold sZero
      rw [hγn]
      linear_combination (s - 1 / 2) * hI
    rw [hs_eq]
    exact him
  obtain ⟨n₀, hn₀, hreal, hnr⟩ :=
    etape2_rang_minimal γ henum.real_one henum.real_two hΩ
  have hfin : (zCritEnum γ).Finite := etape3_finitude γ n₀ (hprop n₀ hn₀ hnr hreal)
  have hsub : zerosCritiques ⊆ zCritEnum γ := zerosCritiques_sub_zCritEnum γ m henum
  exact hHardy (hfin.subset hsub)


theorem rh_of_zerosNonTriviaux
    (h : ∀ s ∈ zerosNonTriviaux, s.re = 1 / 2)
    (hband : ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) →
      s ≠ 1 → 0 < s.re ∧ s.re < 1) :
    RiemannHypothesis := by
  intro s hs htriv hne1
  apply h s
  obtain ⟨h0, h1⟩ := hband s hs htriv hne1
  exact ⟨h0, h1, hs⟩

lemma chi_eq_zero_of_zero
    (s : ℂ) (hs : riemannZeta s = 0) (hnz : riemannZeta (1 - s) ≠ 0)
    (hfe : riemannZeta (1 - (1 - s)) =
      2 * (2 * ↑Real.pi) ^ (-(1 - s)) * Gamma (1 - s) *
        cos (↑Real.pi * (1 - s) / 2) * riemannZeta (1 - s)) :
    2 * (2 * ↑Real.pi) ^ (-(1 - s)) * Gamma (1 - s) *
      cos (↑Real.pi * (1 - s) / 2) = 0 := by
  rw [sub_sub_cancel, hs] at hfe
  have h := hfe.symm
  exact (mul_eq_zero.mp h).resolve_right hnz

lemma trivial_of_cos_eq_zero
    (s : ℂ) (hle : s.re ≤ 0) (hne0 : s ≠ 0)
    (hcos : cos (↑Real.pi * (1 - s) / 2) = 0) :
    ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
  rw [Complex.cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hpi : (↑Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : 1 - s = 2 * (k : ℂ) + 1 := by
    have h2 : (↑Real.pi : ℂ) * (1 - s - (2 * (k : ℂ) + 1)) = 0 := by
      linear_combination 2 * hk
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hpi
    · linear_combination h
  have hs : s = -2 * (k : ℂ) := by
    linear_combination -h1
  have hk0 : (0 : ℤ) ≤ k := by
    have hre : s.re = -2 * (k : ℝ) := by
      rw [hs]; simp
    have : (0 : ℝ) ≤ k := by linarith
    exact_mod_cast this
  rcases Nat.eq_zero_or_pos k.toNat with h | h
  · exfalso; apply hne0
    have : k = 0 := by omega
    rw [hs, this]; simp
  · refine ⟨k.toNat - 1, ?_⟩
    have hk' : (k : ℂ) = ((k.toNat - 1 : ℕ) : ℂ) + 1 := by
      have : (k : ℤ) = ((k.toNat - 1 : ℕ) : ℤ) + 1 := by omega
      exact_mod_cast this
    rw [hs, hk']

lemma Gamma_ne_zero_of_not_pole
    (u : ℂ) (hu : ∀ n : ℕ, u ≠ -(n : ℂ)) :
    Gamma u ≠ 0 :=
  Complex.Gamma_ne_zero hu

theorem zeros_in_critical_strip
    (s : ℂ) (hs : riemannZeta s = 0) (htriv : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (_ : s ≠ 1) : 0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hle
    push Not at hle
    have hne0 : s ≠ 0 := by
      intro h0
      rw [h0, riemannZeta_zero] at hs
      norm_num at hs
    have hpole : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
      intro n hn
      have : s.re = 1 + n := by
        have := congrArg Complex.re hn
        simp at this
        linarith
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hfe := riemannZeta_one_sub (s := 1 - s) hpole
      (by intro h; apply hne0; linear_combination -h)
    have hnz : riemannZeta (1 - s) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      simp
      linarith
    have hchi := chi_eq_zero_of_zero s hs hnz hfe
    have hcos : cos (↑Real.pi * (1 - s) / 2) = 0 := by
      rcases mul_eq_zero.mp hchi with h | h
      · exfalso
        rcases mul_eq_zero.mp h with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · norm_num at h''
          · exfalso
            have hpos : (2 * ↑Real.pi : ℂ) ≠ 0 :=
              mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
            rw [Complex.cpow_def_of_ne_zero hpos] at h''
            exact Complex.exp_ne_zero _ h''
        · exact absurd h' (Gamma_ne_zero_of_not_pole (1 - s) hpole)
      · exact h
    exact htriv (trivial_of_cos_eq_zero s hle hne0 hcos)
  · by_contra hge
    push Not at hge
    exact riemannZeta_ne_zero_of_one_le_re hge hs


theorem hypothesys_of_Riemann_conditional
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ m)
    (hHardy : HardyTheorem)
    (hconj : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → ConjugueSuit γ m n₀)
    (hprop : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → PropagationDefaut γ n₀) :
    RiemannHypothesis :=
  rh_of_zerosNonTriviaux
    (localisation_zeros_droite_critique γ m henum hHardy hconj hprop)
    (fun s hs htriv hne1 => zeros_in_critical_strip s hs htriv hne1)


end RiemannConditionnal
