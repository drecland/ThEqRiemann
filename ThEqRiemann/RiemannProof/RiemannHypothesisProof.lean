import mathlib
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.RiemannProofConditionnal
import ThEqRiemann.RiemannProof.XiEntiereProp
import ThEqRiemann.RiemannProof.Lambda0Prop
import ThEqRiemann.RiemannProof.BrainrotLemma
import ThEqRiemann.RiemannProof.InductionRiemannZero
import ThEqRiemann.ComplementRiemann.DeuxZeroMin
import ThEqRiemann.RiemannProof.hPosProof
import ThEqRiemann.RiemannProof.EndOfRiemannProof
import ThEqRiemann.RiemannProof.RiemannObtentionHypothesis
/-! -/
namespace RiemannHypProof

open Set Complex
open RiemannDef RiemannConditionnal XiEntiereRiemann


lemma XiRiemann_zero_iff_mem (z : ℂ) :
  XiRiemann z = 0 ↔ z ∈ LambdaZeros := Iff.rfl

lemma lambdaZeros_infinite (hHardy : HardyTheorem) : LambdaZeros.Infinite := by
  have h1 : zerosCritiques.Infinite := hHardy
  have hmaps : Set.MapsTo (fun s : ℂ => -Complex.I * (s - 1 / 2)) zerosCritiques LambdaZeros := by
    intro s hs
    obtain ⟨hζ, hre⟩ := hs
    have hxi : xiEntiere s = 0 := (zeta_zero_iff_xiEntiere_zero s hre).mp hζ
    have hX : XiRiemann (-Complex.I * (s - 1 / 2)) = 0 := XiRiemann_zero_of_zeta_zero s hxi
    exact hX
  have hinj : Set.InjOn (fun s : ℂ => -Complex.I * (s - 1 / 2)) zerosCritiques := by
    intro a _ b _ hab
    have hI : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    have h2 : a - 1 / 2 = b - 1 / 2 := mul_left_cancel₀ hI hab
    linear_combination h2
  have himg : ((fun s : ℂ => -Complex.I * (s - 1 / 2)) '' zerosCritiques).Infinite :=
    h1.image hinj
  exact himg.mono hmaps.image_subset

lemma XiRiemann_neg (z : ℂ) : XiRiemann (-z) = XiRiemann z := by
  unfold XiRiemann xiDecale
  have h : (1 / 2 : ℂ) + Complex.I * (-z) = 1 - (1 / 2 + Complex.I * z) := by ring
  rw [h]
  exact xiEntiere_one_sub _

lemma mem_LambdaZeros_iff (z : ℂ) : z ∈ LambdaZeros ↔ XiRiemann z = 0 := by
  simp only [LambdaZeros, Set.mem_ofPred_eq, XiRiemann, xiDecale]

open LambdaRiemann in
lemma lambdaZeros_countable : LambdaZeros.Countable := by
  have h : LambdaZeros = ⋃ N : ℕ, (LambdaZeros ∩ Metric.closedBall (0 : ℂ) (N : ℝ)) := by
    ext γ
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hγ
      obtain ⟨N, hN⟩ := exists_nat_ge ‖γ‖
      exact ⟨N, hγ, hN⟩
    · rintro ⟨N, hγ, _⟩
      exact hγ
  rw [h]
  exact Set.countable_iUnion (fun N => (lambdaZeros_finite_ball (N : ℝ)).countable)

lemma cle_injective : Function.Injective cle := by
  intro z w h
  unfold cle at h
  have h' := toLex.injective h
  simp only [Prod.mk.injEq] at h'
  obtain ⟨_, h2⟩ := h'
  have h2' := toLex.injective h2
  simp only [Prod.mk.injEq] at h2'
  exact Complex.ext h2'.1 h2'.2

lemma norm_le_of_cle_le {z w : ℂ} (h : cle z ≤ cle w) : ‖z‖ ≤ ‖w‖ := by
  unfold cle at h
  rcases (Prod.Lex.le_iff.mp h) with h1 | ⟨h1, _⟩
  · exact h1.le
  · exact h1.le

lemma rang_strictMono (S : Set ℂ)
    (hfin : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite) :
    ∀ z ∈ S, ∀ w ∈ S, cle z < cle w → rang S hfin z < rang S hfin w := by
  intro z hz w hw hzw
  unfold rang
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨z, ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      exact ⟨hz, hzw⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_and]
      intro _
      exact lt_irrefl _
  · intro u hu
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hu ⊢
    exact ⟨hu.1, hu.2.trans hzw⟩

lemma rang_injOn (S : Set ℂ)
    (hfin : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite) :
    Set.InjOn (rang S hfin) S := by
  intro z hz w hw h
  by_contra hne
  have hne' : cle z ≠ cle w := fun h' => hne (cle_injective h')
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · exact absurd h (rang_strictMono S hfin z hz w hw hlt).ne
  · exact absurd h.symm (rang_strictMono S hfin w hw z hz hgt).ne

lemma rang_lt_of_pred (S : Set ℂ)
    (hfin : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite)
    {z₁ w : ℂ} (hz₁ : z₁ ∈ S) (hw : w ∈ S) (h : cle w < cle z₁) :
    rang S hfin w < rang S hfin z₁ :=
  rang_strictMono S hfin w hw z₁ hz₁ h

lemma rang_surj (S : Set ℂ) (hinf : S.Infinite)
    (hfin : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite) :
    ∀ n : ℕ, ∃ z ∈ S, rang S hfin z = n := by
  intro n
  by_contra hno
  push Not at hno
  have hex : ∃ z ∈ S, n < rang S hfin z := by
    by_contra hall
    push Not at hall
    have hmaps : Set.MapsTo (rang S hfin) S (Finset.range (n + 1) : Set ℕ) := by
      intro z hz
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (hall z hz)
    exact hinf (Set.Finite.of_injOn hmaps (rang_injOn S hfin) (Finset.finite_toSet _))
  obtain ⟨z₁, hz₁S, hz₁⟩ := hex
  set P : Finset ℂ := (predecesseurs_finis S hfin z₁).toFinset with hP
  have hcard : P.card = rang S hfin z₁ := rfl
  have hmaps : ∀ w ∈ P, rang S hfin w ∈ Finset.range (rang S hfin z₁) := by
    intro w hw
    simp only [hP, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hw
    exact Finset.mem_range.mpr (rang_lt_of_pred S hfin hz₁S hw.1 hw.2)
  have hinjP : Set.InjOn (rang S hfin) (P : Set ℂ) := by
    intro a ha b hb hab
    simp only [hP, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at ha hb
    exact rang_injOn S hfin ha.1 hb.1 hab
  have himg : P.image (rang S hfin) = Finset.range (rang S hfin z₁) := by
    apply Finset.eq_of_subset_of_card_le
    · intro k hk
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hk
      exact hmaps w hw
    · rw [Finset.card_range, Finset.card_image_of_injOn hinjP, hcard]
  have hn : n ∈ Finset.range (rang S hfin z₁) := Finset.mem_range.mpr hz₁
  rw [← himg] at hn
  obtain ⟨w, hw, hwn⟩ := Finset.mem_image.mp hn
  simp only [hP, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hw
  exact hno w hw.1 hwn

lemma exists_enum_norm_mono (S : Set ℂ) (hinf : S.Infinite)
    (hfin : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite) :
    ∃ f : ℕ → ℂ, Function.Injective f ∧ Set.range f = S ∧
      ∀ i j, i ≤ j → ‖f i‖ ≤ ‖f j‖ := by
  have hmono : ∀ z ∈ S, ∀ w ∈ S, cle z < cle w → rang S hfin z < rang S hfin w :=
    rang_strictMono S hfin
  have hinj : Set.InjOn (rang S hfin) S := rang_injOn S hfin
  have hsurj : ∀ n : ℕ, ∃ z ∈ S, rang S hfin z = n := rang_surj S hinf hfin
  choose f hfS hfrang using hsurj
  refine ⟨f, ?_, ?_, ?_⟩
  · intro i j hij
    rw [← hfrang i, ← hfrang j, hij]
  · ext z
    constructor
    · rintro ⟨n, rfl⟩; exact hfS n
    · intro hz
      obtain ⟨n, hn⟩ : ∃ n, rang S hfin z = n := ⟨_, rfl⟩
      refine ⟨n, hinj (hfS n) hz ?_⟩
      rw [hfrang n, hn]
  · intro i j hij
    have hle : cle (f i) ≤ cle (f j) := by
      by_contra hlt
      push Not at hlt
      have := rang_strictMono S hfin (f j) (hfS j) (f i) (hfS i) hlt
      rw [hfrang, hfrang] at this
      omega
    exact norm_le_of_cle_le hle


lemma prepend2_injective (a b : ℂ) (g : ℕ → ℂ) (hab : a ≠ b)
    (hg : Function.Injective g) (hga : ∀ k, g k ≠ a) (hgb : ∀ k, g k ≠ b) :
    Function.Injective (prepend2 a b g) := by
  intro i j hij
  match i, j with
  | 0, 0 => rfl
  | 0, 1 => exact absurd hij hab
  | 1, 0 => exact absurd hij hab.symm
  | 1, 1 => rfl
  | 0, j + 2 => exact absurd hij.symm (hga j)
  | j + 2, 0 => exact absurd hij (hga j)
  | 1, j + 2 => exact absurd hij.symm (hgb j)
  | j + 2, 1 => exact absurd hij (hgb j)
  | i + 2, j + 2 => exact congrArg (· + 2) (hg hij)

lemma prepend2_range (a b : ℂ) (g : ℕ → ℂ) (L : Set ℂ)
    (haL : a ∈ L) (hbL : b ∈ L) (hg : Set.range g = L \ {a, b}) :
    Set.range (prepend2 a b g) = L := by
  ext z
  constructor
  · rintro ⟨n, rfl⟩
    rcases n with _ | _ | k
    · simpa using haL
    · simpa using hbL
    · have : g k ∈ Set.range g := ⟨k, rfl⟩
      rw [hg] at this
      simpa using this.1
  · intro hz
    by_cases hza : z = a
    · exact ⟨0, by simp [hza]⟩
    · by_cases hzb : z = b
      · exact ⟨1, by simp [hzb]⟩
      · have : z ∈ Set.range g := by
          rw [hg]
          exact ⟨hz, by simp [hza, hzb]⟩
        obtain ⟨k, rfl⟩ := this
        exact ⟨k + 2, by simp⟩

lemma prepend2_mono (a b : ℂ) (g : ℕ → ℂ) (hab : ‖a‖ ≤ ‖b‖)
    (hbg : ∀ k, ‖b‖ ≤ ‖g k‖) (hg : ∀ i j, i ≤ j → ‖g i‖ ≤ ‖g j‖) :
    ∀ i j, i ≤ j → ‖prepend2 a b g i‖ ≤ ‖prepend2 a b g j‖ := by
  intro i j hij
  rcases i with _ | _ | i <;> rcases j with _ | _ | j <;>
    (try simp only [prepend2_zero, prepend2_add_two]) <;>
    first
    | exact le_refl _
    | exact hab
    | exact hbg _
    | exact le_trans hab (hbg _)
    | exact hg _ _ (by omega)
    | (exfalso; omega)

open LambdaRiemann in
lemma exists_enum_with_two_real (hDeux : DeuxPremiersZerosReels)
    (hinf : LambdaZeros.Infinite) :
    ∃ f : ℕ → ℂ, Function.Injective f ∧ Set.range f = LambdaZeros ∧
      (∀ i j, i ≤ j → ‖f i‖ ≤ ‖f j‖) ∧ (f 0).im = 0 ∧ (f 1).im = 0 := by
  obtain ⟨a, b, hab, ha0, hb0, hare, hbre, hnorm, hmin⟩ := hDeux
  have haL : a ∈ LambdaZeros := (mem_LambdaZeros_iff a).mpr ha0
  have hbL : b ∈ LambdaZeros := (mem_LambdaZeros_iff b).mpr hb0
  set S : Set ℂ := LambdaZeros \ {a, b} with hS
  have hSinf : S.Infinite := hinf.sdiff (Set.toFinite {a, b})
  have hSfin : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite := by
    intro R
    exact (lambdaZeros_finite_ball R).subset
      (Set.inter_subset_inter_left _ Set.sdiff_subset)
  obtain ⟨g, hginj, hgrange, hgmono⟩ := exists_enum_norm_mono S hSinf hSfin
  have hg_mem : ∀ k, g k ∈ S := fun k => hgrange ▸ ⟨k, rfl⟩
  have hg_ne_a : ∀ k, g k ≠ a := fun k h => (hg_mem k).2 (Or.inl h)
  have hg_ne_b : ∀ k, g k ≠ b := fun k h => (hg_mem k).2 (Or.inr h)
  have hg_ge : ∀ k, ‖b‖ ≤ ‖g k‖ := fun k =>
    hmin (g k) ((mem_LambdaZeros_iff _).mp (hg_mem k).1) (hg_ne_a k) (hg_ne_b k)
  refine ⟨prepend2 a b g, ?_, ?_, ?_, ?_, ?_⟩
  · exact prepend2_injective a b g hab hginj hg_ne_a hg_ne_b
  · exact prepend2_range a b g LambdaZeros haL hbL hgrange
  · exact prepend2_mono a b g hnorm hg_ge hgmono
  · simpa using hare
  · simpa using hbre


lemma palier_strict_of_inj
    (hPaliers : PaliersStrictsXiRiemann)
    (γ : ℕ → ℂ)
    (hzero : ∀ n, 1 ≤ n → XiRiemann (γ n) = 0)
    (hinj : ∀ m n, 1 ≤ m → 1 ≤ n → γ m = γ n → m = n) :
    ∀ n, 1 ≤ n → ‖γ (n + 1)‖ = ‖γ n‖ →
      (γ (n + 1) = starRingEnd ℂ (γ n)) ∧ ‖γ (n + 2)‖ ≠ ‖γ n‖ := by
  intro n hn hnorm1
  have hconj1 : γ (n + 1) = starRingEnd ℂ (γ n) :=
    hPaliers (γ n) (γ (n + 1))
      (hzero n hn) (hzero (n + 1) (by omega))
      (fun h => by have := hinj n (n + 1) hn (by omega) h; omega)
      hnorm1.symm
  refine ⟨hconj1, ?_⟩
  intro hnorm2
  have hconj2 : γ (n + 2) = starRingEnd ℂ (γ n) :=
    hPaliers (γ n) (γ (n + 2))
      (hzero n hn) (hzero (n + 2) (by omega))
      (fun h => by have := hinj n (n + 2) hn (by omega) h; omega)
      hnorm2.symm
  have heq : γ (n + 2) = γ (n + 1) := hconj2.trans hconj1.symm
  have := hinj (n + 2) (n + 1) (by omega) (by omega) heq
  omega

lemma conj_of_norm_eq
    {Xi : ℂ → ℂ} {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration Xi γ m)
    {i j : ℕ} (hi : 1 ≤ i) (hj : 1 ≤ j) (hij : i ≠ j)
    (hnorm : ‖γ i‖ = ‖γ j‖) :
    γ j = starRingEnd ℂ (γ i) := by
  have h_lt : ∀ a b, 1 ≤ a → a < b → ‖γ a‖ = ‖γ b‖ → γ b = starRingEnd ℂ (γ a) := by
    intro a b ha hab h_eq
    have h_step : ‖γ (a + 1)‖ = ‖γ a‖ := le_antisymm
      (by rw [h_eq]; exact hEnum.mono_norm (a + 1) b (by omega) (by omega))
      (hEnum.mono_norm a (a + 1) ha (by omega))
    have h_pal := hEnum.palier_strict a ha h_step
    by_cases h_ba : b = a + 1
    · subst h_ba; exact h_pal.1
    · exfalso
      apply h_pal.2
      exact le_antisymm
        (by rw [h_eq]; exact hEnum.mono_norm (a + 2) b (by omega) (by omega))
        (hEnum.mono_norm a (a + 2) ha (by omega))
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact h_lt i j hi hlt hnorm
  · exact (hij rfl).elim
  · have h_symm := h_lt j i hj hgt hnorm.symm
    rw [h_symm, RingHomCompTriple.comp_apply, RingHom.id_apply]






lemma exists_zeroEnumeration_XiRiemann (hHardy : HardyTheorem)
    (hDeux : DeuxPremiersZerosReels)
    (hPaliers : PaliersStrictsXiRiemann) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ), ZeroEnumeration XiRiemann γ m := by
  have hinf : LambdaZeros.Infinite := lambdaZeros_infinite hHardy
  obtain ⟨f, hfinj, hfrange, hfmono, hf0, hf1⟩ :=
    exists_enum_with_two_real hDeux hinf
  have hzero : ∀ n, 1 ≤ n → XiRiemann (f (n - 1)) = 0 := by
    intro n _
    have : f (n - 1) ∈ LambdaZeros := hfrange ▸ ⟨n - 1, rfl⟩
    exact (mem_LambdaZeros_iff _).mp this
  have hinj : ∀ i j, 1 ≤ i → 1 ≤ j → f (i - 1) = f (j - 1) → i = j := by
    intro i j hi hj hij
    have := hfinj hij
    omega
  refine ⟨fun n => f (n - 1), fun _ => 1, ?_⟩
  refine
    { zero_mem := hzero
      injective := hinj
      exhaustive := ?_
      mono_norm := ?_
      palier_strict := palier_strict_of_inj hPaliers (fun n => f (n - 1)) hzero hinj
      mult_pos := ?_
      real_one := ?_
      real_two := ?_
      conj_mult := ?_ }
  · intro z hz
    have hz' : z ∈ LambdaZeros := (mem_LambdaZeros_iff z).mpr hz
    rw [← hfrange] at hz'
    obtain ⟨k, hk⟩ := hz'
    exact ⟨k + 1, by omega, by simpa using hk⟩
  · intro i j hi hij
    exact hfmono (i - 1) (j - 1) (by omega)
  · intro n _; exact le_refl 1
  · simpa using hf0
  · simpa using hf1
  · intro i j _ _ _
    rfl


open ComplexConjugate in
lemma XiRiemann_conj_symm (z : ℂ) :
    XiRiemann (conj z) = conj (XiRiemann (-z)) := by
  unfold XiRiemann RiemannDef.xiDecale
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := map_ofNat _ 2
  have harg : (1 / 2 : ℂ) + I * conj z = conj ((1 / 2 : ℂ) + I * (-z)) := by
    simp only [map_add, map_mul, map_neg, map_div₀, map_one, Complex.conj_I, h2]
    ring
  rw [harg, xiEntiere_conj]

lemma XiRiemann_zero_conj (z : ℂ) (hz : XiRiemann z = 0) :
    XiRiemann ((starRingEnd ℂ) z) = 0 := by
  rw [XiRiemann_conj, hz, map_zero]

lemma norm_conj_eq (z : ℂ) : ‖(starRingEnd ℂ) z‖ = ‖z‖ :=
  RCLike.norm_conj z

lemma exists_index_conj (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ m) (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, 1 ≤ k ∧ γ k = (starRingEnd ℂ) (γ n) :=
  henum.exhaustive _ (XiRiemann_zero_conj _ (henum.zero_mem n hn))

lemma conjugueSuit_of_enum (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (_ : ZeroEnumeration XiRiemann γ m)
    (hadj : ConjAdjacent γ)
    (hm : ∀ n, 3 ≤ n → m (n + 1) = m n) :
    ∀ n₀, 3 ≤ n₀ → 0 < (γ n₀).im → ConjugueSuit γ m n₀ := by
  intro n₀ h3 hpos
  exact ⟨hadj n₀ h3 hpos, hm n₀ h3⟩

lemma first_nonreal_im_pos (γ : ℕ → ℂ)
    (hadj' : ∀ n, 3 ≤ n → (γ n).im < 0 → γ (n - 1) = (starRingEnd ℂ) (γ n))
    (n₀ : ℕ) (h3 : 3 ≤ n₀) (hne : (γ n₀).im ≠ 0)
    (hreal : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) :
    0 < (γ n₀).im := by
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exfalso
    have h1 := hadj' n₀ h3 hneg
    have h2 := hreal (n₀ - 1) (by omega) (by omega)
    rw [h1] at h2
    simp at h2
    linarith
  · exact hpos

lemma exists_index_of_mem_range
    {S : Set ℂ} {f : ℕ → ℂ} (hfrange : Set.range f = S)
    {a : ℂ} (ha : a ∈ S) : ∃ i : ℕ, f i = a := by
  rw [← hfrange] at ha
  exact ha

lemma infinite_diff_pair
    {S : Set ℂ} (hS : S.Infinite) (a b : ℂ) :
    (S \ {a, b}).Infinite := by
  exact hS.sdiff (Set.toFinite {a, b})

lemma diff_finite_ball (S : Set ℂ) (a b : ℂ)
    (hS : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite) (R : ℝ) :
    ((S \ {a, b}) ∩ Metric.closedBall (0 : ℂ) R).Finite :=
  (hS R).subset (Set.inter_subset_inter_left _ Set.sdiff_subset)

lemma exists_enum_diff
    (T : Set ℂ) (hT : T.Infinite)
    (hfin : ∀ R : ℝ, (T ∩ Metric.closedBall (0 : ℂ) R).Finite) :
    ∃ g : ℕ → ℂ, Function.Injective g ∧ Set.range g = T ∧
      (∀ i j, i ≤ j → ‖g i‖ ≤ ‖g j‖) := by
  exact exists_enum_norm_mono T hT hfin

lemma norm_le_of_mem_diff
    {S : Set ℂ} {a b : ℂ}
    (hmin : ∀ z ∈ S, z ≠ a → z ≠ b → ‖b‖ ≤ ‖z‖)
    {z : ℂ} (hz : z ∈ S \ {a, b}) : ‖b‖ ≤ ‖z‖ := by
  obtain ⟨hzS, hzab⟩ := hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzab
  exact hmin z hzS hzab.1 hzab.2


lemma build_head
    {S : Set ℂ} {a b : ℂ} (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hab' : ‖a‖ ≤ ‖b‖)
    {g : ℕ → ℂ} (hginj : Function.Injective g)
    (hgrange : Set.range g = S \ {a, b})
    (hgmono : ∀ i j, i ≤ j → ‖g i‖ ≤ ‖g j‖)
    (hgb : ∀ n, ‖b‖ ≤ ‖g n‖) :
    ∃ f' : ℕ → ℂ, Function.Injective f' ∧ Set.range f' = S ∧
      (∀ i j, i ≤ j → ‖f' i‖ ≤ ‖f' j‖) ∧ f' 0 = a ∧ f' 1 = b := by
  have hg_mem : ∀ k, g k ∈ S \ {a, b} := fun k => by
    rw [← hgrange]
    exact ⟨k, rfl⟩
  have hg_ne_a : ∀ k, g k ≠ a := fun k h => (hg_mem k).2 (by simp [h])
  have hg_ne_b : ∀ k, g k ≠ b := fun k h => (hg_mem k).2 (by simp [h])
  refine ⟨fun n => Nat.casesOn n a (fun m => Nat.casesOn m b (fun k => g k)), ?_, ?_, ?_, rfl, rfl⟩
  · intro m n hmn
    match m, n with
    | 0, 0 => rfl
    | 0, 1 => exact absurd hmn (fun h => hab h)
    | 0, (k+2) => exact absurd hmn (fun h => hg_ne_a k h.symm)
    | 1, 0 => exact absurd hmn (fun h => hab h.symm)
    | 1, 1 => rfl
    | (j+2), 0 => exact absurd hmn.symm (fun h => hg_ne_a j h.symm)
    | 1, (k+2) => exact absurd hmn (fun h => hg_ne_b k h.symm)
    | (j+2), 1 => exact absurd hmn.symm (fun h => hg_ne_b j h.symm)
    | (j+2), (k+2) => congr 2; exact hginj hmn
  · apply Set.eq_of_subset_of_subset
    · rintro x ⟨n, rfl⟩
      match n with
      | 0 => exact ha
      | 1 => exact hb
      | (k+2) => exact (hg_mem k).1
    · intro z hz
      by_cases hza : z = a
      · exact ⟨0, hza.symm⟩
      · by_cases hzb : z = b
        · exact ⟨1, hzb.symm⟩
        · have hzg : z ∈ Set.range g := by
            rw [hgrange]
            exact ⟨hz, by simp [hza, hzb]⟩
          obtain ⟨k, hk⟩ := hzg
          exact ⟨k+2, hk⟩
  · intro i j hij
    match i, j with
    | 0, 0 => exact le_refl _
    | 0, 1 => exact hab'
    | 0, (k+2) => exact le_trans hab' (hgb k)
    | 1, 0 => omega
    | 1, 1 => exact le_refl _
    | 1, (k+2) => exact hgb k
    | (i+2), 0 => omega
    | (i+2), 1 => omega
    | (i+2), (k+2) => exact hgmono i k (by omega)

lemma enum_norm_mono_head
    (S : Set ℂ) (hSinf : S.Infinite)
    (hfin_ball : ∀ R : ℝ, (S ∩ Metric.closedBall (0 : ℂ) R).Finite)
    (f : ℕ → ℂ) (__ : Function.Injective f)
    (_ : Set.range f = S) (_ : ∀ i j, i ≤ j → ‖f i‖ ≤ ‖f j‖)
    (a b : ℂ) (hab : a ≠ b) (ha : a ∈ S) (hb : b ∈ S)
    (hab' : ‖a‖ ≤ ‖b‖) (hmin : ∀ z ∈ S, z ≠ a → z ≠ b → ‖b‖ ≤ ‖z‖) :
    ∃ f' : ℕ → ℂ, Function.Injective f' ∧ Set.range f' = S ∧
      (∀ i j, i ≤ j → ‖f' i‖ ≤ ‖f' j‖) ∧ f' 0 = a ∧ f' 1 = b := by
  obtain ⟨g, hginj, hgrange, hgmono⟩ :=
    exists_enum_diff (S \ {a, b}) (infinite_diff_pair hSinf a b)
      (diff_finite_ball S a b hfin_ball)
  exact build_head hab ha hb hab' hginj hgrange hgmono
    (fun n => norm_le_of_mem_diff hmin (by rw [← hgrange]; exact ⟨n, rfl⟩))

lemma zeroEnumeration_swap
    {γ₀ : ℕ → ℂ} {m : ℕ → ℕ} (h : ZeroEnumeration XiRiemann γ₀ m)
    {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hnorm : ‖γ₀ p‖ = ‖γ₀ q‖) :
    ZeroEnumeration XiRiemann (fun n => γ₀ (Equiv.swap p q n))
      (fun n => m (Equiv.swap p q n)) := by
  have hge : ∀ n, 1 ≤ n → 1 ≤ Equiv.swap p q n := by
    intro n hn
    by_cases hnp : n = p
    · rw [hnp, Equiv.swap_apply_left]; omega
    · by_cases hnq : n = q
      · rw [hnq, Equiv.swap_apply_right]; omega
      · rw [Equiv.swap_apply_of_ne_of_ne hnp hnq]; exact hn
  have hfix1 : Equiv.swap p q 1 = 1 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hfix2 : Equiv.swap p q 2 = 2 :=
    Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hnorm_swap : ∀ n, ‖γ₀ (Equiv.swap p q n)‖ = ‖γ₀ n‖ := by
    intro n
    by_cases hnp : n = p
    · rw [hnp, Equiv.swap_apply_left]; exact hnorm.symm
    · by_cases hnq : n = q
      · rw [hnq, Equiv.swap_apply_right]; exact hnorm
      · rw [Equiv.swap_apply_of_ne_of_ne hnp hnq]
  refine
    { zero_mem := ?_
      injective := ?_
      exhaustive := ?_
      mono_norm := ?_
      palier_strict := ?_
      mult_pos := ?_
      real_one := ?_
      real_two := ?_
      conj_mult := ?_ }
  · intro n hn
    exact h.zero_mem _ (hge n hn)
  · intro i j hi hj hij
    have h1 : Equiv.swap p q i = Equiv.swap p q j :=
      h.injective _ _ (hge i hi) (hge j hj) hij
    exact (Equiv.swap p q).injective h1
  · intro z hz
    obtain ⟨k, hk1, hk⟩ := h.exhaustive z hz
    refine ⟨Equiv.swap p q k, hge k hk1, ?_⟩
    simp only [Equiv.swap_apply_self]
    exact hk
  · intro i j hi hij
    rw [hnorm_swap i, hnorm_swap j]
    exact h.mono_norm i j hi hij
  · intro n hn h_eq
    have h_eq' : ‖γ₀ (n + 1)‖ = ‖γ₀ n‖ := by
      rwa [hnorm_swap (n + 1), hnorm_swap n] at h_eq
    refine ⟨?_, ?_⟩
    · exact conj_of_norm_eq h
        (hge n hn)
        (hge (n + 1) (by omega))
        (fun h_swap => by have := (Equiv.swap p q).injective h_swap; omega)
        h_eq.symm
    · rw [hnorm_swap (n + 2), hnorm_swap n]
      exact (h.palier_strict n hn h_eq').2
  · intro n hn
    exact h.mult_pos _ (hge n hn)
  · show (γ₀ (Equiv.swap p q 1)).im = 0
    rw [hfix1]; exact h.real_one
  · show (γ₀ (Equiv.swap p q 2)).im = 0
    rw [hfix2]; exact h.real_two
  · intro i j hi hj hconj
    exact h.conj_mult (Equiv.swap p q i) (Equiv.swap p q j)
      (hge i hi) (hge j hj) hconj

open LambdaRiemann in
lemma exists_zeroEnumeration_XiRiemann_first
    (hHardy : HardyTheorem) (hDeux : DeuxPremiersZerosReels)
    (hPaliers : PaliersStrictsXiRiemann) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ), ZeroEnumeration XiRiemann γ m ∧
      ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n := by
  classical
  have hinf : LambdaZeros.Infinite := lambdaZeros_infinite hHardy
  obtain ⟨f, hfinj, hfrange, hfmono⟩ :=
    exists_enum_norm_mono LambdaZeros hinf lambdaZeros_finite_ball
  obtain ⟨a, b, hab, ha0, hb0, haim, hbim, hanb, hmin⟩ := hDeux
  have haΛ : a ∈ LambdaZeros := (mem_LambdaZeros_iff a).2 ha0
  have hbΛ : b ∈ LambdaZeros := (mem_LambdaZeros_iff b).2 hb0
  obtain ⟨g, hginj, hgrange, hgmono, hg0, hg1⟩ :=
    enum_norm_mono_head LambdaZeros hinf lambdaZeros_finite_ball f hfinj hfrange hfmono
      a b hab haΛ hbΛ hanb
      (fun z hz hza hzb => hmin z ((mem_LambdaZeros_iff z).1 hz) hza hzb)
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : ℕ → ℂ, γ₀ = fun n => g (n - 1) := ⟨_, rfl⟩
  have hev : ∀ n, γ₀ n = g (n - 1) := fun n => by rw [hγ₀]
  have hzero₀ : ∀ n, 1 ≤ n → XiRiemann (γ₀ n) = 0 := by
    intro n _
    have hmem : g (n - 1) ∈ LambdaZeros := by
      rw [← hgrange]; exact Set.mem_range_self (n - 1)
    rw [hev n]
    exact (mem_LambdaZeros_iff _).1 hmem
  have hinj₀ : ∀ i j, 1 ≤ i → 1 ≤ j → γ₀ i = γ₀ j → i = j := by
    intro i j hi hj hij
    rw [hev i, hev j] at hij
    have h' : i - 1 = j - 1 := hginj hij
    omega
  have hZE₀ : ZeroEnumeration XiRiemann γ₀ (fun _ => 1) := by
    refine
      { zero_mem := hzero₀
        injective := hinj₀
        exhaustive := ?_
        mono_norm := ?_
        palier_strict := palier_strict_of_inj hPaliers γ₀ hzero₀ hinj₀
        mult_pos := ?_
        real_one := ?_
        real_two := ?_
        conj_mult := ?_ }
    · intro z hz
      have hzΛ : z ∈ LambdaZeros := (mem_LambdaZeros_iff z).2 hz
      rw [← hgrange] at hzΛ
      obtain ⟨k, hk⟩ := hzΛ
      refine ⟨k + 1, by omega, ?_⟩
      rw [hev (k + 1)]
      simpa using hk
    · intro i j hi hij
      rw [hev i, hev j]
      exact hgmono (i - 1) (j - 1) (by omega)
    · intro n _
      exact le_refl 1
    · rw [hev 1]
      simpa [hg0] using haim
    · rw [hev 2]
      simpa [hg1] using hbim
    · intro i j _ _ _
      rfl
  by_cases hex : ∃ n, 3 ≤ n ∧ (γ₀ n).im ≠ 0
  · let n₀ := Nat.find hex
    have hn₀ : 3 ≤ n₀ ∧ (γ₀ n₀).im ≠ 0 := Nat.find_spec hex
    have hn₀min : ∀ j, j < n₀ → ¬ (3 ≤ j ∧ (γ₀ j).im ≠ 0) :=
      fun j hj => Nat.find_min hex hj
    have hreal_before : ∀ j, 1 ≤ j → j < n₀ → (γ₀ j).im = 0 := by
      intro j hj1 hjn
      by_cases h3 : 3 ≤ j
      · by_contra hne
        exact hn₀min j hjn ⟨h3, hne⟩
      · interval_cases j
        · exact hZE₀.real_one
        · exact hZE₀.real_two
    have hconjzero : XiRiemann ((starRingEnd ℂ) (γ₀ n₀)) = 0 :=
      XiRiemann_zero_conj _ (hZE₀.zero_mem n₀ (by omega))
    obtain ⟨k, hk1, hk⟩ := hZE₀.exhaustive _ hconjzero
    have hk_ne : k ≠ n₀ := by
      intro h
      rw [h] at hk
      have := congrArg Complex.im hk
      simp at this
      exact hn₀.2 (by linarith)
    have hk_gt : n₀ < k := by
      by_contra hle
      have hlt : k < n₀ := lt_of_le_of_ne (not_lt.1 hle) hk_ne
      have hr : (γ₀ k).im = 0 := hreal_before k hk1 hlt
      rw [hk, Complex.conj_im, neg_eq_zero] at hr
      exact hn₀.2 hr
    have hnorm_eq : ‖γ₀ k‖ = ‖γ₀ n₀‖ := by
      rw [hk]; simp
    have hnorm_mid : ‖γ₀ (n₀ + 1)‖ = ‖γ₀ k‖ := by
      apply le_antisymm
      · exact hZE₀.mono_norm (n₀ + 1) k (by omega) (by omega)
      · rw [hnorm_eq]
        exact hZE₀.mono_norm n₀ (n₀ + 1) (by omega) (by omega)
    refine ⟨fun n => γ₀ (Equiv.swap (n₀ + 1) k n),
            fun n => (fun _ => 1) (Equiv.swap (n₀ + 1) k n), ?_, ?_⟩
    · exact zeroEnumeration_swap hZE₀ (by omega) (by omega) hnorm_mid
    · intro n hn hne hprev
      have hn_eq : n = n₀ := by
        by_contra hneq
        rcases lt_or_gt_of_ne hneq with hlt | hgt
        · have hs : Equiv.swap (n₀ + 1) k n = n := by
            apply Equiv.swap_apply_of_ne_of_ne <;> omega
          simp only [hs] at hne
          exact hn₀min n hlt ⟨hn, hne⟩ |>.elim
        · have hs : Equiv.swap (n₀ + 1) k n₀ = n₀ := by
            apply Equiv.swap_apply_of_ne_of_ne <;> omega
          have := hprev n₀ (by omega) hgt
          simp only [hs] at this
          exact hn₀.2 this
      subst hn_eq
      refine ⟨?_, rfl⟩
      have h1 : Equiv.swap (n₀ + 1) k (n₀ + 1) = k := Equiv.swap_apply_left _ _
      have h2 : Equiv.swap (n₀ + 1) k n₀ = n₀ := by
        apply Equiv.swap_apply_of_ne_of_ne <;> omega
      change γ₀ (Equiv.swap (n₀ + 1) k (n₀ + 1)) =
        (starRingEnd ℂ) (γ₀ (Equiv.swap (n₀ + 1) k n₀))
      rw [h1, h2]
      exact hk
  · push Not at hex
    exact ⟨γ₀, fun _ => 1, hZE₀, fun n hn hne _ => absurd (hex n hn) hne⟩



lemma sq_conj_sub_neg (z : ℂ) (hz : z.im ≠ 0) :
    ((starRingEnd ℂ z - z) ^ 2).re < 0 := by
  have h1 : (starRingEnd ℂ z - z) = ((-2 * z.im : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp ; ring
  have h2 : (starRingEnd ℂ z - z) ^ 2 = (((-(( -2 * z.im) ^ 2)) : ℝ) : ℂ) := by
    rw [h1, mul_pow, Complex.I_sq]
    push_cast
    ring
  rw [h2, Complex.ofReal_re]
  have : 0 < (-2 * z.im) ^ 2 := by positivity
  linarith

lemma re_ofReal_mul_eq (r : ℝ) (z : ℂ) : ((r : ℂ) * z).re = r * z.re :=
  Complex.re_ofReal_mul r z

lemma re_ofReal_mul_neg {r : ℝ} {z : ℂ} (hr : 0 < r) (hz : z.re < 0) :
    ((r : ℂ) * z).re < 0 := by
  rw [Complex.re_ofReal_mul]
  exact mul_neg_of_pos_of_neg hr hz

lemma eq_ofReal_of_im_eq_zero {w : ℂ} (h : w.im = 0) : w = (w.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])


open InducRiemannZero BrainrotLemma_Riemann in
lemma delta_neg_palier_critique (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ m) (hpos : HankelPositive γ m)
    (n₀ : ℕ) (h3 : 3 ≤ n₀) (hne : (γ n₀).im ≠ 0)
    (hreal : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0)
    (hc : γ (n₀ + 1) = starRingEnd ℂ (γ n₀)) (hmm : m (n₀ + 1) = m n₀) :
    (Delta γ m (n₀ + 1) (n₀ + 1)).re < 0 := by
  have hprev : 0 < (Delta γ m (n₀ - 1) (n₀ - 1)).re :=
    (((hpos (n₀ - 1) (by omega)).2 (n₀ - 1) (by omega) le_rfl)).1
  have hfact : Delta γ m (n₀ + 1) (n₀ + 1) =
      ((m n₀ : ℂ) * (m (n₀ + 1) : ℂ)) * Delta γ m (n₀ - 1) (n₀ - 1)
        * (γ (n₀ + 1) - γ n₀) ^ 2
        * ∏ j ∈ Finset.Icc 1 (n₀ - 1),
            ((γ n₀ - γ j) ^ 2 * (γ (n₀ + 1) - γ j) ^ 2) := by
    have h1 : Delta γ m (n₀ + 1) (n₀ + 1) =
        (m (n₀ + 1) : ℂ) * Delta γ m n₀ n₀ *
          ∏ j ∈ Finset.Icc 1 n₀, (γ (n₀ + 1) - γ j) ^ 2 := by
      rw [delta_succ γ m n₀]
      rw [prod_fin_eq_prod_Icc n₀ (fun j => (γ (n₀ + 1) - γ j) ^ 2)]
    have h2 : Delta γ m n₀ n₀ =
        (m n₀ : ℂ) * Delta γ m (n₀ - 1) (n₀ - 1) *
          ∏ j ∈ Finset.Icc 1 (n₀ - 1), (γ n₀ - γ j) ^ 2 := by
      obtain ⟨k, hk⟩ : ∃ k, n₀ = k + 1 := ⟨n₀ - 1, by omega⟩
      subst hk
      rw [Nat.add_sub_cancel]
      rw [delta_succ γ m k]
      rw [prod_fin_eq_prod_Icc k (fun j => (γ (k + 1) - γ j) ^ 2)]
    have h3 : ∏ j ∈ Finset.Icc 1 n₀, (γ (n₀ + 1) - γ j) ^ 2 =
        (γ (n₀ + 1) - γ n₀) ^ 2 *
          ∏ j ∈ Finset.Icc 1 (n₀ - 1), (γ (n₀ + 1) - γ j) ^ 2 := by
      obtain ⟨k, rfl⟩ : ∃ k, n₀ = k + 1 := ⟨n₀ - 1, by omega⟩
      rw [Finset.prod_Icc_succ_top (by omega)]
      simp [mul_comm]
    rw [h1, h2, h3, Finset.prod_mul_distrib]
    ring
  have hprod : ∀ j ∈ Finset.Icc 1 (n₀ - 1),
      (γ n₀ - γ j) ^ 2 * (γ (n₀ + 1) - γ j) ^ 2
        = (((‖γ n₀ - γ j‖ ^ 4 : ℝ)) : ℂ) := by
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hj2 : j < n₀ := by have := (Finset.mem_Icc.mp hj).2; omega
    have hγj : starRingEnd ℂ (γ j) = γ j :=
      Complex.conj_eq_iff_im.mpr (hreal j hj1 hj2)
    have hsub : γ (n₀ + 1) - γ j = starRingEnd ℂ (γ n₀ - γ j) := by
      rw [hc, map_sub, hγj]
    rw [hsub, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  rw [hfact, Finset.prod_congr rfl hprod, hc, hmm]
  have hR : 0 < ∏ j ∈ Finset.Icc 1 (n₀ - 1), ‖γ n₀ - γ j‖ ^ 4 := by
    apply Finset.prod_pos
    intro j hj
    have hj1 := (Finset.mem_Icc.mp hj).1
    have hj2 : j < n₀ := by have := (Finset.mem_Icc.mp hj).2; omega
    have hnz : γ n₀ - γ j ≠ 0 := by
      intro h
      apply hne
      have h' := congrArg Complex.im h
      rw [Complex.sub_im, hreal j hj1 hj2, Complex.zero_im, sub_zero] at h'
      exact h'
    positivity
  have hmpos : 0 < (m n₀ : ℝ) := by
    exact_mod_cast (henum.mult_pos n₀ (by omega))
  have hsq := sq_conj_sub_neg (γ n₀) hne
  have hDim := (hpos (n₀ - 1) (by omega)).2 (n₀ - 1) (by omega) le_rfl
  have hD : Delta γ m (n₀ - 1) (n₀ - 1)
      = ((Delta γ m (n₀ - 1) (n₀ - 1)).re : ℂ) := eq_ofReal_of_im_eq_zero hDim.2
  set d : ℝ := (Delta γ m (n₀ - 1) (n₀ - 1)).re with hd
  have hreg :
      (↑(m n₀) * ↑(m n₀) * Delta γ m (n₀ - 1) (n₀ - 1)
          * ((starRingEnd ℂ) (γ n₀) - γ n₀) ^ 2
          * ∏ x ∈ Finset.Icc 1 (n₀ - 1), (↑(‖γ n₀ - γ x‖ ^ 4) : ℂ))
        = (((m n₀ : ℝ) * (m n₀ : ℝ) * d
              * ∏ x ∈ Finset.Icc 1 (n₀ - 1), ‖γ n₀ - γ x‖ ^ 4 : ℝ) : ℂ)
          * ((starRingEnd ℂ) (γ n₀) - γ n₀) ^ 2 := by
    rw [hD]
    push_cast
    ring
  rw [hreg]
  apply re_ofReal_mul_neg _ hsq
  exact mul_pos (mul_pos (mul_pos hmpos hmpos) hDim.1) hR

lemma propagation_of_enum (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (_ : HardyTheorem)
    (henum : ZeroEnumeration XiRiemann γ m)
    (_ : DeuxPremiersZerosReels)
    (hpos : HankelPositive γ m)
    (hconj : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → ConjugueSuit γ m n₀) :
    ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → PropagationDefaut γ n₀ := by
  intro n₀ h3 hne hreal N hN hNreal
  have hCS := hconj n₀ h3 hne hreal
  obtain ⟨hc, hmm⟩ := hCS
  have hneg := delta_neg_palier_critique γ m henum hpos n₀ h3 hne hreal hc hmm
  have hP := (hpos (n₀ + 1) (by omega)).2 (n₀ + 1) (by omega) le_rfl
  exact absurd hP.1 (not_lt.mpr hneg.le)


theorem Riemann_Hypothesis_hDeux_hPos (hHardy : HardyTheorem)
    (hDeux : DeuxPremiersZerosReels)
    (hPaliers : PaliersStrictsXiRiemann)
    (hpos : ∀ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m → HankelPositive γ m) :
    RiemannHypothesis := by
  obtain ⟨γ, m, henum, hfirst⟩ :=
    exists_zeroEnumeration_XiRiemann_first hHardy hDeux hPaliers
  have hconj : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → ConjugueSuit γ m n₀ := by
    intro n₀ h3 hne hreal
    obtain ⟨hc, hmm⟩ := hfirst n₀ h3 hne hreal
    exact ⟨hc, hmm⟩
  have hprop : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → PropagationDefaut γ n₀ :=
    propagation_of_enum γ m hHardy henum hDeux (hpos γ m henum) hconj
  exact hypothesys_of_Riemann_conditional γ m henum hHardy hconj hprop


--------------------------------------------------------------------

lemma zeroCritique_to_Xi (s : ℂ) (hs : s ∈ zerosCritiques) :
    ∃ z : ℂ, z.im = 0 ∧ XiRiemann z = 0 ∧ 1 / 2 + Complex.I * z = s := by
  obtain ⟨hζ, hre⟩ := hs
  refine ⟨(s - 1 / 2) / Complex.I, ?_, ?_, ?_⟩
  · rw [Complex.div_im]
    simp [hre]
  · have harg : (1 / 2 : ℂ) + Complex.I * ((s - 1 / 2) / Complex.I) = s := by
      field_simp
      ring
    rw [XiRiemann_eq, harg]
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hre
      norm_num at hre
    have hs1 : s ≠ 1 := by
      intro h
      rw [h] at hre
      norm_num at hre
    have hΓ : Complex.Gammaℝ s ≠ 0 :=
      Complex.Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num)
    have hΛ : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0] at hζ
      rcases div_eq_zero_iff.mp hζ with h | h
      · exact h
      · exact absurd h hΓ
    have hxi : xi s = 0 := by
      unfold xi
      rw [hΛ, mul_zero]
    rw [← xi_eq_xiEntiere s hs0 hs1]
    exact hxi
  · field_simp
    ring

lemma XiRiemann_analytique : AnalyticOnNhd ℂ XiRiemann Set.univ := by
  have hd : Differentiable ℂ XiRiemann := by
    unfold XiRiemann RiemannDef.xiDecale xiEntiere
    have h0 : Differentiable ℂ (fun z : ℂ => completedRiemannZeta₀ (1 / 2 + Complex.I * z)) :=
      differentiable_completedZeta₀.comp (by fun_prop)
    exact ((((differentiable_const _).mul
              ((differentiable_const _).add
                ((differentiable_const _).mul differentiable_id))).mul
            ((((differentiable_const _).add
                ((differentiable_const _).mul differentiable_id)).sub
              (differentiable_const _)))).mul h0).add (differentiable_const _)
  exact fun z _ => hd.analyticAt z

lemma XiRiemann_not_identically_zero : ∃ z : ℂ, XiRiemann z ≠ 0 := by
  refine ⟨(3 / 2 : ℂ) / Complex.I, ?_⟩
  have harg : (1 / 2 : ℂ) + Complex.I * ((3 / 2 : ℂ) / Complex.I) = 2 := by
    field_simp
    ring
  rw [XiRiemann_eq, harg]
  have h20 : (2 : ℂ) ≠ 0 := by norm_num
  have h21 : (2 : ℂ) ≠ 1 := by norm_num
  rw [← xi_eq_xiEntiere 2 h20 h21]
  have hζ2 : riemannZeta 2 ≠ 0 := by
    rw [riemannZeta_two]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    exact div_ne_zero (pow_ne_zero 2 hπ) (by norm_num)
  have hΛ : completedRiemannZeta 2 ≠ 0 := by
    intro h
    apply hζ2
    rw [riemannZeta_def_of_ne_zero h20, h, zero_div]
  unfold xi
  intro h
  apply hΛ
  have h' : (1 / 2 : ℂ) * 2 * (2 - 1) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h).resolve_left h'

lemma zeros_Xi_bornes_finis (R : ℝ) :
    {z : ℂ | XiRiemann z = 0 ∧ ‖z‖ ≤ R}.Finite := by
  have hana : AnalyticOnNhd ℂ XiRiemann Set.univ := XiRiemann_analytique
  obtain ⟨z0, hz0⟩ := XiRiemann_not_identically_zero
  have hne : ∀ z : ℂ, ¬ (∀ᶠ w in nhds z, XiRiemann w = 0) := by
    intro z hloc
    have := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hloc
    exact hz0 (this (Set.mem_univ z0))
  have hK : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have hiso : ∀ z : ℂ, ∀ᶠ w in nhdsWithin z {z}ᶜ, XiRiemann w ≠ 0 := by
    intro z
    have hz : AnalyticAt ℂ XiRiemann z := hana z (Set.mem_univ z)
    rcases hz.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd h (hne z)
    · exact h
  set S : Set ℂ := {z : ℂ | XiRiemann z = 0 ∧ ‖z‖ ≤ R} with hS
  have hSsub : S ⊆ Metric.closedBall (0 : ℂ) R := by
    intro z hz
    simpa [Metric.mem_closedBall, dist_zero_right] using hz.2
  by_contra hinf
  have hSinf : S.Infinite := hinf
  obtain ⟨z, hzK, hzacc⟩ := hSinf.exists_accPt_of_subset_isCompact hK hSsub
  have h1 : ∃ᶠ w in nhdsWithin z {z}ᶜ, w ∈ S := by
    rw [accPt_iff_nhds] at hzacc
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨V, hVo, hzV, hVU⟩ := mem_nhdsWithin.mp hU
    have hV : V ∈ nhds z := hVo.mem_nhds hzV
    obtain ⟨w, ⟨hwV, hwS⟩, hwz⟩ := hzacc V hV
    exact ⟨w, hVU ⟨hwV, hwz⟩, hwS⟩
  have h2 := hiso z
  obtain ⟨w, hw1, hw2⟩ := (h1.and_eventually h2).exists
  exact hw2 hw1.1

lemma deux_zeros_reels_of_hHardy (hHardy : HardyTheorem) :
    ∃ a b : ℂ, a ≠ b ∧ XiRiemann a = 0 ∧
    XiRiemann b = 0 ∧ a.im = 0 ∧ b.im = 0 := by
  unfold HardyTheorem at hHardy
  obtain ⟨s, hs, t, ht, hst⟩ : ∃ s ∈ zerosCritiques, ∃ t ∈ zerosCritiques, s ≠ t := by
    obtain ⟨s, hs⟩ := hHardy.nonempty
    obtain ⟨t, ht, hts⟩ := (hHardy.sdiff (Set.finite_singleton s)).nonempty
    exact ⟨s, hs, t, ht, fun h => hts (by rw [h]; rfl)⟩
  obtain ⟨a, ha_im, ha0, ha⟩ := zeroCritique_to_Xi s hs
  obtain ⟨b, hb_im, hb0, hb⟩ := zeroCritique_to_Xi t ht
  refine ⟨a, b, ?_, ha0, hb0, ha_im, hb_im⟩
  intro hab
  apply hst
  rw [← ha, ← hb, hab]

lemma newton_im_eq_zero_of_perm (γ : ℕ → ℂ) (m : ℕ → ℕ) (n k : ℕ)
    (σ : ℕ → ℕ)
    (hσ_mem : ∀ j ∈ Finset.Icc 1 n, σ j ∈ Finset.Icc 1 n)
    (hσ_inj : Set.InjOn σ (Finset.Icc 1 n))
    (hγ : ∀ j ∈ Finset.Icc 1 n, γ (σ j) = (starRingEnd ℂ) (γ j))
    (hm : ∀ j ∈ Finset.Icc 1 n, m (σ j) = m j) :
    (newton γ m n k).im = 0 := by
  have himg : (Finset.Icc 1 n).image σ = Finset.Icc 1 n := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact hσ_mem j hj
    · rw [Finset.card_image_of_injOn hσ_inj]
  have hconj : (starRingEnd ℂ) (newton γ m n k) = newton γ m n k := by
    unfold newton
    rw [map_sum]
    have hterm : ∀ j ∈ Finset.Icc 1 n,
        (starRingEnd ℂ) ((m j : ℂ) * γ j ^ k) = (m (σ j) : ℂ) * γ (σ j) ^ k := by
      intro j hj
      rw [map_mul, map_pow, hm j hj, hγ j hj]
      simp
    rw [Finset.sum_congr rfl hterm]
    have hsum := Finset.sum_image (f := fun x => (m x : ℂ) * γ x ^ k) hσ_inj
    rw [himg] at hsum
    exact hsum.symm
  have := congrArg Complex.im hconj
  simp at this
  linarith


open InducRiemannZero


lemma hankel_rang_of_reels
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration XiRiemann γ m)
    (n : ℕ) (_ : 2 ≤ n)
    (hreal : ∀ j, 1 ≤ j → j ≤ n → (γ j).im = 0) :
    (∀ k, k ≤ 2 * n - 1 → (newton γ m n k).im = 0) ∧
    (∀ r, 1 ≤ r → r ≤ n → 0 < (Delta γ m n r).re ∧
    (Delta γ m n r).im = 0) := by
  refine ⟨fun k _ => newton_im_zero γ m n k hreal, ?_⟩
  intro r hr1 hrn
  refine Delta_pos_of_real γ m n r hr1 hrn ?_ hreal ?_
  · intro j hj
    exact henum.mult_pos j (Finset.mem_Icc.mp hj).1
  · intro i hi j hj hij
    exact henum.injective i j (Finset.mem_Icc.mp hi).1 (Finset.mem_Icc.mp hj).1 hij


open ZeroMin2


lemma deux_plus_petits_zeros_reels
    (a b : ℂ)
    (ha : XiRiemann a = 0) (hb : XiRiemann b = 0) (hba : b ≠ a)
    (hamin' : ∀ z : ℂ, XiRiemann z = 0 → ‖a‖ ≤ ‖z‖)
    (hbmin' : ∀ z : ℂ, XiRiemann z = 0 → z ≠ a → ‖b‖ ≤ ‖z‖)
    (hpaliers : PaliersStrictsXiRiemann) :
    a.im = 0 ∧ b.im = 0 := by
  have hsym : ∀ w, xiDecale (-(starRingEnd ℂ) w) = (starRingEnd ℂ) (xiDecale w) :=
    xiDecale_symm_conj'
  have h_zeta_real : ∀ x : ℝ, 0 < x → x < 1 → riemannZeta (x : ℂ) ≠ 0 := by
    intro x hx0 hx1
    exact riemannZeta_ne_zero_of_mem_Ioo_real x hx0 hx1
  have hre_ne : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z.re ≠ 0 :=
    fun z hz _ => XiRiemann_zero_re_ne_zero h_zeta_real z hz
  have ha_re : a.re ≠ 0 := hre_ne a ha rfl
  have ha0 : a ≠ 0 := fun h0 => ha_re (by simp [h0])
  have hdeux_cercle : ∀ z : ℂ, XiRiemann z = 0 → ‖z‖ = ‖a‖ → z = a ∨ z = -a := by
    apply hdeux_cercle_of_spectre_minimal a ha_re ![1, 1] (by intro j; fin_cases j <;> decide)
    intro z hz hnorm
    exact selection_spectrale_cercle_minimal
      a ha hamin' ha_re z hz hnorm hpaliers
  exact deux_plus_petits_zeros_reels_of_cercle_minimal
    a b ha hb hba hamin' hbmin' hsym hre_ne hdeux_cercle

lemma DeuxPremiersZerosReels_of_hHardy (hHardy : HardyTheorem)
  (hpaliers : PaliersStrictsXiRiemann) :
    DeuxPremiersZerosReels := by
  obtain ⟨a₀, b₀, hab₀, ha₀, hb₀, ha₀im, hb₀im⟩ := deux_zeros_reels_of_hHardy hHardy
  set Z : Set ℂ := {z : ℂ | XiRiemann z = 0} with hZ
  have hfin_a : {z : ℂ | XiRiemann z = 0 ∧ ‖z‖ ≤ ‖a₀‖}.Finite :=
    zeros_Xi_bornes_finis ‖a₀‖
  have hne_a : {z : ℂ | XiRiemann z = 0 ∧ ‖z‖ ≤ ‖a₀‖}.Nonempty :=
    ⟨a₀, ha₀, le_refl _⟩
  obtain ⟨a, ⟨ha, haR⟩, hamin⟩ := Set.exists_min_image _ (fun z : ℂ => ‖z‖) hfin_a hne_a
  have hamin' : ∀ z : ℂ, XiRiemann z = 0 → ‖a‖ ≤ ‖z‖ := by
    intro z hz
    by_cases hzle : ‖z‖ ≤ ‖a₀‖
    · exact hamin z ⟨hz, hzle⟩
    · push Not at hzle
      exact le_trans haR hzle.le
  obtain ⟨c, hc, hca⟩ : ∃ c : ℂ, XiRiemann c = 0 ∧ c ≠ a := by
    by_cases h : a₀ = a
    · exact ⟨b₀, hb₀, fun h' => hab₀ (h.trans h'.symm)⟩
    · exact ⟨a₀, ha₀, h⟩
  have hfin_b : {z : ℂ | XiRiemann z = 0 ∧ z ≠ a ∧ ‖z‖ ≤ ‖c‖}.Finite :=
    (zeros_Xi_bornes_finis ‖c‖).subset (fun z hz => ⟨hz.1, hz.2.2⟩)
  have hne_b : {z : ℂ | XiRiemann z = 0 ∧ z ≠ a ∧ ‖z‖ ≤ ‖c‖}.Nonempty :=
    ⟨c, hc, hca, le_refl _⟩
  obtain ⟨b, ⟨hb, hba, hbR⟩, hbmin⟩ :=
    Set.exists_min_image _ (fun z : ℂ => ‖z‖) hfin_b hne_b
  have hbmin' : ∀ z : ℂ, XiRiemann z = 0 → z ≠ a → ‖b‖ ≤ ‖z‖ := by
    intro z hz hza
    by_cases hzle : ‖z‖ ≤ ‖c‖
    · exact hbmin z ⟨hz, hza, hzle⟩
    · push Not at hzle
      exact le_trans hbR hzle.le
  have hab_im : a.im = 0 ∧ b.im = 0 :=
    deux_plus_petits_zeros_reels a b ha hb hba hamin' hbmin' hpaliers
  refine ⟨a, b, hba.symm, ha, hb, hab_im.1, hab_im.2, hamin' b hb, ?_⟩
  intro z hz hza hzb
  exact hbmin' z hz hza

theorem Riemann_Hypothesis_hPos_hPaliers (hHardy : HardyTheorem)
    (hPaliers : PaliersStrictsXiRiemann)
    (hpos : ∀ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m → HankelPositive γ m) :
    RiemannHypothesis := by
  have hDeux : DeuxPremiersZerosReels :=
    DeuxPremiersZerosReels_of_hHardy hHardy hPaliers
  obtain ⟨γ, m, henum, hfirst⟩ :=
    exists_zeroEnumeration_XiRiemann_first hHardy hDeux hPaliers
  have hconj : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → ConjugueSuit γ m n₀ := by
    intro n₀ h3 hne hreal
    obtain ⟨hc, hmm⟩ := hfirst n₀ h3 hne hreal
    exact ⟨hc, hmm⟩
  have hprop : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → PropagationDefaut γ n₀ :=
    propagation_of_enum γ m hHardy henum hDeux (hpos γ m henum) hconj
  exact hypothesys_of_Riemann_conditional γ m henum hHardy hconj hprop

open RiemannObtentionHyp

lemma newton_real_of_conj_stable (γ : ℕ → ℂ) (m : ℕ → ℕ) (n k : ℕ)
    (hstab : ∃ σ : ℕ → ℕ,
      (∀ j ∈ Finset.Icc 1 n, σ j ∈ Finset.Icc 1 n) ∧
      Set.InjOn σ (Finset.Icc 1 n) ∧
      (∀ j ∈ Finset.Icc 1 n, γ (σ j) = (starRingEnd ℂ) (γ j)) ∧
      (∀ j ∈ Finset.Icc 1 n, m (σ j) = m j)) :
    (newton γ m n k).im = 0 := by
  obtain ⟨σ, hσ_mem, hσ_inj, hγ, hm⟩ := hstab
  exact newton_im_eq_zero_of_perm γ m n k σ hσ_mem hσ_inj hγ hm

open hPosRiemann


open BrainrotLemma_Riemann in
theorem hankelPositive_of_hardy'
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hcompat : ConjCompatible γ m)
    (hconj : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n)
    (hHardy : HardyTheorem) :
    HankelPositive γ m := by
  refine hankelPositive_of_all_real γ m hEnum ?_
  by_contra hcon
  push Not at hcon
  classical
  have hex : ∃ k, 1 ≤ k ∧ (γ k).im ≠ 0 := hcon
  obtain ⟨n₀, hn₀, hmin⟩ : ∃ n₀, (1 ≤ n₀ ∧ (γ n₀).im ≠ 0) ∧
      ∀ j, j < n₀ → ¬ (1 ≤ j ∧ (γ j).im ≠ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hreal_before : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0 := by
    intro j hj1 hjlt
    by_contra hne
    exact hmin j hjlt ⟨hj1, hne⟩
  have hn₀3 : 3 ≤ n₀ := by
    by_contra hlt
    push Not at hlt
    have h12 : n₀ = 1 ∨ n₀ = 2 := by omega
    rcases h12 with h1 | h2
    · exact hn₀.2 (h1 ▸ hEnum.real_one)
    · exact hn₀.2 (h2 ▸ hEnum.real_two)
  obtain ⟨hconj_n, hmult_n⟩ := hconj n₀ hn₀3 hn₀.2 hreal_before
  have hpalier : PalierCritique γ m n₀ :=
    { n0_ge       := hn₀3
      reels_avant := hreal_before
      non_reel    := hn₀.2
      conj_zero   := hconj_n
      mult_pos    := fun j hj1 _ => hEnum.mult_pos j hj1
      mult_conj   := hmult_n
      injectif    := fun i j hi _ hj _ hij => hEnum.injective i j hi hj hij }
  have hbrain := brainrot_Lemma XiRiemann XiRiemann_conj_forall γ m hEnum n₀ hpalier
  obtain ⟨_, ⟨_, hDelta_neg, hDelta_im, _⟩, hprop, _⟩ := hbrain
  have hinf := hardy_gives_infinite_real_indices γ m hEnum hHardy
  have hprop_def : ∀ N, n₀ ≤ N → (γ N).im ≠ 0 :=
    propagation_defaut γ m hcompat n₀ hpalier
  have hfin : {k : ℕ | 1 ≤ k ∧ (γ k).im = 0}.Finite := by
    apply (Set.finite_lt_nat n₀).subset
    intro k hk
    obtain ⟨hk1, hkim⟩ := hk
    rw [Set.mem_ofPred_eq]
    by_contra hge
    rw [not_lt] at hge
    exact hprop_def k hge hkim
  exact hinf hfin


lemma conjCompatible_all_real
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hinj : ∀ i j, 1 ≤ i → 1 ≤ j → γ i = γ j → i = j)
    (hcompat : ConjCompatible γ m) :
    ∀ n, 3 ≤ n → (γ n).im = 0 := by
  intro n hn
  by_contra hne
  have h1 : γ (n + 1) = starRingEnd ℂ (γ n) := hcompat.conj_next n hn hne
  have hne1 : (γ (n + 1)).im ≠ 0 := by
    rw [h1, Complex.conj_im]
    exact neg_ne_zero.mpr hne
  have h2 : γ (n + 1 + 1) = starRingEnd ℂ (γ (n + 1)) :=
    hcompat.conj_next (n + 1) (by omega) hne1
  have h3 : γ (n + 1 + 1) = γ n := by
    rw [h2, h1, Complex.conj_conj]
  have := hinj (n + 1 + 1) n (by omega) (by omega) h3
  omega

lemma palier_paire_non_reelle
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (n₀ : ℕ)
    (hpalier : PalierCritique γ m n₀) :
    (γ n₀).im ≠ 0 ∧ (γ (n₀ + 1)).im ≠ 0 := by
  refine ⟨hpalier.non_reel, ?_⟩
  rw [hpalier.conj_zero, Complex.conj_im]
  exact neg_ne_zero.mpr hpalier.non_reel

open BrainrotLemma_Riemann in
lemma delta_nonpos_base
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (hEnum : ZeroEnumeration XiRiemann γ m)
    (n₀ : ℕ) (hpalier : PalierCritique γ m n₀) :
    (Delta γ m (n₀ + 1) (n₀ + 1)).re ≤ 0 := by
  have hbrain := brainrot_Lemma XiRiemann XiRiemann_conj_forall γ m hEnum n₀ hpalier
  obtain ⟨_, ⟨_, hneg, _, _⟩, _, _⟩ := hbrain
  exact hneg.le


lemma propagation_defaut'
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (_ : ZeroEnumeration XiRiemann γ m)
    (hcompat' : ConjCompatible' γ m)
    (n₀ : ℕ) (hpalier : PalierCritique γ m n₀)
    (hdeg : ∀ n, n₀ ≤ n → 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = starRingEnd ℂ (γ n) → (γ (n + 1)).im ≠ 0) :
    PropagationDefaut γ n₀ := by
  have key : ∀ k, (γ (n₀ + k)).im ≠ 0 := by
    intro k
    induction k with
    | zero =>
      simpa using hpalier.non_reel
    | succ k ih =>
      have hn : 3 ≤ n₀ + k := le_trans hpalier.n0_ge
        (Nat.le_add_right _ _)
      by_cases hprev : γ (n₀ + k - 1) = starRingEnd ℂ (γ (n₀ + k))
      · have := hdeg (n₀ + k) (Nat.le_add_right _ _) hn ih hprev
        rw [show n₀ + (k + 1) = n₀ + k + 1 by ring]
        exact this
      · obtain ⟨hconj, _⟩ := hcompat'.conj_next (n₀ + k) hn ih hprev
        rw [show n₀ + (k + 1) = n₀ + k + 1 by ring, hconj]
        simpa [Complex.conj_im] using ih
  intro N hN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  exact key k


open EndRiemannProof



lemma ordreSpectral_all_real (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hall : ∀ k, 1 ≤ k → (γ k).im = 0) :
    OrdreSpectralIntraPalier γ m := {
  paire_ouverte := by
    intro n₀ n hn₀ hn₀n hnon₀ hreels heven hnon
    exfalso
    exact hnon (hall n (by omega))
  paire_fermee := by
    intro n₀ n hn₀ hn₀n hnon₀ hreels hodd hnon
    exfalso
    exact hnon (hall n (by omega))
  pas_reel_apres_paire := by
    intro n hn hnon hprev
    exfalso
    exact hnon (hall n (by omega))
}


lemma ordreSpectral_of_align
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hAlign : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ = gammaAlign γ n ∧ m = mAlign m n) :
    OrdreSpectralIntraPalier γ m := by
  classical
  by_cases hex : ∃ k, 1 ≤ k ∧ (γ k).im ≠ 0
  · obtain ⟨n₀, hn₀, hmin⟩ : ∃ n₀, (1 ≤ n₀ ∧ (γ n₀).im ≠ 0) ∧
        ∀ j, j < n₀ → ¬ (1 ≤ j ∧ (γ j).im ≠ 0) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
    have hreal_before : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0 := by
      intro j hj1 hjlt
      by_contra hne
      exact hmin j hjlt ⟨hj1, hne⟩
    have hn₀3 : 3 ≤ n₀ := by
      by_contra hlt
      push Not at hlt
      have h12 : n₀ = 1 ∨ n₀ = 2 := by omega
      rcases h12 with h1 | h2
      · exact hn₀.2 (h1 ▸ hEnum.real_one)
      · exact hn₀.2 (h2 ▸ hEnum.real_two)
    obtain ⟨hγ, hm⟩ := hAlign n₀ hn₀3 hn₀.2 hreal_before
    rw [hγ, hm]
    exact ordreSpectralIntraPalier_gammaAlign γ m n₀
  · push Not at hex
    exact ordreSpectral_all_real γ m hex

lemma ordreSpectral_of_enum_conj
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hAlign : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ = gammaAlign γ n ∧ m = mAlign m n) :
    OrdreSpectralIntraPalier γ m :=
  ordreSpectral_of_align γ m hEnum hAlign


lemma even_zero' : Even (0 : ℕ) :=
  ⟨0, rfl⟩

lemma hconj_of_align
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hAlign : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ = gammaAlign γ n ∧ m = mAlign m n) :
    ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
      γ (n + 1) = starRingEnd ℂ (γ n) ∧ m (n + 1) = m n := by
  intro n hn3 hne hreels
  have hOrdre : OrdreSpectralIntraPalier γ m :=
    ordreSpectral_of_enum_conj γ m hEnum hAlign
  have heven : Even (n - n) := by
    rw [Nat.sub_self]
    exact even_zero'
  have hpo := hOrdre.paire_ouverte n n hn3 (le_refl n) hne hreels heven hne
  exact ⟨hpo.1, hpo.2.1⟩

lemma conjCompat'_of_first
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hAlign : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ = gammaAlign γ n ∧ m = mAlign m n) :
    ConjCompatible' γ m := by
  have hOrdre : OrdreSpectralIntraPalier γ m :=
    ordreSpectral_of_enum_conj γ m hEnum hAlign
  have hconj := hconj_of_align γ m hEnum hAlign
  exact conjCompat'_of_first_preproof γ m hEnum hOrdre hconj

lemma Propagation_DegenereProof_sans_hPos
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hOrdre : OrdreSpectralIntraPalier γ m)
    (n₀ : ℕ) :
    ∀ n, n₀ ≤ n → 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = starRingEnd ℂ (γ n) → (γ (n + 1)).im ≠ 0 := by
  intro n _ hn3 hne hprev
  exact hOrdre.pas_reel_apres_paire n hn3 hne hprev


lemma Propagation_DegenereProof
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hOrdre : OrdreSpectralIntraPalier γ m)
    (n₀ : ℕ) :
    ∀ n, n₀ ≤ n → 3 ≤ n → (γ n).im ≠ 0 →
      γ (n - 1) = starRingEnd ℂ (γ n) → (γ (n + 1)).im ≠ 0 :=
  Propagation_DegenereProof_sans_hPos γ m hOrdre n₀


lemma exists_perm_conjCompat
    {γ₀ : ℕ → ℂ} {m₀ : ℕ → ℕ}
    (hEnum₀ : ZeroEnumeration XiRiemann γ₀ m₀)
    (hPermAlign : ∃ σ : Equiv.Perm ℕ,
      (∀ n < 3, σ n = n) ∧
      (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
      (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
        (γ₀ ∘ σ) = gammaAlign (γ₀ ∘ σ) n ∧
        (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n)) :
    ∃ σ : Equiv.Perm ℕ,
      (∀ n < 3, σ n = n) ∧
      (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
      OrdreSpectralIntraPalier (γ₀ ∘ σ) (m₀ ∘ σ) ∧
      ConjCompatible' (γ₀ ∘ σ) (m₀ ∘ σ) := by
  rcases hPermAlign with ⟨σ, hfix, hnorm, hAlignσ⟩
  have hEnumσ : ZeroEnumeration XiRiemann (γ₀ ∘ σ) (m₀ ∘ σ) :=
    PermZeroEnumerationMemeModule hEnum₀ σ hfix hnorm
  have hOrdreσ : OrdreSpectralIntraPalier (γ₀ ∘ σ) (m₀ ∘ σ) :=
    ordreSpectral_of_enum_conj (γ₀ ∘ σ) (m₀ ∘ σ) hEnumσ hAlignσ
  have hCompatσ : ConjCompatible' (γ₀ ∘ σ) (m₀ ∘ σ) :=
    conjCompat'_of_first (γ₀ ∘ σ) (m₀ ∘ σ) hEnumσ hAlignσ
  exact ⟨σ, hfix, hnorm, hOrdreσ, hCompatσ⟩


theorem exists_zeroEnumeration_XiRiemann_compat_of_perm'
    {γ₀ : ℕ → ℂ} {m₀ : ℕ → ℕ}
    (hEnum₀ : ZeroEnumeration XiRiemann γ₀ m₀)
    (σ : Equiv.Perm ℕ)
    (hfix : ∀ n < 3, σ n = n)
    (hnorm : ∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖)
    (hOrdreσ : OrdreSpectralIntraPalier (γ₀ ∘ σ) (m₀ ∘ σ))
    (hCompatσ : ConjCompatible' (γ₀ ∘ σ) (m₀ ∘ σ)) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧
      OrdreSpectralIntraPalier γ m ∧
      ConjCompatible' γ m ∧
      (∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n) := by
  have hEnumσ : ZeroEnumeration XiRiemann (γ₀ ∘ σ) (m₀ ∘ σ) :=
    PermZeroEnumerationMemeModule hEnum₀ σ hfix hnorm
  refine ⟨γ₀ ∘ σ, m₀ ∘ σ, hEnumσ, hOrdreσ, hCompatσ, ?_⟩
  exact ConjCompatImpliqueHypothesePremierNonReel hEnumσ hCompatσ

theorem hankelPositive_of_hardy''
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hOrdre : OrdreSpectralIntraPalier γ m)
    (hcompat' : ConjCompatible' γ m)
    (hconj : ∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n)
    (hHardy : HardyTheorem) :
    HankelPositive γ m := by
  refine hankelPositive_of_all_real γ m hEnum ?_
  by_contra hcon
  push Not at hcon
  classical
  have hex : ∃ k, 1 ≤ k ∧ (γ k).im ≠ 0 := hcon
  obtain ⟨n₀, hn₀, hmin⟩ : ∃ n₀, (1 ≤ n₀ ∧ (γ n₀).im ≠ 0) ∧
      ∀ j, j < n₀ → ¬ (1 ≤ j ∧ (γ j).im ≠ 0) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hreal_before : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0 := by
    intro j hj1 hjlt
    by_contra hne
    exact hmin j hjlt ⟨hj1, hne⟩
  have hn₀3 : 3 ≤ n₀ := by
    by_contra hlt
    push Not at hlt
    have h12 : n₀ = 1 ∨ n₀ = 2 := by omega
    rcases h12 with h1 | h2
    · exact hn₀.2 (h1 ▸ hEnum.real_one)
    · exact hn₀.2 (h2 ▸ hEnum.real_two)
  obtain ⟨hconj_n, hmult_n⟩ := hconj n₀ hn₀3 hn₀.2 hreal_before
  have hpalier : PalierCritique γ m n₀ :=
    { n0_ge       := hn₀3
      reels_avant := hreal_before
      non_reel    := hn₀.2
      conj_zero   := hconj_n
      mult_pos    := fun j hj1 _ => hEnum.mult_pos j hj1
      mult_conj   := hmult_n
      injectif    := fun i j hi _ hj _ hij => hEnum.injective i j hi hj hij }
  have hinf := hardy_gives_infinite_real_indices γ m hEnum hHardy
  have hprop_def : ∀ N, n₀ ≤ N → (γ N).im ≠ 0 :=
    propagation_defaut' γ m hEnum hcompat' n₀ hpalier
      (Propagation_DegenereProof γ m hOrdre n₀)
  have hfin : {k : ℕ | 1 ≤ k ∧ (γ k).im = 0}.Finite := by
    apply (Set.finite_lt_nat n₀).subset
    intro k hk
    obtain ⟨hk1, hkim⟩ := hk
    rw [Set.mem_ofPred_eq]
    by_contra hge
    rw [not_lt] at hge
    exact hprop_def k hge hkim
  exact hinf hfin

lemma exists_zeroEnumeration_XiRiemann_compat
    (hHardy : HardyTheorem) (hDeux : DeuxPremiersZerosReels)
    (hPaliers : PaliersStrictsXiRiemann)
    (hAlignPerm : ∀ (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ₀ m₀ →
      ∃ σ : Equiv.Perm ℕ,
        (∀ n < 3, σ n = n) ∧
        (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
        (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
          (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
          (γ₀ ∘ σ) = gammaAlign (γ₀ ∘ σ) n ∧
          (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n)) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧
      OrdreSpectralIntraPalier γ m ∧
      ConjCompatible' γ m ∧
      (∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n) := by
  obtain ⟨γ₀, m₀, hEnum₀⟩ := exists_zeroEnumeration_XiRiemann hHardy hDeux hPaliers
  obtain ⟨σ, hfix, hnorm, hOrdreσ, hCompatσ⟩ :=
    exists_perm_conjCompat hEnum₀ (hAlignPerm γ₀ m₀ hEnum₀)
  exact exists_zeroEnumeration_XiRiemann_compat_of_perm' hEnum₀
    σ hfix hnorm hOrdreσ hCompatσ

lemma hPosProof_hDeux
    (hHardy : HardyTheorem)
    (hDeux : DeuxPremiersZerosReels)
    (hPaliers : PaliersStrictsXiRiemann)
    (hAlignPerm : ∀ (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ₀ m₀ →
      ∃ σ : Equiv.Perm ℕ,
        (∀ n < 3, σ n = n) ∧
        (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
        (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
          (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
          (γ₀ ∘ σ) = gammaAlign (γ₀ ∘ σ) n ∧
          (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n)) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧
      HankelPositive γ m := by
  obtain ⟨γ, m, hEnum, hOrdre, hcompat', hconj⟩ :=
    exists_zeroEnumeration_XiRiemann_compat hHardy hDeux hPaliers hAlignPerm
  refine ⟨γ, m, hEnum, ?_⟩
  exact hankelPositive_of_hardy'' γ m hEnum hOrdre hcompat' hconj hHardy

theorem Riemann_Hypothesis_hPosEx (hHardy : HardyTheorem)
    (hPaliers : PaliersStrictsXiRiemann)
    (hpos : ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧ HankelPositive γ m ∧
      (∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → ConjugueSuit γ m n₀)) :
    RiemannHypothesis := by
  have hDeux : DeuxPremiersZerosReels :=
    DeuxPremiersZerosReels_of_hHardy hHardy hPaliers
  obtain ⟨γ, m, henum, hpos', hconj⟩ := hpos
  have hprop : ∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → PropagationDefaut γ n₀ :=
    propagation_of_enum γ m hHardy henum hDeux hpos' hconj
  exact hypothesys_of_Riemann_conditional γ m henum hHardy hconj hprop

lemma hPosExists
    (hHardy : HardyTheorem) (hDeux : DeuxPremiersZerosReels)
    (hPaliers : PaliersStrictsXiRiemann)
    (hAlignPerm : ∀ (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ₀ m₀ →
      ∃ σ : Equiv.Perm ℕ,
        (∀ n < 3, σ n = n) ∧
        (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
        (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
          (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
          (γ₀ ∘ σ) = gammaAlign (γ₀ ∘ σ) n ∧
          (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n)) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧ HankelPositive γ m ∧
      (∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → ConjugueSuit γ m n₀) := by
  obtain ⟨γ, m, hEnum, hOrdre, hcompat', hconj⟩ :=
    exists_zeroEnumeration_XiRiemann_compat hHardy hDeux hPaliers hAlignPerm
  refine ⟨γ, m, hEnum,
    hankelPositive_of_hardy'' γ m hEnum hOrdre hcompat' hconj hHardy, ?_⟩
  intro n₀ h3 hne hreal
  obtain ⟨hc, hmm⟩ := hconj n₀ h3 hne hreal
  exact ⟨hc, hmm⟩

lemma ordreSpectral_of_all_real (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hall : ∀ k, 1 ≤ k → (γ k).im = 0) :
    OrdreSpectralIntraPalier γ m := {
  paire_ouverte := by
    intro n₀ n hn₀ hn₀n hnon₀ hreels heven hnon
    have h_zero : (γ n).im = 0 := hall n (by omega)
    exact False.elim (hnon h_zero)
  paire_fermee := by
    intro n₀ n hn₀ hn₀n hnon₀ hreels hodd hnon
    have h_zero : (γ n).im = 0 := hall n (by omega)
    exact False.elim (hnon h_zero)
  pas_reel_apres_paire := by
    intro n hn hnon hprev
    have h_zero : (γ n).im = 0 := hall n (by omega)
    exact False.elim (hnon h_zero)
}

lemma conjCompatible'_of_all_real (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hall : ∀ k, 1 ≤ k → (γ k).im = 0) :
    ConjCompatible' γ m := by
  refine ⟨?_⟩
  intro n hn him hprev
  have : (γ n).im = 0 := hall n (by omega)
  exact (him this).elim

lemma cas_non_reel_contradiction
    (hHardy : HardyTheorem)
    (γ₁ : ℕ → ℂ) (m₁ : ℕ → ℕ)
    (hEnum₁ : ZeroEnumeration XiRiemann γ₁ m₁)
    (hconj₁ : ∀ n, 3 ≤ n → (γ₁ n).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n → (γ₁ j).im = 0) →
      γ₁ (n + 1) = (starRingEnd ℂ) (γ₁ n) ∧ m₁ (n + 1) = m₁ n)
    (hPos₁ : HankelPositive γ₁ m₁)
    (hex : ∃ n, 3 ≤ n ∧ (γ₁ n).im ≠ 0)
    (hPaliers : PaliersStrictsXiRiemann) :
    False := by
  classical
  have hDeux : DeuxPremiersZerosReels :=
    DeuxPremiersZerosReels_of_hHardy hHardy hPaliers
  have hConjSuit₁ : ∀ n₀, 3 ≤ n₀ → (γ₁ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ₁ j).im = 0) → ConjugueSuit γ₁ m₁ n₀ := by
    intro n₀ hn₀3 hne hreal
    obtain ⟨hc, hmm⟩ := hconj₁ n₀ hn₀3 hne hreal
    exact ⟨hc, hmm⟩
  have hprop : ∀ n₀, 3 ≤ n₀ → (γ₁ n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ₁ j).im = 0) → PropagationDefaut γ₁ n₀ :=
    propagation_of_enum γ₁ m₁ hHardy hEnum₁ hDeux hPos₁ hConjSuit₁
  let n₀ := Nat.find hex
  have hn₀_spec : 3 ≤ n₀ ∧ (γ₁ n₀).im ≠ 0 := Nat.find_spec hex
  have hn₀3 : 3 ≤ n₀ := hn₀_spec.1
  have hn₀_im : (γ₁ n₀).im ≠ 0 := hn₀_spec.2
  have hreal : ∀ j, 1 ≤ j → j < n₀ → (γ₁ j).im = 0 := by
    intro j hj1 hjn₀
    by_cases hj3 : 3 ≤ j
    · by_contra hne
      exact Nat.find_min hex hjn₀ ⟨hj3, hne⟩
    · have : j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl
      · exact hEnum₁.real_one
      · exact hEnum₁.real_two
  have hprop_def : ∀ n, n₀ ≤ n → (γ₁ n).im ≠ 0 :=
    hprop n₀ hn₀3 hn₀_im hreal
  have hinf := hardy_gives_infinite_real_indices γ₁ m₁ hEnum₁ hHardy
  have hfin : {k : ℕ | 1 ≤ k ∧ (γ₁ k).im = 0}.Finite := by
    apply (Set.finite_lt_nat n₀).subset
    intro k hk
    obtain ⟨hk1, hkim⟩ := hk
    rw [Set.mem_ofPred_eq]
    by_contra hge
    rw [not_lt] at hge
    exact hprop_def k hge hkim
  exact hinf hfin

lemma im_ne_zero_of_ge_first_nonreal
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hOrdre : OrdreSpectralIntraPalier γ m)
    (n₀ : ℕ) (hn₀3 : 3 ≤ n₀) (hn₀ : (γ n₀).im ≠ 0)
    (hmin : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) :
    ∀ k : ℕ, (γ (n₀ + k)).im ≠ 0 := by
  intro k
  refine Nat.strongRecOn k (fun k ih => ?_)
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · by_cases hk0 : k = 0
    · simpa [hk0] using hn₀
    · obtain ⟨r, hr⟩ := hk_even
      have hr1 : 1 ≤ r := by omega
      have hk_pred_odd : Odd ((n₀ + (k - 1)) - n₀) := by
        have : (n₀ + (k - 1)) - n₀ = 2 * (r - 1) + 1 := by omega
        rw [this]
        exact ⟨r - 1, rfl⟩
      have h_im_pred : (γ (n₀ + (k - 1))).im ≠ 0 := ih (k - 1) (by omega)
      have h_fermee : γ ((n₀ + (k - 1)) - 1) = (starRingEnd ℂ) (γ (n₀ + (k - 1))) :=
        hOrdre.paire_fermee n₀ (n₀ + (k - 1)) hn₀3 (by omega) hn₀ hmin hk_pred_odd h_im_pred
      have h_pas_reel : (γ ((n₀ + (k - 1)) + 1)).im ≠ 0 :=
        hOrdre.pas_reel_apres_paire (n₀ + (k - 1)) (by omega) h_im_pred h_fermee
      have h_eq : (n₀ + (k - 1)) + 1 = n₀ + k := by omega
      rwa [h_eq] at h_pas_reel
  · obtain ⟨r, hr⟩ := hk_odd
    have hk_pred_even : Even ((n₀ + (k - 1)) - n₀) := by
      have : (n₀ + (k - 1)) - n₀ = r + r := by omega
      rw [this]
      exact ⟨r, rfl⟩
    have h_im_pred : (γ (n₀ + (k - 1))).im ≠ 0 := ih (k - 1) (by omega)
    have h_ouverte :=
      (hOrdre.paire_ouverte n₀ (n₀ + (k - 1)) hn₀3 (by omega) hn₀ hmin hk_pred_even h_im_pred).1
    have h_eq : (n₀ + (k - 1)) + 1 = n₀ + k := by omega
    rw [h_eq] at h_ouverte
    rw [h_ouverte, Complex.conj_im, neg_ne_zero]
    exact h_im_pred


lemma norm_le_of_le
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) :
    ‖γ i‖ ≤ ‖γ j‖ :=
  hEnum.mono_norm i j hi hij


lemma all_real_of_ordreSpectral_and_hardy
    (hHardy : HardyTheorem)
    (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hOrdre : OrdreSpectralIntraPalier γ m) :
    ∀ n, 1 ≤ n → (γ n).im = 0 := by
  classical
  by_contra hNotAll
  push Not at hNotAll
  have hex3 : ∃ n, 3 ≤ n ∧ (γ n).im ≠ 0 := by
    rcases hNotAll with ⟨n, hn1, hne⟩
    refine ⟨n, ?_, hne⟩
    by_contra hn3
    have : n = 1 ∨ n = 2 := by omega
    rcases this with rfl | rfl
    · exact hne hEnum.real_one
    · exact hne hEnum.real_two
  let n₀ := Nat.find hex3
  have hn₀_spec : 3 ≤ n₀ ∧ (γ n₀).im ≠ 0 := Nat.find_spec hex3
  have hn₀3 : 3 ≤ n₀ := hn₀_spec.1
  have hn₀_im : (γ n₀).im ≠ 0 := hn₀_spec.2
  have hmin : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0 := by
    intro j hj1 hjn₀
    by_cases hj3 : 3 ≤ j
    · by_contra hne
      exact Nat.find_min hex3 hjn₀ ⟨hj3, hne⟩
    · have : j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl
      · exact hEnum.real_one
      · exact hEnum.real_two
  have h_nonreal_ge : ∀ n, n₀ ≤ n → (γ n).im ≠ 0 := by
    intro n hn
    have h_eq : n = n₀ + (n - n₀) := by omega
    rw [h_eq]
    exact im_ne_zero_of_ge_first_nonreal γ m hOrdre n₀ hn₀3 hn₀_im hmin (n - n₀)
  have hinf := hardy_gives_infinite_real_indices γ m hEnum hHardy
  have hfin : {k : ℕ | 1 ≤ k ∧ (γ k).im = 0}.Finite := by
    apply (Set.finite_lt_nat n₀).subset
    intro k hk
    obtain ⟨hk1, hkim⟩ := hk
    rw [Set.mem_ofPred_eq]
    by_contra hge
    rw [not_lt] at hge
    exact h_nonreal_ge k hge hkim
  exact hinf hfin

lemma exists_zeroEnumeration_XiRiemann_compat'_pos_case
    (hHardy : HardyTheorem)
    (γ₁ : ℕ → ℂ) (m₁ : ℕ → ℕ)
    (hEnum₁ : ZeroEnumeration XiRiemann γ₁ m₁)
    (hconj₁ : ∀ n, 3 ≤ n → (γ₁ n).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n → (γ₁ j).im = 0) →
      γ₁ (n + 1) = (starRingEnd ℂ) (γ₁ n) ∧ m₁ (n + 1) = m₁ n)
    (hPos₁ : HankelPositive γ₁ m₁)
    (hex : ∃ n, 3 ≤ n ∧ (γ₁ n).im ≠ 0)
    (hPaliers : PaliersStrictsXiRiemann) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧
      OrdreSpectralIntraPalier γ m ∧
      ConjCompatible' γ m ∧
      (∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n) := by
  exfalso
  exact cas_non_reel_contradiction
    hHardy γ₁ m₁ hEnum₁ hconj₁ hPos₁ hex hPaliers

lemma pred_ne_conj_of_first_nonreal
    (γ : ℕ → ℂ) (n₀ : ℕ) (hn₀3 : 3 ≤ n₀)
    (hn₀_im : (γ n₀).im ≠ 0)
    (hreal : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) :
    γ (n₀ - 1) ≠ (starRingEnd ℂ) (γ n₀) := by
  intro h_eq
  have h_pred_ge : 1 ≤ n₀ - 1 := by omega
  have h_pred_lt : n₀ - 1 < n₀ := by omega
  have h_pred_real : (γ (n₀ - 1)).im = 0 := hreal (n₀ - 1) h_pred_ge h_pred_lt
  have h_conj_im : ((starRingEnd ℂ) (γ n₀)).im = - (γ n₀).im := Complex.conj_im (γ n₀)
  have h_im_eq : (γ (n₀ - 1)).im = ((starRingEnd ℂ) (γ n₀)).im := by rw [h_eq]
  rw [h_pred_real, h_conj_im] at h_im_eq
  have h_im_zero : (γ n₀).im = 0 := by
    linarith [h_im_eq]
  exact hn₀_im h_im_zero

lemma eq_first_nonreal_of_minimal
    (γ : ℕ → ℂ) (n₀ n₁ : ℕ)
    (hn₀3 : 3 ≤ n₀) (hn₀_im : (γ n₀).im ≠ 0)
    (hreal₀ : ∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0)
    (hn₁3 : 3 ≤ n₁) (hn₁_im : (γ n₁).im ≠ 0)
    (hmin₁ : ∀ j, 1 ≤ j → j < n₁ → (γ j).im = 0) :
    n₁ = n₀ := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : 1 ≤ n₁ := by omega
    exact hn₁_im (hreal₀ n₁ h1 hlt)
  · have h1 : 1 ≤ n₀ := by omega
    exact hn₀_im (hmin₁ n₀ h1 hgt)

lemma extraction_enumeration_canonique_sans_hankel
    (hHardy : HardyTheorem)
    (hChoice : CanonicalZeroEnumerationExists) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧
      (∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        ((∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
          γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n) ∧
        (γ (n + 1)).im ≠ 0) := by
  have _ := DeuxPremiersZerosReels_of_hHardy hHardy
  obtain ⟨γ, m, hEnum, hconj⟩ := hChoice
  exact ⟨γ, m, hEnum, hconj⟩

lemma propagationDefaut_of_ordreSpectral
    (γ₁ : ℕ → ℂ) (m₁ : ℕ → ℕ)
    (hOrdre : OrdreSpectralIntraPalier γ₁ m₁)
    (n₀ : ℕ) (hn₀3 : 3 ≤ n₀) (hn₀_im : (γ₁ n₀).im ≠ 0)
    (hreal : ∀ j, 1 ≤ j → j < n₀ → (γ₁ j).im = 0) :
    PropagationDefaut γ₁ n₀ := by
  intro N hN
  have hN_eq : N = n₀ + (N - n₀) := by omega
  rw [hN_eq]
  exact im_ne_zero_of_ge_first_nonreal
    γ₁ m₁ hOrdre n₀ hn₀3 hn₀_im hreal (N - n₀)

lemma cas_non_reel_sans_hankel
    (hHardy : HardyTheorem)
    (γ₁ : ℕ → ℂ) (m₁ : ℕ → ℕ)
    (hEnum₁ : ZeroEnumeration XiRiemann γ₁ m₁)
    (hOrdre₁ : OrdreSpectralIntraPalier γ₁ m₁)
    (hconj₁ : ∀ n, 3 ≤ n → (γ₁ n).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n → (γ₁ j).im = 0) →
      γ₁ (n + 1) = (starRingEnd ℂ) (γ₁ n) ∧ m₁ (n + 1) = m₁ n)
    (hex : ∃ n, 3 ≤ n ∧ (γ₁ n).im ≠ 0) :
    False := by
  classical
  let n₀ := Nat.find hex
  have hn₀_spec : 3 ≤ n₀ ∧ (γ₁ n₀).im ≠ 0 := Nat.find_spec hex
  have hn₀3 : 3 ≤ n₀ := hn₀_spec.1
  have hn₀_im : (γ₁ n₀).im ≠ 0 := hn₀_spec.2
  have hreal : ∀ j, 1 ≤ j → j < n₀ → (γ₁ j).im = 0 := by
    intro j hj1 hjn₀
    by_cases hj3 : 3 ≤ j
    · by_contra hne
      exact Nat.find_min hex hjn₀ ⟨hj3, hne⟩
    · have hj12 : j = 1 ∨ j = 2 := by omega
      rcases hj12 with rfl | rfl
      · exact hEnum₁.real_one
      · exact hEnum₁.real_two
  have hConjSuit₁ : ConjugueSuit γ₁ m₁ n₀ := by
    obtain ⟨hc, hm⟩ := hconj₁ n₀ hn₀3 hn₀_im hreal
    exact ⟨hc, hm⟩
  have hinf : Set.Infinite {k : ℕ | 1 ≤ k ∧ (γ₁ k).im = 0} :=
    hardy_gives_infinite_real_indices γ₁ m₁ hEnum₁ hHardy
  have hprop_all : PropagationDefaut γ₁ n₀ :=
    propagationDefaut_of_ordreSpectral γ₁ m₁ hOrdre₁ n₀ hn₀3 hn₀_im hreal
  have hsubset : {k : ℕ | 1 ≤ k ∧ (γ₁ k).im = 0} ⊆ Finset.range n₀ := by
    intro k hk
    simp only [Set.mem_ofPred_eq] at hk
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra! hge
    have hkn₀ : n₀ ≤ k := hge
    rcases eq_or_lt_of_le hkn₀ with rfl | hlt
    · exact hn₀_im hk.2
    · have hconj_im : (γ₁ (n₀ + 1)).im ≠ 0 := by
        have hc := hConjSuit₁.1
        intro h0
        apply hn₀_im
        have hc_im : (γ₁ (n₀ + 1)).im = - (γ₁ n₀).im := by
          rw [hc]
          exact Complex.conj_im (γ₁ n₀)
        rw [h0] at hc_im
        have h_neg_zero : - (γ₁ n₀).im = 0 := hc_im.symm
        exact neg_eq_zero.mp h_neg_zero
      by_cases hk_succ : k = n₀ + 1
      · subst hk_succ
        exact hconj_im hk.2
      · have hk_ge2 : n₀ + 2 ≤ k := by omega
        obtain ⟨hc, hm⟩ := hConjSuit₁
        have h_conj_im : (γ₁ (n₀ + 1)).im = -(γ₁ n₀).im := by
          rw [hc]
          rfl
        have hk_im : (γ₁ k).im = 0 := hk.2
        have hk_ne_zero : (γ₁ k).im ≠ 0 := hprop_all k hkn₀
        exact hk_ne_zero hk_im
  have hfin : ({k : ℕ | 1 ≤ k ∧ (γ₁ k).im = 0} : Set ℕ).Finite :=
    Finset.finite_toSet (Finset.range n₀) |>.subset hsubset
  exact hinf hfin



lemma exists_zeroEnumeration_XiRiemann_compat'
    (hHardy : HardyTheorem) (hDeux : DeuxPremiersZerosReels)
    (hPaliers : PaliersStrictsXiRiemann)
    (hAlignPerm : ∀ (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ₀ m₀ →
      ∃ σ : Equiv.Perm ℕ,
        (∀ n < 3, σ n = n) ∧
        (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
        (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
          (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
          (γ₀ ∘ σ) = gammaAlign (γ₀ ∘ σ) n ∧
          (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n)) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧
      OrdreSpectralIntraPalier γ m ∧
      ConjCompatible' γ m ∧
      (∀ n, 3 ≤ n → (γ n).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n → (γ j).im = 0) →
        γ (n + 1) = (starRingEnd ℂ) (γ n) ∧ m (n + 1) = m n) := by
  exact exists_zeroEnumeration_XiRiemann_compat hHardy hDeux hPaliers hAlignPerm

lemma hPosExists'
    (hHardy : HardyTheorem) (hDeux : DeuxPremiersZerosReels)
    (hPaliers : PaliersStrictsXiRiemann)
    (hAlignPerm : ∀ (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ₀ m₀ →
      ∃ σ : Equiv.Perm ℕ,
        (∀ n < 3, σ n = n) ∧
        (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
        (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
          (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
          (γ₀ ∘ σ) = gammaAlign (γ₀ ∘ σ) n ∧
          (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n)) :
    ∃ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m ∧ HankelPositive γ m ∧
      (∀ n₀, 3 ≤ n₀ → (γ n₀).im ≠ 0 →
        (∀ j, 1 ≤ j → j < n₀ → (γ j).im = 0) → ConjugueSuit γ m n₀) := by
  obtain ⟨γ, m, hEnum, hOrdre, hcompat', hconj⟩ :=
    exists_zeroEnumeration_XiRiemann_compat' hHardy hDeux hPaliers hAlignPerm
  refine ⟨γ, m, hEnum,
    hankelPositive_of_hardy'' γ m hEnum hOrdre hcompat' hconj hHardy, ?_⟩
  intro n₀ h3 hne hreal
  obtain ⟨hc, hmm⟩ := hconj n₀ h3 hne hreal
  exact ⟨hc, hmm⟩


theorem Riemann_Hypothesis_hDeux
    (hHardy : HardyTheorem)
    (hDeux : DeuxPremiersZerosReels)
    (hPaliers : PaliersStrictsXiRiemann)
    (hAlignPerm : ∀ (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ₀ m₀ →
      ∃ σ : Equiv.Perm ℕ,
        (∀ n < 3, σ n = n) ∧
        (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
        (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
          (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
          (γ₀ ∘ σ) = gammaAlign (γ₀ ∘ σ) n ∧
          (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n)) :
    RiemannHypothesis :=
  Riemann_Hypothesis_hPosEx hHardy hPaliers
    (hPosExists' hHardy hDeux hPaliers hAlignPerm)

theorem Riemann_Hypothesis_hGeom (hHardy : HardyTheorem)
    (hGeom : HypotheseGeometrieSpectraleXi) :
    RiemannHypothesis := by
  obtain ⟨hPaliers, hAlignPerm⟩ := hGeom
  have hDeux : DeuxPremiersZerosReels :=
    DeuxPremiersZerosReels_of_hHardy hHardy hPaliers
  exact Riemann_Hypothesis_hDeux hHardy hDeux hPaliers hAlignPerm

theorem Riemann_Hypothesis_hpalier_hAlign (hHardy : HardyTheorem)
    (hPaliers : PaliersStrictsXiRiemann)
    (hAlignPerm : ∀ (γ₀ : ℕ → ℂ) (m₀ : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ₀ m₀ →
      ∃ σ : Equiv.Perm ℕ,
        (∀ n < 3, σ n = n) ∧
        (∀ n, 1 ≤ n → ‖γ₀ (σ n)‖ = ‖γ₀ n‖) ∧
        (∀ n, 3 ≤ n → ((γ₀ ∘ σ) n).im ≠ 0 →
          (∀ j, 1 ≤ j → j < n → ((γ₀ ∘ σ) j).im = 0) →
          (γ₀ ∘ σ) = gammaAlign (γ₀ ∘ σ) n ∧
          (m₀ ∘ σ) = mAlign (m₀ ∘ σ) n)) :
    RiemannHypothesis :=
  Riemann_Hypothesis_hGeom hHardy ⟨hPaliers, hAlignPerm⟩

lemma XiRiemann_neg_conj (z : ℂ) (hz : XiRiemann z = 0) :
    XiRiemann (-(starRingEnd ℂ) z) = 0 := by
  rw [XiRiemann_neg]
  rw [XiRiemann_conj_symm]
  rw [XiRiemann_neg]
  rw [hz]
  exact map_zero (starRingEnd ℂ)

lemma exists_neg_conj_index
    {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration XiRiemann γ m) (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, γ k = -(starRingEnd ℂ) (γ n) := by
  have hzero : XiRiemann (γ n) = 0 := hEnum.zero_mem n hn
  have h_symm_zero : XiRiemann (-(starRingEnd ℂ) (γ n)) = 0 := by
    rw [XiRiemann_neg]
    rw [XiRiemann_conj_symm]
    rw [XiRiemann_neg]
    rw [hzero]
    exact map_zero (starRingEnd ℂ)
  obtain ⟨k, _, hk_eq⟩ := hEnum.exhaustive (-(starRingEnd ℂ) (γ n)) h_symm_zero
  exact ⟨k, hk_eq⟩


lemma exists_neg_conj_index_all_of_eq_zero
    {γ : ℕ → ℂ} {m : ℕ → ℕ}
    (hEnum : ZeroEnumeration XiRiemann γ m)
    (hγ0 : γ 0 = γ 1) (n : ℕ) :
    ∃ k, γ k = -(starRingEnd ℂ) (γ n) := by
  by_cases hn : 1 ≤ n
  · exact exists_neg_conj_index hEnum n hn
  · have hn0 : n = 0 := by omega
    subst hn0
    obtain ⟨k, hk⟩ := exists_neg_conj_index hEnum 1 (by omega)
    refine ⟨k, ?_⟩
    rw [hγ0]
    exact hk

lemma neg_conj_mem_LambdaZeros {γ : ℂ} (hγ : γ ∈ LambdaZeros) :
    -(starRingEnd ℂ) γ ∈ LambdaZeros := by
  simp only [LambdaZeros, Set.mem_ofPred_eq] at hγ ⊢
  have h : (1 / 2 : ℂ) + Complex.I * (-(starRingEnd ℂ) γ)
      = (starRingEnd ℂ) (1 / 2 + Complex.I * γ) := by
    rw [map_add, map_mul, Complex.conj_I, map_div₀, map_one, map_ofNat]
    ring
  rw [h]
  rw [xiEntiere_conj, hγ]
  exact map_zero _

lemma hsym_enum_of_range
    (f : ℕ → ℂ)
    (hfrange : Set.range f = LambdaZeros)
    (_ : Function.Injective f) :
    ∀ n, 1 ≤ n → ∃ k, 1 ≤ k ∧
      (fun i => f (i - 1)) k = -(starRingEnd ℂ) ((fun i => f (i - 1)) n) := by
  intro n hn
  have hmem : f (n - 1) ∈ LambdaZeros := by
    rw [← hfrange]
    exact Set.mem_range_self (n - 1)
  have hmem' : -(starRingEnd ℂ) (f (n - 1)) ∈ LambdaZeros :=
    neg_conj_mem_LambdaZeros hmem
  rw [← hfrange] at hmem'
  obtain ⟨m, hm⟩ := hmem'
  refine ⟨m + 1, Nat.le_add_left 1 m, ?_⟩
  simp only [Nat.add_sub_cancel]
  exact hm

theorem Riemann_Hypothesis_hPos (hHardy : HardyTheorem)
    (hGeom : HypotheseGeometrieSpectraleXi)
    (_ : ∀ (γ : ℕ → ℂ) (m : ℕ → ℕ),
      ZeroEnumeration XiRiemann γ m → HankelPositive γ m) :
    RiemannHypothesis := by
  have hPaliers : PaliersStrictsXiRiemann := hGeom.paliers_stricts
  have hDeux : DeuxPremiersZerosReels :=
  DeuxPremiersZerosReels_of_hHardy hHardy hPaliers
  have hinf : LambdaZeros.Infinite := lambdaZeros_infinite hHardy
  obtain ⟨f, hfinj, hfrange, hfmono, hf0, hf1⟩ :=
    exists_enum_with_two_real hDeux hinf
  let γ_init : ℕ → ℂ := fun n => f (n - 1)
  let m_init : ℕ → ℕ := fun _ => 1
  have hEnum : ZeroEnumeration XiRiemann γ_init m_init := by
    refine
      { zero_mem := ?_,
        injective := ?_,
        exhaustive := ?_,
        mono_norm := ?_,
        palier_strict := ?_,
        mult_pos := ?_,
        real_one := ?_,
        real_two := ?_,
        conj_mult := ?_ }
    · intro n _
      have hmem : f (n - 1) ∈ LambdaZeros := by
        rw [← hfrange]
        exact Set.mem_range_self (n - 1)
      exact (mem_LambdaZeros_iff (f (n - 1))).1 hmem
    · intro i j hi hj heq
      dsimp [γ_init] at heq
      have := hfinj heq
      omega
    · intro z hz
      have hzΛ : z ∈ LambdaZeros := (mem_LambdaZeros_iff z).2 hz
      rw [← hfrange] at hzΛ
      obtain ⟨k, rfl⟩ := hzΛ
      refine ⟨k + 1, by omega, ?_⟩
      dsimp [γ_init]
    · intro i j hi hij
      dsimp [γ_init]
      exact hfmono (i - 1) (j - 1) (by omega)
    · intro n hn hnorm
      exact palier_strict_of_inj hPaliers γ_init
        (fun k _ => by
          have hmem : f (k - 1) ∈ LambdaZeros := by
            rw [← hfrange]
            exact Set.mem_range_self (k - 1)
          exact (mem_LambdaZeros_iff (f (k - 1))).1 hmem)
        (fun i j hi hj heq => by
          dsimp [γ_init] at heq
          have := hfinj heq
          omega)
        n hn hnorm
    · intro _ _
      exact le_rfl
    · dsimp [γ_init]
      exact hf0
    · dsimp [γ_init]
      exact hf1
    · intro _ _ _ _ _
      rfl
  have hγ0 : γ_init 0 = γ_init 1 := rfl
  have hsym : ∀ n, 1 ≤ n → ∃ k, 1 ≤ k ∧
      γ_init k = -(starRingEnd ℂ) (γ_init n) :=
    hsym_enum_of_range f hfrange hfinj
  have hOrdre : OrdreSpectralIntraPalier γ_init m_init :=
    ordre_spectral_de_enumeration γ_init m_init hEnum hsym
  have hconj : ∀ n₀, 3 ≤ n₀ → (γ_init n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ_init j).im = 0) → ConjugueSuit γ_init m_init n₀ := by
    intro n₀ h3 hne hreal
    have h0 := hOrdre.paire_ouverte n₀ n₀ h3 le_rfl hne hreal (by simp) hne
    exact ⟨h0.1, h0.2.1⟩
  have hprop : ∀ n₀, 3 ≤ n₀ → (γ_init n₀).im ≠ 0 →
      (∀ j, 1 ≤ j → j < n₀ → (γ_init j).im = 0) → PropagationDefaut γ_init n₀ :=
    propagationDefaut_of_ordreSpectral γ_init m_init hOrdre
  exact hypothesys_of_Riemann_conditional γ_init m_init hEnum hHardy hconj hprop



/-!
# Mathematical Commentary on the Hypotheses of `Riemann_Hypothesis_hPos`
# Commentaire Mathématique sur les Hypothèses de `Riemann_Hypothesis_hPos`

================================================================================
ENGLISH VERSION
================================================================================

### 1. Conceptual role of the two geometric hypotheses
The combined hypothesis structure `HypotheseGeometrieSpectraleXi` (or the pair
formed by `hPaliers : PaliersStrictsXiRiemann` and `hAlignPerm`) encapsulates two
structural constraints on the zero set of `XiRiemann`:
1. `PaliersStrictsXiRiemann`: Two distinct zeros sharing the same Euclidean norm
   must be complex conjugates ($z_1 = \overline{z_2}$), implying that each level
   set $\{\, z \in \mathbb{C} : \Xi(z) = 0 \text{ and } \|z\| = R \,\}$ contains
   at most two elements.
2. `hAlignPerm`: Any admissible zero enumeration $(\gamma_0, m_0)$ can be
   reordered via an index permutation $\sigma \in \mathfrak{S}(\mathbb{N})$ that
   preserves the norms ($\|\gamma_0(\sigma(n))\| = \|\gamma_0(n)\|$) and fixes the
   initial real zeros ($\sigma(n) = n$ for $n < 3$), such that the resulting
   sequence coincides with the canonical block alignment (`gammaAlign`, `mAlign`).

### 2. Derivation from zeta properties, Hardy's theorem, and Choice
- **Initial real zeros**: By Hardy's theorem (`hHardy : HardyTheorem`, Hardy 1914),
  $\Xi_{\mathrm{Riemann}}$ has infinitely many real zeros on the critical axis.
  Assuming the Axiom of Choice (`Classical.choice` via `Set.Infinite.natEmbedding`),
  one can always extract an infinite injective sequence of zeros ordered by non-decreasing
  norms, whose first two elements are strictly real ($f(0), f(1) \in \mathbb{R}$,
  represented by `DeuxPremiersZerosReels`).
- **Matrix construction and uniqueness**: As established in the spectral Hankel
  construction (cf. `RiemannProof.tex`, sections on bordered Hankel determinants and
  Newton sums), the sequence of zeros reconstructed through consecutive orthogonal
  spectral extensions is uniquely determined up to index permutation between conjugate
  pairs within each constant-modulus tier. The assumption `hAlignPerm` merely ensures
  that one operates with this canonical sequence: it groups any non-real zero directly
  with its complex conjugate in consecutive ranks ($n_0$ and $n_0 + 1$) with matching
  multiplicities, preserving the underlying Hankel matrix identities.

### 3. Dilemma: Lean formalization versus circularity
In practice, these two assumptions represent either:
- A benign normalisation property (essentially a choice of canonical representative
  modulo permutation of conjugate pairs); or
- A substantial gap in Lean requiring an induction over indices. If one relaxes
  `ZeroEnumeration` to remove the strict modulus-step condition (`palier_strict`),
  the resulting enumeration predicate becomes too weak for Lean to establish the
  spectral ordering (`OrdreSpectralIntraPalier`).
Without a structural condition linking consecutive ranks of the enumeration, one is
forced back into the global hypothesis `hpos`
(`∀ γ m, ZeroEnumeration Xi γ m → HankelPositive γ m`).
However, as demonstrated in Proposition `pr:critere-global-hankel-riemann` of `RiemannProof.tex`,
the global positive definiteness of all Hankel matrices is mathematically equivalent to
the Riemann Hypothesis itself. Thus, assuming `hpos` across all weak enumerations without
rank-by-rank inductive control renders the deduction circular. The role of `hAlignPerm`
and `paliers_stricts` is precisely to provide the exact bridge allowing the induction
to propagate the Hankel defect step-by-step from the first non-real zero.

### 4. Eligibility for the Riemann Hypothesis status
- **Mathematical eligibility**: The statement constitutes a valid conditional reduction:
  "Under Hardy's theorem, spectral Hankel positivity, and canonical tier alignment,
  the Riemann Hypothesis holds."
- **Status in Lean**: Because `PaliersStrictsXiRiemann` is an explicit open hypothesis
  (or left as `sorry` in `obtention_hypothesis`) and because `HardyTheorem` is asserted
  without proof, this theorem does not yet constitute an unconditional Lean proof of the
  Riemann Hypothesis. To achieve full formal certification, Lean requires:
  (a) A formal proof of Hardy's theorem in Mathlib;
  (b) A constructive proof that the modulus-equivalence classes on `LambdaZeros`
      admit a reordering into `gammaAlign` and `mAlign` without postulating `hAlignPerm`;
  (c) Either an unconditional proof of `PaliersStrictsXiRiemann`, or an overhaul of
      `ZeroEnumeration` that handles tiers of arbitrary finite cardinality.

================================================================================
VERSION FRANÇAISE
================================================================================

### 1. Rôle conceptuel des deux hypothèses géométriques
La structure d'hypothèse unifiée `HypotheseGeometrieSpectraleXi` (ou le couple
formé de `hPaliers : PaliersStrictsXiRiemann` et `hAlignPerm`) formalise deux
contraintes structurelles sur l'ensemble des zéros de `XiRiemann` :
1. `PaliersStrictsXiRiemann` : Deux zéros distincts ayant la même norme euclidienne
   sont nécessairement conjugués ($z_1 = \overline{z_2}$), ce qui implique que chaque
   palier de module $\{\, z \in \mathbb{C} : \Xi(z) = 0 \text{ et } \|z\| = R \,\}$
   contient au plus deux zéros.
2. `hAlignPerm` : Toute énumération admissible $(\gamma_0, m_0)$ peut être réordonnée
   par une permutation d'indices $\sigma \in \mathfrak{S}(\mathbb{N})$ préservant les
   normes ($\|\gamma_0(\sigma(n))\| = \|\gamma_0(n)\|$) et fixant les zéros réels
   initiaux ($\sigma(n) = n$ pour $n < 3$), de sorte que la suite réordonnée coïncide
   exactement avec l'alignement canonique par blocs (`gammaAlign`, `mAlign`).

### 2. Déduction à partir des propriétés de zêta, du théorème de Hardy et du Choix
- **Zéros réels initiaux** : En vertu du théorème de Hardy (`hHardy : HardyTheorem`,
  Hardy 1914), la fonction $\Xi_{\mathrm{Riemann}}$ possède une infinité de zéros réels.
  En admettant l'axiome du choix (`Classical.choice` via `Set.Infinite.natEmbedding`),
  on peut toujours extraire une énumération infinie injective ordonnée selon les normes
  croissantes et dont les deux premiers termes sont strictement réels
  ($f(0), f(1) \in \mathbb{R}$, matérialisés par `DeuxPremiersZerosReels`).
- **Construction matricielle et unicité** : Comme établi dans la construction spectrale
  de Hankel (cf. `RiemannProof.tex`, sections sur les bordages de Hankel et les sommes de
  Newton), la suite des zéros reconstructible par extensions spectrales orthogonales
  successives est unique à permutation près des indices entre zéros conjugués au sein
  de chaque palier de même module. L'hypothèse `hAlignPerm` ne sert ainsi qu'à garantir
  que l'on travaille effectivement avec cette suite canonique : elle apparie immédiatement
  tout zéro non réel avec son conjugué aux rangs consécutifs ($n_0$ et $n_0 + 1$) avec
  la même multiplicité, préservant la validité des déterminants de Hankel bordés.

### 3. Dilemme : formalisation Lean versus circularité logique
Dans la pratique, ces deux hypothèses représentent :
- Soit une propriété de normalisation anodine (un choix de représentant canonique à
  permutation de conjugués près) ;
- Soit une difficulté technique majeure dans Lean demandant une récurrence fine sur
  les indices. Si l'on affaiblit la définition de `ZeroEnumeration` pour supprimer la
  condition de saut de norme tous les deux termes (`palier_strict`), la suite obtenue
  possède des hypothèses de construction trop faibles pour que Lean puisse en déduire
  l'ordre spectral (`OrdreSpectralIntraPalier`).
Sans hypothèse structurelle contraignant les rangs successifs de l'énumération, on se
retrouve ramené au cadre de l'hypothèse globale `hpos`
(`∀ γ m, ZeroEnumeration Xi γ m → HankelPositive γ m`).
Or, d'après la proposition `pr:critere-global-hankel-riemann` de `RiemannProof.tex`,
la positivité globale de Hankel à chaque étape d'épuisement est mathématiquement
équivalente à l'Hypothèse de Riemann elle-même. Dès lors, supposer `hpos` sans contrôle
du rang d'énumération rend la démarche circulaire. Les hypothèses `hAlignPerm` et
`paliers_stricts` sont précisément le verrou technique qui permet de briser cette
circularité en autorisant une propagation récurrente locale du défaut de positivité.

### 4. Éligibilité vis-à-vis de l'Hypothèse de Riemann
- **Éligibilité mathématique** : La formulation constitue une réduction conditionnelle
  suffisante : « Sous le théorème de Hardy, la positivité de Hankel et l'alignement
  canonique des paliers spectraux, l'Hypothèse de Riemann est vraie. »
- **Nécessité de complétion dans Lean** : Tant que `PaliersStrictsXiRiemann` figure
  en prémisse non démontrée (ou en `sorry` dans `obtention_hypothesis`) et que
  `HardyTheorem` n'est pas démontré à partir des axiomes de Mathlib, le fichier ne
  fournit pas une preuve close et inconditionnelle de l'Hypothèse de Riemann.
  Une certification complète dans Lean requiert :
  (a) La formalisation complète du théorème de Hardy ;
  (b) La démonstration constructive de l'existence de la permutation $\sigma$
      alignant les paliers finis sur `gammaAlign` sans postuler `hAlignPerm` ;
  (c) La démonstration inconditionnelle de `PaliersStrictsXiRiemann`, ou la
      généralisation de `ZeroEnumeration` aux paliers de multiplicité géométrique
      arbitraire.
-/




/-
theorem Riemann_Hypothesis (hHardy : HardyTheorem) :
    RiemannHypothesis := by
  sorry
-/





end RiemannHypProof
