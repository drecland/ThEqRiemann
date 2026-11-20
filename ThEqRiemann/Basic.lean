/-
Copyright (c) 2026 Drecland (Côte Léandre Bernard) . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Drecland (Côte Léandre Bernard)
-/
import mathlib
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.EquationnaryTheorem
import ThEqRiemann.EqTheorem.ObservableAnalytiqueSelection
import ThEqRiemann.EqTheorem.SpectrumInversion
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.IntResTheorem
import ThEqRiemann.RiemannProof.RiemannDefinition
import ThEqRiemann.RiemannProof.InductionRiemannZero
import ThEqRiemann.RiemannProof.BrainrotLemma
import ThEqRiemann.RiemannProof.RiemannHypothesisProof

/-!  -/
namespace BasicThEqRiemann

open Set Complex ThEq DefinitionsThEq

theorem equationary_theorem_for_basic
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y₀ : ℂ)
    (lamFun : ℂ → Fin K → ℂ) (w : ℂ → Fin K → ℤ)
    (hlam : ∀ y, Function.Injective (lamFun y))
    (hw : ∀ y r, w y r ≠ 0)
    (hmom : ∀ y k, momentsParametres C γΩ g y k =
      ∑ r : Fin K, (w y r : ℂ) * (lamFun y r) ^ k)
    (lamLim : Fin K → ℂ)
    (hlim : Filter.Tendsto lamFun
        (nhdsWithin y₀ {y₀}ᶜ) (nhds lamLim))
    (Pf : Set ℂ) (hPf : Set.range lamLim = Pf) :
    (∀ y : ℂ,
      IsUnit (hankel0Dynamique K C γΩ g y) ∧
      spectrum ℂ ((hankel0Dynamique K C γΩ g y)⁻¹ *
      hankel1Dynamique K C γΩ g y)
        = Set.range (lamFun y)) ∧
    (∃ Mlim : Matrix (Fin K) (Fin K) ℂ,
      Filter.Tendsto
        (fun y => (hankel0Dynamique K C γΩ g y)⁻¹ *
        hankel1Dynamique K C γΩ g y)
        (nhdsWithin y₀ {y₀}ᶜ) (nhds Mlim) ∧
      spectrum ℂ Mlim = Pf) := by
  exact equationary_theorem K C γΩ g y₀
    lamFun w hlam hw hmom lamLim hlim Pf hPf

open ObservableSelectionTheorem

theorem selection_spectrale_for_basic
    {K M : ℕ} (az : Fin K → ℂ) (ap : Fin M → ℂ)
    (m : Fin K → ℕ) (d : Fin M → ℕ)
    (hm : ∀ j, 0 < m j) (hd : ∀ l, 0 < d l)
    (hdist : Function.Injective (Sum.elim az ap)) :
    let lam : Fin (K + M) → ℂ := Sum.elim az ap ∘ finSumFinEquiv.symm
    let w : Fin (K + M) → ℤ :=
      Sum.elim (fun j => (m j : ℤ)) (fun l => -(d l : ℤ)) ∘ finSumFinEquiv.symm
    IsUnit (hankel0 lam w).det ∧
    spectrum ℂ (operateurM lam w) = Set.range az ∪ Set.range ap := by
  exact selection_spectrale az ap m d hm hd hdist

theorem recherche_zeros_observable_for_basic
    {K M : ℕ} (az : Fin K → ℂ) (ap : Fin M → ℂ)
    (m : Fin K → ℕ) (d : Fin M → ℕ)
    (hm : ∀ j, 0 < m j) (hd : ∀ l, 0 < d l)
    (hdist : Function.Injective (Sum.elim az ap)) :
    let lam : Fin (K + M) → ℂ := Sum.elim az ap ∘ finSumFinEquiv.symm
    let w : Fin (K + M) → ℤ :=
      Sum.elim (fun j => (m j : ℤ)) (fun l => -(d l : ℤ)) ∘ finSumFinEquiv.symm
    IsUnit (hankel0 lam w).det ∧
    spectrum ℂ (operateurM lam w) = Set.range az ∪ Set.range ap ∧
    (∀ i, 0 < w i ↔ lam i ∈ Set.range az) := by
  exact recherche_zeros_observable az ap m d hm hd hdist

open SpecInversion

theorem inversion_spectrale_meromorphe_for_basic
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ)
    (lamFun : ℂ → Fin K → ℂ) (w : ℂ → Fin K → ℤ)
    (hlam : ∀ y, Function.Injective (lamFun y))
    (hw : ∀ y r, w y r ≠ 0)
    (hmom : ∀ y k, momentsParametres C γΩ g y k
              = ∑ r : Fin K, (w y r : ℂ) * (lamFun y r) ^ k)
    (hsol : ∀ y, Set.range (lamFun y) =
      ensembleSolutions C.f C.Ω (g y)) :
    ∀ y : ℂ,
      IsUnit (hankel0Dynamique K C γΩ g y) ∧
      spectrum ℂ ((hankel0Dynamique K C γΩ g y)⁻¹ *
        hankel1Dynamique K C γΩ g y)
        = ensembleSolutions C.f C.Ω (g y) := by
  apply inversion_spectrale_meromorphe K C γΩ g
    lamFun w hlam hw hmom hsol


open ResIntTheorem Module End ResDef

variable {V : Type*} [AddCommGroup V]
  [Module ℂ V] [FiniteDimensional ℂ V]


theorem resolution_integrale_for_basic (T : End ℂ V) :
    -- (1)
    (∑ μ ∈ spec T, mT T μ = Module.finrank ℂ V) ∧
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]
        (f : ℂ → E) (e : Fin (spec T).card ≃ spec T),
      (∀ n ≥ (spec T).card, partialSum T f e n = resInt T f) ∧
      Filter.Tendsto (partialSum T f e) Filter.atTop (nhds (resInt T f)) ∧
      (∀ e' : Fin (spec T).card ≃ spec T,
        partialSum T f e (spec T).card = partialSum T f e' (spec T).card)) ∧
    -- (2)
    (∀ f : ℂ → ℂ,
      (pf T f).degree < (spec T).card ∧
      (∀ μ ∈ spec T, (pf T f).eval μ = f μ) ∧
      (∀ q : Polynomial ℂ, q.degree < (spec T).card →
        (∀ μ ∈ spec T, q.eval μ = f μ) → q = pf T f) ∧
      LinearMap.trace ℂ V (Polynomial.aeval T (pf T f)) = resInt T f) ∧
    -- (4)
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E),
      ‖resInt T f‖ ≤ ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ∧
      (∀ C : ℝ, (∀ μ ∈ spec T, ‖f μ‖ ≤ C) →
        ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ≤
          (Module.finrank ℂ V : ℝ) * C)) ∧
    -- (5)
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]
        (W : Submodule ℂ E) (f : ℂ → E), (∀ μ ∈ spec T, f μ ∈ W) →
      resInt T f ∈ W ∧ Metric.infDist (resInt T f) (W : Set E) = 0) ∧
    -- (6)
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E],
      Val T (Set.univ : Set E) =
        {x | ∃ v : ℂ → E, x = ∑ μ ∈ spec T, mT T μ • v μ}) ∧
    (∀ {E : Type _} [NormedAddCommGroup E]
      [NormedSpace ℂ E] (W : Submodule ℂ E),
      Val T (W : Set E) = {x | ∃ w : ℂ → E, (∀ μ ∈ spec T, w μ ∈ W) ∧
        x = ∑ μ ∈ spec T, mT T μ • w μ} ∧ Val T (W : Set E) ⊆ W) :=
  resolution_integrale_complet T

theorem resolution_integrale_residus_for_basic
    (T : End ℂ V) (f F : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hspec : ∀ μ ∈ spec T, μ ∈ Metric.ball c R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall c R))
    (hFf : ∀ μ ∈ spec T, F μ = f μ) :
    (1 / (2 * Real.pi * Complex.I)) *
      (∮ z in C(c, R), F z * LinearMap.trace ℂ V
        (Ring.inverse ((algebraMap ℂ (End ℂ V) z) - T)))
        = resInt T f :=
  resolution_integrale_residus T f F c R hR hspec hF hFf


open RiemannDef InducRiemannZero Matrix Polynomial


theorem induction_zeros_hankel_riemann_for_basic
    (Xi : ℂ → ℂ) (γ : ℕ → ℂ) (m : ℕ → ℕ)
    (henum : ZeroEnumeration Xi γ m) :
    -- (1) inversibility and diagonalisation
    (∀ n, 2 ≤ n →
      IsUnit (Hn γ m n).det ∧
      Delta γ m n n =
        (∏ j ∈ Finset.Icc 1 n, (m j : ℂ)) *
          ∏ i ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 n,
            (if i < j then (γ j - γ i) ^ 2 else 1) ∧
      Delta γ m n n ≠ 0 ∧
      IsUnit (Vn γ n).det ∧
      Vn γ n * Cn γ m n * (Vn γ n)⁻¹ = Dn' γ n) ∧
    -- (2) initialisation on the second rank
    ((∀ k, (newton γ m 2 k).im = 0) ∧
      0 < (Delta γ m 2 1).re ∧ (Delta γ m 2 1).im = 0 ∧
      Delta γ m 2 1 = (m 1 : ℂ) + (m 2 : ℂ) ∧
      Delta γ m 2 2 = (m 1 : ℂ) * (m 2 : ℂ) * (γ 2 - γ 1) ^ 2 ∧
      0 < (Delta γ m 2 2).re ∧ (Delta γ m 2 2).im = 0 ∧
      (Hn γ m 2).IsHermitian) ∧
    -- (3) transition and DefPos
    (∀ n, 3 ≤ n → (∀ j, 1 ≤ j → j ≤ n - 1 → (γ j).im = 0) →
      (∀ r, 1 ≤ r → r ≤ n - 1 → 0 < (Delta γ m (n - 1) r).re ∧
        (Delta γ m (n - 1) r).im = 0) ∧
      Delta γ m n n =
        (m n : ℂ) * Delta γ m (n - 1) (n - 1) *
          ∏ j ∈ Finset.Icc 1 (n - 1), (γ n - γ j) ^ 2 ∧
      ((γ n).im = 0 ↔
        ((∀ k, k ≤ 2 * n - 1 → (newton γ m n k).im = 0) ∧
          0 < (Schur γ m n).re ∧ (Schur γ m n).im = 0 ∧
          Schur γ m n = Delta γ m n n / Delta γ m n (n - 1) ∧
          (∀ r, 1 ≤ r → r ≤ n - 1 → 0 < (Delta γ m n r).re ∧ (Delta γ m n r).im = 0)))) ∧
    -- (4) explicite caracterisation of γ_n and conclusion of Re(s_n)
    (∀ n, 2 ≤ n →
      γ n = (Cn γ m n).trace - ∑ j ∈ Finset.Icc 1 (n - 1), γ j ∧
      γ n = (newton γ m n 1 - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ) * γ j) /
            (newton γ m n 0 - ∑ j ∈ Finset.Icc 1 (n - 1), (m j : ℂ)) ∧
      PiPoly γ m n = (X - C (γ n)) * ∏ j ∈ Finset.Icc 1 (n - 1), (X - C (γ j)) ∧
      (∀ z : ℂ, (PiPoly γ m n).eval z = 0 → z ≠ γ n →
        ∃ j, 1 ≤ j ∧ j ≤ n - 1 ∧ z = γ j)) ∧
    (HankelPositive γ m →
      ∀ n, 1 ≤ n → ((1 : ℂ) / 2 + Complex.I * γ n).re = 1 / 2) :=
  recurrence_zeros_hankel_riemann Xi γ m henum


open BrainrotLemma_Riemann ComplexConjugate


theorem brainrot_Lemma_for_basic
    (Xi : ℂ → ℂ) (hconjXi : ∀ z, Xi (conj z) = conj (Xi z))
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (hE : ZeroEnumeration Xi γ m)
    (n₀ : ℕ) (h : PalierCritique γ m n₀) :
    Xi (γ (n₀ + 1)) = 0 ∧
    -- (1)
    ((∀ k, (newton γ m (n₀ + 1) k).im = 0) ∧
     (Delta γ m (n₀ + 1) (n₀ + 1)).re < 0 ∧
     (Delta γ m (n₀ + 1) (n₀ + 1)).im = 0 ∧
     ¬ ∃ B : Matrix (Fin (n₀ + 1)) (Fin (n₀ + 1)) ℝ, B.PosDef ∧
        ∀ p q, (B p q : ℂ) = newton γ m (n₀ + 1) (p + q)) ∧
    -- (2)
    (∀ N r : ℕ, n₀ + 1 ≤ N → n₀ + 1 ≤ r → r ≤ N →
      (Delta γ m N (n₀ + 1)).re ≤ 0 →
      ¬ ∃ B : Matrix (Fin r) (Fin r) ℝ, B.PosDef ∧
        ∀ p q, (B p q : ℂ) = newton γ m N (p + q)) ∧
    -- (3)
    (∀ N : ℕ, n₀ + 1 < N →
      (∀ j ∈ Finset.Icc 1 N, j ≠ n₀ → j ≠ n₀ + 1 →
        ∃ k ∈ Finset.Icc 1 N, k ≠ n₀ ∧ k ≠ n₀ + 1 ∧ γ k = conj (γ j)) →
      ∃ x : Fin 2 → ℝ, x ≠ 0) :=
  brainrot_Lemma Xi hconjXi γ m hE n₀ h

theorem brainrot_Lemma_xi_for_basic
    (γ : ℕ → ℂ) (m : ℕ → ℕ) (hE : ZeroEnumeration xiEntiere γ m)
    (n₀ : ℕ) (h : PalierCritique γ m n₀) :
    xiEntiere (γ (n₀ + 1)) = 0 ∧
    ((∀ k, (newton γ m (n₀ + 1) k).im = 0) ∧
     (Delta γ m (n₀ + 1) (n₀ + 1)).re < 0 ∧
     (Delta γ m (n₀ + 1) (n₀ + 1)).im = 0 ∧
     ¬ ∃ B : Matrix (Fin (n₀ + 1)) (Fin (n₀ + 1)) ℝ, B.PosDef ∧
        ∀ p q, (B p q : ℂ) = newton γ m (n₀ + 1) (p + q)) ∧
    (∀ N r : ℕ, n₀ + 1 ≤ N → n₀ + 1 ≤ r → r ≤ N →
      (Delta γ m N (n₀ + 1)).re ≤ 0 →
      ¬ ∃ B : Matrix (Fin r) (Fin r) ℝ, B.PosDef ∧
        ∀ p q, (B p q : ℂ) = newton γ m N (p + q)) ∧
    (∀ N : ℕ, n₀ + 1 < N →
      (∀ j ∈ Finset.Icc 1 N, j ≠ n₀ → j ≠ n₀ + 1 →
        ∃ k ∈ Finset.Icc 1 N, k ≠ n₀ ∧ k ≠ n₀ + 1 ∧ γ k = conj (γ j)) →
      ∃ x : Fin 2 → ℝ, x ≠ 0) :=
  brainrot_Lemma_xi γ m hE n₀ h


open RiemannHypProof



theorem Riemann_Hypothesis_hPos_for_basic (hHardy : HardyTheorem)
  (hGeom : HypotheseGeometrieSpectraleXi)
  (hpos : ∀ (γ : ℕ → ℂ) (m : ℕ → ℕ),
    ZeroEnumeration XiRiemann γ m → HankelPositive γ m) :
  RiemannHypothesis := Riemann_Hypothesis_hPos hHardy hGeom hpos

theorem Riemann_Hypothesis_hpalier_hAlign_for_basic (hHardy : HardyTheorem)
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
  RiemannHypothesis := Riemann_Hypothesis_hpalier_hAlign
    hHardy hPaliers hAlignPerm

theorem Riemann_Hypothesis_hGeom_for_basic (hHardy : HardyTheorem)
    (hGeom : HypotheseGeometrieSpectraleXi) :
    RiemannHypothesis := Riemann_Hypothesis_hGeom hHardy hGeom


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




end BasicThEqRiemann
