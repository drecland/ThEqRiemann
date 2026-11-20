import mathlib

/-! ... -/
namespace DefinitionsThEq

open Set Complex


noncomputable def indiceLacet (γ : ℝ → ℂ) (a : ℂ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I)) *
    ∫ t in (0:ℝ)..1, deriv γ t / (γ t - a)

noncomputable def residu (f : ℂ → ℂ) (a : ℂ) (r : ℝ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I)) * ∮ z in C(a, r), f z

axiom residus_theoreme
    (U : Set ℂ) (hU_open : IsOpen U) (hU_conn : IsPreconnected U)
    (hU_simply : SimplyConnectedSpace U)
    (A : Finset ℂ) (hA_sub : (A : Set ℂ) ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ (A : Set ℂ)))
    (γ : ℝ → ℂ) (hγ_loop : γ 0 = γ 1)
    (hγ_diff : ContDiffOn ℝ 1 γ (Set.Icc (0 : ℝ) 1))
    (hγ_range : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ U \ (A : Set ℂ)) :
    (∫ t in (0:ℝ)..1, deriv γ t * f (γ t))
      = 2 * Complex.I * (Real.pi : ℂ) *
        ∑ a ∈ A, (indiceLacet γ a) * (residu f a (1 : ℝ))

noncomputable def nbZerosAvecMultiplicite (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  ∑ᶠ a ∈ S, (meromorphicOrderAt f a).elim 0 Int.toNat

axiom rouche_theoreme
    (U : Set ℂ) (hU_open : IsOpen U)
    (K : Set ℂ) (hK_sub : K ⊆ U) (hK_compact : IsCompact K)
    (bordK_simple_loops : Prop)
    (f g : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    (hdom : ∀ z ∈ frontier K, ‖f z - g z‖ < ‖f z‖) :
    nbZerosAvecMultiplicite f
        (interior K) = nbZerosAvecMultiplicite g (interior K)

axiom Courant (n p : ℕ) (Ω : Set (Fin n → ℂ)) : Type

/-- Un courant est-il positif (cf. `df:mesure_hausdorff_courants`). -/
axiom Courant.positif {n p : ℕ} {Ω : Set (Fin n → ℂ)} (T : Courant n p Ω) : Prop

/-- Un courant est-il fermé, i.e. `dT = 0` au sens des distributions. -/
axiom Courant.ferme {n p : ℕ} {Ω : Set (Fin n → ℂ)} (T : Courant n p Ω) : Prop

/-- Masse d'un courant `T` évaluée sur un sous-ensemble `E ⊆ Ω` (réel positif étendu). -/
axiom Courant.masse {n p : ℕ} {Ω : Set (Fin n → ℂ)} (T : Courant n p Ω)
    (E : Set (Fin n → ℂ)) : ENNReal

/-- Restriction d'un courant défini sur `Ω` à un ouvert `Ω' ⊆ Ω`. -/
axiom Courant.restrict {n p : ℕ} {Ω Ω' : Set (Fin n → ℂ)} (hΩ' : Ω' ⊆ Ω)
    (T : Courant n p Ω) : Courant n p Ω'

noncomputable abbrev hausdorffMeasureC (n : ℕ) (d : ℝ) :
    MeasureTheory.Measure (Fin n → ℂ) :=
  MeasureTheory.Measure.hausdorffMeasure d

axiom harvey_polking_extension
    (n p : ℕ) (hp1 : 1 ≤ p) (hpn : p ≤ n)
    (Ω : Set (Fin n → ℂ)) (hΩ : IsOpen Ω)
    (A : Set (Fin n → ℂ)) (hA_sub : A ⊆ Ω) (hA_closed : IsClosed A)
    (hA_hausdorff : hausdorffMeasureC n (2 * p) A = 0)
    (T : Courant n p (Ω \ A)) (hT_pos : T.positif) (hT_ferme : T.ferme)
    (hmasse_finie : ∀ x ∈ A, ∃ U ∈ nhds x, T.masse (U ∩ (Ω \ A)) ≠ ⊤) :
    ∃! T' : Courant n p Ω,
      T'.positif ∧ T'.ferme ∧
      Courant.restrict (Set.sdiff_subset) T' = T

axiom VarieteAnalytique (n : ℕ) : Type

axiom VarieteAnalytique.toTopologicalSpace {n : ℕ} :
    TopologicalSpace (VarieteAnalytique n)

noncomputable instance {n : ℕ} : TopologicalSpace (VarieteAnalytique n) :=
  VarieteAnalytique.toTopologicalSpace

axiom EnsembleAnalytiqueFerme {n : ℕ} (X : VarieteAnalytique n) (p : ℕ) : Type

axiom EnsembleAnalytiqueFerme.toSet {n : ℕ} {X : VarieteAnalytique n} {p : ℕ}
    (V : EnsembleAnalytiqueFerme X p) : Set (VarieteAnalytique n)

axiom EnsembleAnalytiqueFerme.est_ferme {n : ℕ} {X : VarieteAnalytique n} {p : ℕ}
    (V : EnsembleAnalytiqueFerme X p) : IsClosed V.toSet

axiom EnsembleAnalytiqueFerme.partieReguliere {n : ℕ} {X : VarieteAnalytique n} {p : ℕ}
    (V : EnsembleAnalytiqueFerme X p) : Set (VarieteAnalytique n)

axiom Courant' (E : Type*) [TopologicalSpace E] (p : ℕ) (Ω : Set E) : Type

axiom Courant'.positif {E : Type*} [TopologicalSpace E] {p : ℕ} {Ω : Set E}
    (T : Courant' E p Ω) : Prop

axiom Courant'.ferme {E : Type*} [TopologicalSpace E] {p : ℕ} {Ω : Set E}
    (T : Courant' E p Ω) : Prop

axiom Courant'.masse {E : Type*} [TopologicalSpace E] {p : ℕ} {Ω : Set E}
    (T : Courant' E p Ω) (F : Set E) : ENNReal

axiom courantIntegration {n : ℕ} {X : VarieteAnalytique n} {p : ℕ}
    (V : EnsembleAnalytiqueFerme X p) :
    Courant' (VarieteAnalytique n) p Set.univ

axiom lelong_theoreme {n : ℕ} (X : VarieteAnalytique n) {p : ℕ}
    (V : EnsembleAnalytiqueFerme X p) :
    (courantIntegration V).positif ∧ (courantIntegration V).ferme

axiom lelong_masse_localement_finie {n : ℕ} (X : VarieteAnalytique n) {p : ℕ}
    (V : EnsembleAnalytiqueFerme X p) (z₀ : VarieteAnalytique n) :
    ∃ U ∈ nhds z₀, (courantIntegration V).masse U < ⊤

axiom prolongement_remmert_stein {n : ℕ} (X : VarieteAnalytique n) (p : ℕ) :
    EnsembleAnalytiqueFerme X p

axiom Courant'.support {E : Type*} [TopologicalSpace E] {p : ℕ} {Ω : Set E}
    (T : Courant' E p Ω) : Set E

axiom Courant'.support_isClosed {E : Type*} [TopologicalSpace E] {p : ℕ} {Ω : Set E}
    (T : Courant' E p Ω) : IsClosed T.support

axiom courantIntegration_support_subset {n : ℕ} {X : VarieteAnalytique n} {p : ℕ}
    (V : EnsembleAnalytiqueFerme X p) :
    (courantIntegration V).support ⊆ V.toSet

axiom masse_nulle_of_disjoint_support {E : Type*} [TopologicalSpace E] {p : ℕ}
    {Ω : Set E} (T : Courant' E p Ω) {U : Set E} (hU_open : IsOpen U)
    (hU_disjoint : Disjoint U T.support) :
    T.masse U = 0

axiom VarieteAnalytique.toX {n : ℕ} (X : VarieteAnalytique n) : ℂ × ℂ → VarieteAnalytique n

axiom VarieteAnalytique.ofX {n : ℕ} (X : VarieteAnalytique n) : VarieteAnalytique n → ℂ × ℂ

axiom VarieteAnalytique.toX_continuous {n : ℕ} (X : VarieteAnalytique n) :
    Continuous X.toX

axiom VarieteAnalytique.ofX_continuous {n : ℕ} (X : VarieteAnalytique n) :
    Continuous X.ofX

axiom VarieteAnalytique.toX_ofX {n : ℕ} (X : VarieteAnalytique n) :
    ∀ x, X.toX (X.ofX x) = x

axiom VarieteAnalytique.ofX_toX {n : ℕ} (X : VarieteAnalytique n) :
    ∀ z, X.ofX (X.toX z) = z

axiom Courant'.masse_mono {E : Type*} [TopologicalSpace E] {p : ℕ} {Ω : Set E}
    (T : Courant' E p Ω) {U V : Set E} (h : U ⊆ V) : T.masse U ≤ T.masse V

axiom Courant'.restrict {E : Type*} [TopologicalSpace E] {p : ℕ}
    {Ω Ω' : Set E} (hΩ' : Ω' ⊆ Ω) (T : Courant' E p Ω) : Courant' E p Ω'

axiom harvey_polking_extension' (E : Type*) [TopologicalSpace E] (p : ℕ)
    (hp1 : 1 ≤ p) (Ω : Set E) (hΩ : IsOpen Ω) (A : Set E)
    (hA_sub : A ⊆ Ω) (hA_closed : IsClosed A) (hA_negligible : Prop)
    (T : Courant' E p Ω) (hT_pos : T.positif) (hT_ferme : T.ferme)
    (hmasse_finie : ∀ x ∈ A, ∃ U ∈ nhds x, T.masse U < ⊤) :
    ∃! T' : Courant' E p Ω, T'.positif ∧ T'.ferme ∧
      Courant'.restrict (Ω' := Ω \ A) Set.sdiff_subset T' =
      Courant'.restrict (Ω' := Ω \ A) Set.sdiff_subset T

axiom decomposition_residu {n : ℕ} {p : ℕ} (Vbar_univ : Set (VarieteAnalytique n))
    (Pi0 : Courant' (VarieteAnalytique n) p Set.univ) (I_H : Set (VarieteAnalytique n))
    (hPi0_pos : Pi0.positif) (hPi0_ferme : Pi0.ferme) :
    ∃ R : Courant' (VarieteAnalytique n) p Set.univ,
      R.positif ∧ R.ferme

-----------------------------------------------------------------------------------

structure CadreGeometrique where
  Ω : Set ℂ
  hΩ_open : IsOpen Ω
  hΩ_bounded : Bornology.IsBounded Ω
  hΩ_simply : SimplyConnectedSpace Ω
  V : Set ℂ
  hV_open : IsOpen V
  hV_preconnected : IsPreconnected V
  hV_sub : closure Ω ⊆ V
  f : ℂ → ℂ
  hf : DifferentiableOn ℂ f V
  y : ℂ
  hy_bord : ∀ z ∈ frontier Ω, f z ≠ y

noncomputable def solutionsInterieures (C : CadreGeometrique) : Set ℂ :=
  {z ∈ C.Ω | C.f z = C.y}

noncomputable def ensembleSolutions (f : ℂ → ℂ) (Ω₁ : Set ℂ) (v : ℂ) : Set ℂ :=
  {x ∈ Ω₁ | f x = v}

noncomputable def ensemblePoles (f : ℂ → ℂ) (Ω : Set ℂ) : Set ℂ :=
  {x ∈ Ω | Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin x {x}ᶜ) Filter.atTop}

noncomputable def gAux (C : CadreGeometrique) : ℂ → ℂ :=
  fun z => C.f z - C.y

----------------------------------------------------------------------

/-- `z ↦ z^k * f'(z) / (f(z) - y)`, singular potential solvant, order `k`. -/
noncomputable def potentielSingulierResolvant (C : CadreGeometrique) (k : ℕ) : ℂ → ℂ :=
  fun z => z ^ k * deriv C.f z / (C.f z - C.y)

@[inherit_doc]
notation "Φ_Sing[" C ", " k "]" => potentielSingulierResolvant C k


/-- trace operator: intégrale `(1/(2iπ)) ∮_{∂Ω} ψ(z) dz`,
calculus with a parametrisation `γΩ : ℝ → ℂ`
-/
noncomputable def operateurTrace (γΩ : ℝ → ℂ) (ψ : ℂ → ℂ) : ℂ :=
  (1 / (2 * Real.pi * Complex.I)) *
    ∫ t in (0:ℝ)..1, deriv γΩ t * ψ (γΩ t)

notation "𝒯[" γΩ ", " ψ "]" => operateurTrace γΩ ψ

/-- Generalisation on solving integration : for all `w ∈ ℂ`,
`μ[C, γΩ, k](w) = (1/(2iπ)) ∮_{∂Ω} z^k f'(z) / (f(z) - w) dz`,
made by parametrisation of `γΩ` on `∂Ω`. -/
noncomputable def muResolvante (C : CadreGeometrique) (γΩ : ℝ → ℂ) (k : ℕ) : ℂ → ℂ :=
  fun w =>
    (1 / (2 * Real.pi * Complex.I)) *
      ∫ t in (0:ℝ)..1, deriv γΩ t * (γΩ t) ^ k * deriv C.f (γΩ t) / (C.f (γΩ t) - w)

notation "μ[" C ", " γΩ ", " k "]" => muResolvante C γΩ k


noncomputable def formeSpectrale (f : ℂ → ℂ) (w : ℂ) (k : ℕ) : ℂ → ℂ :=
  fun x => x ^ k * deriv f x / (f x - w)




----------------------------------------------------------------------

noncomputable def poles (h : ℂ → ℂ) (Ω₁ : Set ℂ) : Set ℂ :=
  {x ∈ Ω₁ | meromorphicOrderAt h x < 0}

noncomputable def orderZeros (h : ℂ → ℂ) (Ω₁ : Set ℂ) : Set ℂ :=
  {x ∈ Ω₁ | 0 < meromorphicOrderAt h x}

/-- Axiome (hypothèse de travail globale) : toute fonction méromorphe f sur un
ouvert Ω₁ est supposée donnée sous sa forme "canonique", i.e. en tout point x
de Ω₁ où f n'a pas de pôle (ordre ≥ 0), f coïncide avec son prolongement
analytique en x. Cet axiome est nommé pour pouvoir être invoqué explicitement
comme hypothèse dans les énoncés de lemmes. -/
axiom canonical_extension
    {Ω₁ : Set ℂ} {f : ℂ → ℂ} (hf : MeromorphicOn f Ω₁) :
    ∀ x ∈ Ω₁, 0 ≤ meromorphicOrderAt f x → AnalyticAt ℂ f x

----------------------------------------------------------------------


noncomputable def momentsHankel {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) (k : ℕ) : ℂ :=
  ∑ r : Fin K, (w r : ℂ) * (lam r) ^ k

noncomputable def hankel0 {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) :
    Matrix (Fin K) (Fin K) ℂ :=
  fun i j => momentsHankel lam w (i.1 + j.1)

noncomputable def vandermonde' {K : ℕ} (lam : Fin K → ℂ) :
    Matrix (Fin K) (Fin K) ℂ :=
  fun i r => (lam r) ^ (i : ℕ)

noncomputable def diagPoids {K : ℕ} (w : Fin K → ℤ) :
    Matrix (Fin K) (Fin K) ℂ :=
  Matrix.diagonal (fun r => (w r : ℂ))

noncomputable def polyAssocie {K : ℕ} (lam : Fin K → ℂ) : Polynomial ℂ :=
  ∏ r : Fin K, (Polynomial.X - Polynomial.C (lam r))

noncomputable def hankel1 {K : ℕ} (lam : Fin K → ℂ) (w : Fin K → ℤ) :
    Matrix (Fin K) (Fin K) ℂ :=
  fun i j => momentsHankel lam w (i.1 + j.1 + 1)

noncomputable def companion' {K : ℕ} (lam : Fin K → ℂ) :
    Matrix (Fin K) (Fin K) ℂ :=
  fun i j =>
    if (i : ℕ) = (j : ℕ) + 1 ∧ (j : ℕ) < K - 1 then 1
    else if (j : ℕ) = K - 1 then -(polyAssocie lam).coeff (i : ℕ)
    else 0

noncomputable def hankelOfMoments (K : ℕ) (mu : ℕ → ℂ) :
    Matrix (Fin K) (Fin K) ℂ :=
  fun i j => mu (i.1 + j.1)


---------------------------------------------------------------------





noncomputable def companionCoeff {K : ℕ} (c : Fin K → ℂ) :
    Matrix (Fin K) (Fin K) ℂ :=
  fun i j =>
    if (i : ℕ) = (j : ℕ) + 1 ∧ (j : ℕ) < K - 1 then 1
    else if (j : ℕ) = K - 1 then -(c i)
    else 0

noncomputable def polyAssocieCoeff {K : ℕ}
    (c : Fin K → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ K + ∑ j : Fin K,
    Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)


noncomputable def charPolyCoeff {K : ℕ} (lam : Fin K → ℂ) (j : Fin K) : ℂ :=
  -(polyAssocie lam).coeff (j : ℕ)

------------------------------------------------------------------------


noncomputable def ensemblePolesN {n : ℕ} (f : (Fin n → ℂ) → ℂ) (Ω : Set (Fin n → ℂ)) :
    Set (Fin n → ℂ) :=
  {x ∈ Ω | Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin x {x}ᶜ) Filter.atTop}

variable {n p : ℕ} (hn : 0 < n) (hp : 0 < p)
variable {Ω₁ : Set (Fin n → ℂ)} (hΩ₁_open : IsOpen Ω₁) (hΩ₁_conn : IsPreconnected Ω₁)
variable {Ω₂ : Set (Fin p → ℂ)} (hΩ₂_open : IsOpen Ω₂) (hΩ₂_conn : IsPreconnected Ω₂)


noncomputable def ensemblePolaireGlobal {n p : ℕ}
    (f : (Fin n → ℂ) → ℂ) (Ω₁ : Set (Fin n → ℂ))
    (g : (Fin p → ℂ) → ℂ) (Ω₂ : Set (Fin p → ℂ)) :
    Set ((Fin n → ℂ) × (Fin p → ℂ)) :=
  (ensemblePolesN f Ω₁ ×ˢ Ω₂) ∪ (Ω₁ ×ˢ ensemblePolesN g Ω₂)

noncomputable def ensembleIndetermination {n p : ℕ}
    (f : (Fin n → ℂ) → ℂ) (Ω₁ : Set (Fin n → ℂ))
    (g : (Fin p → ℂ) → ℂ) (Ω₂ : Set (Fin p → ℂ)) :
    Set ((Fin n → ℂ) × (Fin p → ℂ)) :=
  ensemblePolesN f Ω₁ ×ˢ ensemblePolesN g Ω₂

noncomputable def ensembleZerosH {n p : ℕ}
    (f : (Fin n → ℂ) → ℂ) (Ω₁ : Set (Fin n → ℂ))
    (g : (Fin p → ℂ) → ℂ) (Ω₂ : Set (Fin p → ℂ)) :
    Set ((Fin n → ℂ) × (Fin p → ℂ)) :=
  {z | z.1 ∈ Ω₁ ∧ z.2 ∈ Ω₂ ∧
       z.1 ∉ ensemblePolesN f Ω₁ ∧ z.2 ∉ ensemblePolesN g Ω₂ ∧
       f z.1 - g z.2 = 0}

lemma ensembleZerosH_eq {n p : ℕ}
    (f : (Fin n → ℂ) → ℂ) (Ω₁ : Set (Fin n → ℂ))
    (g : (Fin p → ℂ) → ℂ) (Ω₂ : Set (Fin p → ℂ)) :
    ensembleZerosH f Ω₁ g Ω₂ =
      ((Ω₁ ×ˢ Ω₂) \ ensemblePolaireGlobal f Ω₁ g Ω₂) ∩
        {z | f z.1 - g z.2 = 0} := by
  ext z
  simp only [ensembleZerosH, ensemblePolaireGlobal, Set.mem_inter_iff,
    Set.mem_sdiff, Set.mem_prod, Set.mem_union, Set.mem_ofPred_eq, not_or]
  tauto


lemma poles_eq_ensemblePoles
    {f : ℂ → ℂ} {Ω₁ : Set ℂ}
    (hf : MeromorphicOn f Ω₁) :
    poles f Ω₁ = ensemblePoles f Ω₁ := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxΩ, horder⟩
    refine ⟨hxΩ, ?_⟩
    exact (tendsto_norm_atTop_iff_cobounded
            (E := ℂ) (f := f) (l := nhdsWithin x {x}ᶜ)).mpr
          ((tendsto_cobounded_iff_meromorphicOrderAt_neg
            (hf x hxΩ)).mpr horder)
  · intro hx
    rcases hx with ⟨hxΩ, hlim⟩
    refine ⟨hxΩ, ?_⟩
    apply (tendsto_cobounded_iff_meromorphicOrderAt_neg (hf x hxΩ)).mp
    exact (tendsto_norm_atTop_iff_cobounded
            (E := ℂ) (f := f) (l := nhdsWithin x {x}ᶜ)).mp hlim

-------------------------------------------------------------------------

noncomputable def momentsParametres
    (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y : ℂ) : ℕ → ℂ :=
  fun k => muResolvante C γΩ k (g y)

noncomputable def hankel0Dynamique
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y : ℂ) :
    Matrix (Fin K) (Fin K) ℂ :=
  hankelOfMoments K (momentsParametres C γΩ g y)

noncomputable def hankel1Dynamique
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y : ℂ) :
    Matrix (Fin K) (Fin K) ℂ :=
  fun i j => momentsParametres C γΩ g y (i.1 + j.1 + 1)

noncomputable def operateurDecalageParametre
    (K : ℕ) (C : CadreGeometrique) (γΩ : ℝ → ℂ) (g : ℂ → ℂ) (y : ℂ)
    [Invertible (hankel0Dynamique K C γΩ g y)] :
    Matrix (Fin K) (Fin K) ℂ :=
  (hankel0Dynamique K C γΩ g y)⁻¹ * hankel1Dynamique K C γΩ g y

-- Rouche local ---
axiom solution_proche_pole_locale
    {f g : ℂ → ℂ} {y₀ pq : ℂ}
    (hpole : Filter.Tendsto (fun z => ‖f z‖) (nhdsWithin pq {pq}ᶜ) Filter.atTop)
    (hg : Filter.Tendsto (fun y => ‖g y‖) (nhdsWithin y₀ {y₀}ᶜ) Filter.atTop)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in nhdsWithin y₀ {y₀}ᶜ, ∃ x ∈ Metric.ball pq ε, f x = g y


----------------------------------------------------------------------

noncomputable def operateurM {r} (lam : Fin r → ℂ) (w : Fin r → ℤ) :
  Matrix (Fin r) (Fin r) ℂ :=
  (hankel0 lam w)⁻¹ * hankel1 lam w







end DefinitionsThEq
