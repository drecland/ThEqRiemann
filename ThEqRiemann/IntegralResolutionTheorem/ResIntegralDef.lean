import mathlib
import ThEqRiemann.EqTheorem.DefThEq
import ThEqRiemann.EqTheorem.CompagnonCharpoly

/-! -/
namespace ResDef

open Set Matrix Module End Complex DefinitionsThEq

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]


noncomputable def spec (T : End ℂ V) : Finset ℂ :=
  (LinearMap.charpoly T).roots.toFinset

noncomputable def mT (T : End ℂ V) (μ : ℂ) : ℕ :=
  Module.finrank ℂ (T.maxGenEigenspace μ)

noncomputable def resInt (T : End ℂ V) {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (f : ℂ → E) : E :=
  ∑ μ ∈ spec T, (mT T μ) • f μ

lemma norm_resInt_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : End ℂ V) (f : ℂ → E) :
    ‖resInt T f‖ ≤ ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ := by
  unfold resInt
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
  rw [← Nat.cast_smul_eq_nsmul ℂ, norm_smul]
  simp

lemma resInt_mem {E : Type*} [AddCommGroup E] [Module ℂ E]
    (W : Submodule ℂ E) (T : End ℂ V) (f : ℂ → E) (hf : ∀ μ ∈ spec T, f μ ∈ W) :
    resInt T f ∈ W :=
  Submodule.sum_mem _ fun μ hμ => W.nsmul_mem (hf μ hμ) _




noncomputable def pf (T : End ℂ V) (f : ℂ → ℂ) : Polynomial ℂ :=
  Lagrange.interpolate (spec T) (fun μ => μ) f

noncomputable def Pprod (T : End ℂ V) (z : ℂ) : ℂ :=
  ∏ μ ∈ spec T, (z - μ) ^ mT T μ

---------------------------------------------------------------------

noncomputable def term (T : End ℂ V) {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (f : ℂ → E) (e : Fin (spec T).card ≃ spec T) (j : ℕ) : E :=
  if h : j < (spec T).card then mT T (e ⟨j, h⟩) • f (e ⟨j, h⟩) else 0

noncomputable def partialSum (T : End ℂ V) {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (f : ℂ → E) (e : Fin (spec T).card ≃ spec T) (n : ℕ) : E :=
  ∑ j ∈ Finset.range (min n (spec T).card), term T f e j

---------------------------------------------------------------------

def Val {E : Type*} [AddCommMonoid E] [Module ℂ E] (T : End ℂ V) (S : Set E) : Set E :=
  {x | ∃ f : ℂ → E, (∀ μ ∈ spec T, f μ ∈ S) ∧ resInt T f = x}

---------------------------------------------------------------------

noncomputable def newton (T : End ℂ V) (k : ℕ) : ℂ :=
  ∑ μ ∈ spec T, (mT T μ : ℂ) * μ ^ k

noncomputable def Rrat (x y : ℂ) : ℂ := - x / y


---------------------------------------------------------------------
-- For CritColi

noncomputable def nuMoment {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) (a : ℂ) (θ : ℝ) (k : ℕ) : ℂ :=
  ∑ j, (m j : ℂ) * (Complex.exp (-(θ * Complex.I)) * (z j - a)) ^ k

noncomputable def HankelR {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) (a : ℂ) (θ : ℝ)
    (r : ℕ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun p q => nuMoment z m a θ (p + q)

def Aligned {d : ℕ} (z : Fin d → ℂ) : Prop :=
  ∃ (a : ℂ) (θ : ℝ), ∀ j, ∃ x : ℝ, z j = a +
  Complex.exp (θ * Complex.I) * x

def HankelCriterion {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) : Prop :=
  ∃ a θ,
    (∀ k ≤ 2 * d - 1, (nuMoment z m a θ k).im = 0) ∧
      ∀ (r : ℕ), 1 ≤ r → r ≤ d →
        0 < (HankelR z m a θ r).det.re ∧ (HankelR z m a θ r).det.im = 0

noncomputable def wNode {d : ℕ} (z : Fin d → ℂ) (a : ℂ) (θ : ℝ) (j : Fin d) : ℂ :=
  Complex.exp (-(θ * Complex.I)) * (z j - a)

noncomputable def HankelRR {d : ℕ} (x : Fin d → ℝ) (m : Fin d → ℕ) (r : ℕ) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun p q => ∑ j, (m j : ℝ) * (x j) ^ ((p : ℕ) + q)

noncomputable def HankelSeq (ν : ℕ → ℝ) (r : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of fun p q => ν ((p : ℕ) + (q : ℕ))

noncomputable def momentForm (ν : ℕ → ℝ) (P Q : Polynomial ℝ) : ℝ :=
  ∑ p ∈ Finset.range (P.natDegree + 1), ∑ q ∈ Finset.range (Q.natDegree + 1),
    P.coeff p * Q.coeff q * ν (p + q)

noncomputable def nuReal {d : ℕ} (z : Fin d → ℂ) (m : Fin d → ℕ) (a : ℂ) (θ : ℝ) (k : ℕ) : ℝ :=
  (nuMoment z m a θ k).re

-------------------------------------------------------------------

open Polynomial BigOperators

noncomputable def nu {d : ℕ} (w : Fin d → ℂ) (m : Fin d → ℕ) (k : ℕ) : ℂ :=
  ∑ j, (m j : ℂ) * w j ^ k

noncomputable def nuR {d : ℕ} (w : Fin d → ℂ) (m : Fin d → ℕ) (k : ℕ) : ℝ :=
  (nu w m k).re

noncomputable def hankel {d : ℕ} (w : Fin d → ℂ) (m : Fin d → ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun p q => nuR w m (p + q)

noncomputable def L {d : ℕ} (w : Fin d → ℂ) (m : Fin d → ℕ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun k => (nuR w m k) • LinearMap.id)

noncomputable def RdegLE (n : ℕ) : Submodule ℝ ℝ[X] := Polynomial.degreeLE ℝ n

noncomputable def vandermondeW {d : ℕ} (w : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  Matrix.vandermonde w

---------------------------------------------------------------------

open MeasureTheory Finset Matrix
open scoped ComplexConjugate

structure IsBorelOn01 (μ : Measure ℝ) : Prop where
  finite : IsFiniteMeasure μ
  supp : μ (Set.Icc (0 : ℝ) 1)ᶜ = 0

def IsIntegralResolution (m : ℕ → ℝ) (μ : Measure ℝ) : Prop :=
  IsBorelOn01 μ ∧ ∀ k : ℕ, m k = ∫ x in Set.Icc (0 : ℝ) 1, x ^ k ∂μ

noncomputable def hankel' (m : ℕ → ℝ) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.of fun i j => ((m (i.val + j.val) : ℝ) : ℂ)

noncomputable def pc {N : ℕ} (c : Fin (N + 1) → ℂ) (x : ℝ) : ℂ :=
  ∑ j : Fin (N+1), c j * ((x : ℂ) ^ (j.val))

noncomputable def quadForm (m : ℕ → ℝ) (N : ℕ) (c : Fin (N + 1) → ℂ) : ℂ :=
  ∑ i : Fin (N+1), ∑ j : Fin (N+1), conj (c i) *
  c j * ((m (i.val + j.val) : ℝ) : ℂ)

def IsElementaryResolution (m : ℕ → ℝ) (N : ℕ)
    (x : (q : ℕ) → Fin q → ℝ) (lam : (q : ℕ) → Fin q → ℝ) : Prop :=
  (∀ q r, x q r ∈ Set.Icc (0:ℝ) 1) ∧ (∀ q r, 0 ≤ lam q r) ∧
  ∀ k ≤ 2 * N, Filter.Tendsto
    (fun q : ℕ => ∑ r : Fin q, lam q r * (x q r) ^ k)
    Filter.atTop (nhds (m k))

---------------------------------------------------------------------

noncomputable def polyOf {N : ℕ} (c : Fin (N + 1) → ℂ) : Polynomial ℂ :=
  ∑ j : Fin (N+1), Polynomial.C (c j) * Polynomial.X ^ j.val

noncomputable def Sq (x lam : (q : ℕ) → Fin q → ℝ)
  (P : Polynomial ℂ) (q : ℕ) : ℝ :=
  ∑ r : Fin q, lam q r * ‖P.eval ((x q r : ℝ) : ℂ)‖ ^ 2

def KroneckerPositive (m : ℕ → ℝ) (D : ℕ) : Prop :=
  ∃ (r : ℕ) (_ : r ≤ D) (pts : Fin r → ℝ) (w : Fin r → ℝ),
    Function.Injective pts ∧ (∀ i, pts i ∈ Set.Icc (0:ℝ) 1) ∧
    (∀ i, 0 < w i) ∧ ∀ k, m k = ∑ i, w i * pts i ^ k


-----------------------------------------------------------------------

noncomputable def hk (m : ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.of fun i j => ((m (i.val + j.val) : ℝ) : ℂ)


noncomputable def hkR (m : ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => m (i.val + j.val)

noncomputable def polyOfVec {D : ℕ} (b : Fin (D + 1) → ℝ) : Polynomial ℝ :=
  ∑ j : Fin (D + 1), Polynomial.C (b j) * Polynomial.X ^ j.val





end ResDef
