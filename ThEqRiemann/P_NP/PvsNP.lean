import Mathlib
import ThEqRiemann.IntegralResolutionTheorem.ResIntegralDef
import ThEqRiemann.IntegralResolutionTheorem.IntResTheorem
import ThEqRiemann.IntegralResolutionTheorem.CircleIntegration2
import ThEqRiemann.IntegralResolutionTheorem.PartialSumProp
import ThEqRiemann.IntegralResolutionTheorem.MtSpec
import ThEqRiemann.IntegralResolutionTheorem.PfPolynomial
/-! -/
namespace P_NP


structure CostM (α : Type u) where
  val : α
  cost : Nat
deriving Repr, DecidableEq

namespace CostM

def pure (a : α) : CostM α := ⟨a, 0⟩

def bind (m : CostM α) (f : α → CostM β) : CostM β :=
  let r := f m.val
  ⟨r.val, m.cost + r.cost⟩

instance : Monad CostM where
  pure := CostM.pure
  bind := CostM.bind

def tickOp (a : α) (c : Nat := 1) : CostM α := ⟨a, c⟩

@[simp] theorem val_bind (m : CostM α) (f : α → CostM β) :
    (m.bind f).val = (f m.val).val := rfl

@[simp] theorem cost_bind (m : CostM α) (f : α → CostM β) :
    (m.bind f).cost = m.cost + (f m.val).cost := rfl

def repeatCost : Nat → CostM Unit → CostM Unit
  | 0,     _    => CostM.pure ()
  | n + 1, step => CostM.bind (repeatCost n step) (fun _ => step)

@[simp] theorem repeatCost_cost (n : Nat) (step : CostM Unit) :
    (repeatCost n step).cost = n * step.cost := by
  induction n with
  | zero =>
      simp only [repeatCost, CostM.pure, Nat.zero_mul]
  | succ k ih =>
      simp only [repeatCost, CostM.bind, ih]
      ring



end CostM

inductive BTree (α : Type u) where
  | leaf (x : α) : BTree α
  | node (left right : BTree α) : BTree α
deriving Repr

namespace BTree

def size : BTree α → Nat
  | leaf _   => 1
  | node l r => l.size + r.size

def depth : BTree α → Nat
  | leaf _   => 0
  | node l r => 1 + max l.depth r.depth

theorem size_pos (t : BTree α) : 1 ≤ t.size := by
  induction t with
  | leaf _ =>
      simp only [size]
      omega
  | node l r ihl ihr =>
      simp only [size]
      omega

def specProd : BTree Nat → Nat
  | leaf x   => x
  | node l r => l.specProd * r.specProd

def evalProd : BTree Nat → CostM Nat
  | leaf x   => CostM.pure x
  | node l r =>
      CostM.bind (evalProd l) (fun vl =>
      CostM.bind (evalProd r) (fun vr =>
      CostM.tickOp (vl * vr) 1))

theorem evalProd_correct (t : BTree Nat) :
    (evalProd t).val = specProd t := by
  induction t with
  | leaf x => rfl
  | node l r ihl ihr =>
      simp [evalProd, specProd, CostM.bind, CostM.tickOp, ihl, ihr]

theorem evalProd_cost_exact (t : BTree Nat) :
    (evalProd t).cost + 1 = t.size := by
  induction t with
  | leaf x => rfl
  | node l r ihl ihr =>
      simp only [evalProd, CostM.bind, CostM.tickOp, size]
      omega

end BTree

structure ClauseTree where
  lits : BTree Nat

def evalClause (c : ClauseTree) : CostM Nat :=
  CostM.bind (BTree.evalProd c.lits) (fun prodVal =>
  CostM.tickOp (1 - prodVal) 1)

theorem evalClause_cost (c : ClauseTree) :
    (evalClause c).cost = c.lits.size := by
  simp only [evalClause, CostM.bind, CostM.tickOp]
  have h := BTree.evalProd_cost_exact c.lits
  omega

def evalFormula : BTree ClauseTree → CostM Nat
  | BTree.leaf c   => evalClause c
  | BTree.node l r =>
      CostM.bind (evalFormula l) (fun vl =>
      CostM.bind (evalFormula r) (fun vr =>
      CostM.tickOp (vl * vr) 1))

def formulaLitSize : BTree ClauseTree → Nat
  | BTree.leaf c   => c.lits.size
  | BTree.node l r => formulaLitSize l + formulaLitSize r

def numClauses : BTree ClauseTree → Nat
  | BTree.leaf _   => 1
  | BTree.node l r => numClauses l + numClauses r

theorem numClauses_eq_size (f : BTree ClauseTree) :
    numClauses f = f.size := by
  induction f with
  | leaf _ => rfl
  | node l r ihl ihr =>
      simp only [numClauses, BTree.size, ihl, ihr]

theorem evalFormula_cost_exact (f : BTree ClauseTree) :
    (evalFormula f).cost + 1 = formulaLitSize f + numClauses f := by
  induction f with
  | leaf c =>
      simp only [evalFormula, formulaLitSize, numClauses, evalClause_cost]
  | node l r ihl ihr =>
      simp only [evalFormula, CostM.bind, CostM.tickOp, formulaLitSize, numClauses]
      omega

theorem evalFormula_cost_linear_bound (f : BTree ClauseTree) :
    numClauses f ≤ formulaLitSize f →
    (evalFormula f).cost + 1 ≤ 2 * formulaLitSize f := by
  intro hm
  have h := evalFormula_cost_exact f
  omega

theorem numClauses_le_formulaLitSize (f : BTree ClauseTree) :
    numClauses f ≤ formulaLitSize f := by
  induction f with
  | leaf c =>
      simp only [numClauses, formulaLitSize]
      exact BTree.size_pos c.lits
  | node l r ihl ihr =>
      simp only [numClauses, formulaLitSize]
      omega

def newtonGirardStepCost (j : Nat) : Nat := 2 * j + 1

def newtonGirardModuleCost : Nat → Nat
  | 0     => 0
  | K + 1 => newtonGirardModuleCost K + (2 * K + 1)

theorem newtonGirardModuleCost_eq_sq (K : Nat) :
    newtonGirardModuleCost K = K ^ 2 := by
  induction K with
  | zero => rfl
  | succ k ih =>
      simp only [newtonGirardModuleCost, ih]
      ring

---------------------------------------------------------------

def garnerPrecompLoop : Nat → Nat → CostM Unit
  | 0,     _ => CostM.pure ()
  | r + 1, w =>
      CostM.bind (garnerPrecompLoop r w) (fun _ =>
      CostM.tickOp () (r * w))

theorem garnerPrecompLoop_cost_exact (r w : Nat) :
    2 * (garnerPrecompLoop r w).cost + r * w = r ^ 2 * w := by
  induction r with
  | zero =>
      simp only [garnerPrecompLoop, CostM.pure]
      ring
  | succ k ih =>
      simp only [garnerPrecompLoop, CostM.bind, CostM.tickOp]
      have h : 2 * ((garnerPrecompLoop k w).cost + k * w) + (k + 1) * w
             = (2 * (garnerPrecompLoop k w).cost + k * w) + (2 * k + 1) * w := by ring
      rw [h, ih]
      ring

theorem step1_cost_le (r w : Nat) :
    (garnerPrecompLoop r w).cost ≤ r ^ 2 * w := by
  have h := garnerPrecompLoop_cost_exact r w
  omega

def step2EvalMoments (f : BTree ClauseTree) (N_loc r K : Nat) : CostM Unit :=
  let evalDomain := CostM.repeatCost N_loc (CostM.bind (evalFormula f) (fun _ => CostM.pure ()))
  let accumMoments := CostM.repeatCost r (CostM.repeatCost K (CostM.tickOp () K))
  CostM.bind evalDomain (fun _ => accumMoments)

theorem step2_cost_exact (f : BTree ClauseTree) (N_loc r K : Nat) :
    (step2EvalMoments f N_loc r K).cost =
      N_loc * (evalFormula f).cost + r * K ^ 2 := by
  simp only [step2EvalMoments, CostM.bind, CostM.repeatCost_cost, CostM.pure, CostM.tickOp]
  ring

def newtonGirardModule : Nat → CostM Unit
  | 0     => CostM.pure ()
  | K + 1 =>
      CostM.bind (newtonGirardModule K) (fun _ =>
      CostM.tickOp () (2 * K + 1))

theorem newtonGirardModule_cost (K : Nat) :
    (newtonGirardModule K).cost = newtonGirardModuleCost K := by
  induction K with
  | zero => rfl
  | succ k ih =>
      simp only [newtonGirardModule,
        newtonGirardModuleCost, CostM.bind, CostM.tickOp, ih]


def step3NewtonGirard (r K : Nat) : CostM Unit :=
  CostM.repeatCost r (newtonGirardModule K)

theorem step3_cost_exact (r K : Nat) :
    (step3NewtonGirard r K).cost = r * K ^ 2 := by
  simp only [step3NewtonGirard, CostM.repeatCost_cost, newtonGirardModule_cost,
             newtonGirardModuleCost_eq_sq]

def step4RootExtraction (r K shoupCost : Nat) : CostM Unit :=
  if K = 1 then
    CostM.repeatCost r (CostM.tickOp () 1)
  else
    CostM.repeatCost r (CostM.tickOp () (2 * K ^ 2 + shoupCost))

theorem step4_cost_K1 (r shoupCost : Nat) :
    (step4RootExtraction r 1 shoupCost).cost = r := by
  simp only [step4RootExtraction, ↓reduceIte, CostM.repeatCost_cost, CostM.tickOp, Nat.mul_one]

theorem step4_cost_general (r K shoupCost : Nat) (hK : K ≠ 1) :
    (step4RootExtraction r K shoupCost).cost = r * (2 * K ^ 2 + shoupCost) := by
  simp only [step4RootExtraction, hK, ↓reduceIte, CostM.repeatCost_cost, CostM.tickOp]

def step5GarnerBaseQ (K r n : Nat) : CostM Unit :=
  CostM.repeatCost K (CostM.tickOp () (r ^ 2 + r * n))



theorem step5_cost_exact (K r n : Nat) :
    (step5GarnerBaseQ K r n).cost = K * (r ^ 2 + r * n) := by
  simp only [step5GarnerBaseQ, CostM.repeatCost_cost, CostM.tickOp]


def globalModularSAT
    (f : BTree ClauseTree) (N_loc r w K n shoupCost : Nat) : CostM Unit :=
  CostM.bind (garnerPrecompLoop r w) (fun _ =>
  CostM.bind (step2EvalMoments f N_loc r K) (fun _ =>
  CostM.bind (step3NewtonGirard r K) (fun _ =>
  CostM.bind (step4RootExtraction r K shoupCost) (fun _ =>
  step5GarnerBaseQ K r n))))

theorem globalModularSAT_cost_exact_general
    (f : BTree ClauseTree) (N_loc r w K n shoupCost : Nat) (hK : K ≠ 1) :
    (globalModularSAT f N_loc r w K n shoupCost).cost =
      (garnerPrecompLoop r w).cost
      + N_loc * (evalFormula f).cost
      + 4 * r * K ^ 2
      + r * shoupCost
      + K * (r ^ 2 + r * n) := by
  simp only [globalModularSAT, CostM.bind, step2_cost_exact, step3_cost_exact,
             step4_cost_general r K shoupCost hK, step5_cost_exact]
  ring

theorem globalModularSAT_cost_bound_general
    (f : BTree ClauseTree) (N_loc r w K n shoupCost : Nat) (hK : K ≠ 1) :
    (globalModularSAT f N_loc r w K n shoupCost).cost ≤
      r ^ 2 * w
      + N_loc * (2 * formulaLitSize f)
      + 4 * r * K ^ 2
      + r * shoupCost
      + K * (r ^ 2 + r * n) := by
  rw [globalModularSAT_cost_exact_general f N_loc r w K n shoupCost hK]
  have h1 : (garnerPrecompLoop r w).cost ≤ r ^ 2 * w := step1_cost_le r w
  have hF : (evalFormula f).cost ≤ 2 * formulaLitSize f := by
    have hlin := evalFormula_cost_linear_bound f (numClauses_le_formulaLitSize f)
    omega
  have h2 : N_loc * (evalFormula f).cost ≤ N_loc * (2 * formulaLitSize f) :=
    Nat.mul_le_mul_left N_loc hF
  omega

theorem globalModularSAT_cost_bound_K1
    (f : BTree ClauseTree) (N_loc r w n shoupCost : Nat) :
    (globalModularSAT f N_loc r w 1 n shoupCost).cost ≤
      r ^ 2 * w
      + N_loc * (2 * formulaLitSize f)
      + 3 * r
      + r ^ 2
      + r * n := by
  have hexact :
      (globalModularSAT f N_loc r w 1 n shoupCost).cost =
        (garnerPrecompLoop r w).cost
        + N_loc * (evalFormula f).cost
        + 3 * r
        + r ^ 2
        + r * n := by
    simp only [globalModularSAT, CostM.bind, step2_cost_exact, step3_cost_exact,
               step4_cost_K1, step5_cost_exact]
    ring
  rw [hexact]
  have h1 : (garnerPrecompLoop r w).cost ≤ r ^ 2 * w := step1_cost_le r w
  have hF : (evalFormula f).cost ≤ 2 * formulaLitSize f := by
    have hlin := evalFormula_cost_linear_bound f (numClauses_le_formulaLitSize f)
    omega
  have h2 : N_loc * (evalFormula f).cost ≤ N_loc * (2 * formulaLitSize f) :=
    Nat.mul_le_mul_left N_loc hF
  omega

-- ----------------------------------------------------------------------


open Set Complex Module End
open ResDef ResIntTheorem PartialSum PfResIntTh MtRes

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]




open CircInt2 in
theorem resolution_integrale_residus_bis
    (T : End ℂ V) (f F : ℂ → ℂ) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hspec : ∀ μ ∈ spec T, μ ∈ Metric.ball c R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall c R))
    (hFf : ∀ μ ∈ spec T, F μ = f μ) :
    (1 / (2 * Real.pi * Complex.I)) *
      (∮ z in C(c, R), F z * LinearMap.trace ℂ V
        (Ring.inverse ((algebraMap ℂ (End ℂ V) z) - T))) = resInt T f :=
  contour_integral_resInt T f F c R hR hspec hF hFf


theorem resolution_integrale_bis (T : End ℂ V) (f : ℂ → ℂ)
    (e : Fin (spec T).card ≃ spec T) :
    (∀ n ≥ (spec T).card, partialSum T f e n = resInt T f) ∧
    Filter.Tendsto (partialSum T f e) Filter.atTop (nhds (resInt T f)) ∧
    (pf T f).degree < (spec T).card ∧
    (∀ μ ∈ spec T, (pf T f).eval μ = f μ) ∧
    LinearMap.trace ℂ V (Polynomial.aeval T (pf T f)) = resInt T f :=
  ⟨fun _ hn => partialSum_stationary T f e hn,
   partialSum_tendsto T f e,
   pf_degree_lt T f,
   fun _ hμ => pf_eval T f hμ,
   trace_pf T f⟩

theorem resolution_integrale_norme_bis {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : End ℂ V) (f : ℂ → E) :
    ‖resInt T f‖ ≤ ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ∧
    (∀ C : ℝ, (∀ μ ∈ spec T, ‖f μ‖ ≤ C) →
      ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ≤ (Module.finrank ℂ V : ℝ) * C) ∧
    (∀ W : Submodule ℂ E, (∀ μ ∈ spec T, f μ ∈ W) →
      resInt T f ∈ W ∧ Metric.infDist (resInt T f) (W : Set E) = 0) :=
  ⟨norm_resInt_le T f,
   fun C hC => sum_mT_norm_le T f C hC,
   fun W hW => ⟨resInt_mem W T f hW, infDist_resInt_eq_zero W T f hW⟩⟩


theorem resolution_integrale_complet_bis (T : End ℂ V) :
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
        ∑ μ ∈ spec T, (mT T μ : ℝ) * ‖f μ‖ ≤ (Module.finrank ℂ V : ℝ) * C)) ∧
    -- (5)
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]
        (W : Submodule ℂ E) (f : ℂ → E), (∀ μ ∈ spec T, f μ ∈ W) →
      resInt T f ∈ W ∧ Metric.infDist (resInt T f) (W : Set E) = 0) ∧
    -- (6)
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E],
      Val T (Set.univ : Set E) =
        {x | ∃ v : ℂ → E, x = ∑ μ ∈ spec T, mT T μ • v μ}) ∧
    (∀ {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Submodule ℂ E),
      Val T (W : Set E) = {x | ∃ w : ℂ → E, (∀ μ ∈ spec T, w μ ∈ W) ∧
        x = ∑ μ ∈ spec T, mT T μ • w μ} ∧ Val T (W : Set E) ⊆ W)  :=
  resolution_integrale_complet T



noncomputable def traceCLM : (V →L[ℂ] V) →ₗ[ℂ] ℂ where
  toFun A := LinearMap.trace ℂ V A.toLinearMap
  map_add' A B := by simp [map_add]
  map_smul' c A := by simp [map_smul]


noncomputable def resolvent (T : V →L[ℂ] V) (z : ℂ) : V →L[ℂ] V :=
  Ring.inverse ((algebraMap ℂ (V →L[ℂ] V) z) - T)
def phiMonomial (k : ℕ) : ℂ → ℂ := fun z => z ^ k

noncomputable def momentOp (T : V →L[ℂ] V) (c : ℂ) (R : ℝ) (k : ℕ) : V →L[ℂ] V :=
  (1 / (2 * Real.pi * I)) • ∮ z in C(c, R), z ^ k • resolvent T z

lemma circleIntegral_comp_comm
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (h_int : CircleIntegrable f c R) :
    L (∮ z in C(c, R), f z) = ∮ z in C(c, R), L (f z) := by
  simp only [circleIntegral]
  rw [← L.intervalIntegral_comp_comm]
  · simp only [map_smul]
  · simp only [deriv_circleMap]
    exact IntervalIntegrable.continuousOn_smul h_int
      (Continuous.continuousOn (by fun_prop))

theorem trace_momentOp_eq_resInt
    (T : V →L[ℂ] V) (c : ℂ) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (hspec : ∀ μ ∈ spec T.toLinearMap, μ ∈ Metric.ball c R)
    (h_int : CircleIntegrable (fun z => z ^ k • resolvent T z) c R)
    (h_inv_eq : ∀ z ∈ Metric.sphere c |R|,
      (resolvent T z).toLinearMap = Ring.inverse ((algebraMap ℂ (End ℂ V) z) - T.toLinearMap)) :
    LinearMap.trace ℂ V (momentOp T c R k).toLinearMap = resInt T.toLinearMap (phiMonomial k) := by
  have h_res := resolution_integrale_residus_bis T.toLinearMap (phiMonomial k) (phiMonomial k)
    c R hR hspec (differentiable_pow k).differentiableOn (fun _ _ => rfl)
  rw [← h_res]
  change traceCLM (momentOp T c R k) = _
  unfold momentOp phiMonomial
  rw [map_smul, smul_eq_mul]
  congr 1
  let trCont : (V →L[ℂ] V) →L[ℂ] ℂ :=
    ⟨traceCLM, (traceCLM (V := V)).continuous_of_finiteDimensional⟩
  have h_comm := circleIntegral_comp_comm trCont h_int
  rw [show traceCLM (∮ z in C(c, R), z ^ k • resolvent T z) =
      trCont (∮ z in C(c, R), z ^ k • resolvent T z) from rfl, h_comm]
  apply circleIntegral.integral_congr (le_of_lt hR)
  intro z hz
  simp only [trCont, ContinuousLinearMap.coe_mk', traceCLM, LinearMap.coe_mk, AddHom.coe_mk,
    map_smul, smul_eq_mul]
  have hz_abs : z ∈ Metric.sphere c |R| := by rwa [abs_of_pos hR]
  rw [h_inv_eq z hz_abs]

omit [FiniteDimensional ℂ V] in
lemma smul_resolvent_eq_one_add_mul
    (T : V →L[ℂ] V) (z : ℂ)
    (hz : IsUnit ((algebraMap ℂ (V →L[ℂ] V) z) - T)) :
    z • resolvent T z = 1 + T * resolvent T z := by
  unfold resolvent
  rw [Algebra.smul_def]
  calc
    algebraMap ℂ (V →L[ℂ] V) z * Ring.inverse (algebraMap ℂ (V →L[ℂ] V) z - T)
        = ((algebraMap ℂ (V →L[ℂ] V) z - T) + T) *
            Ring.inverse (algebraMap ℂ (V →L[ℂ] V) z - T) := by
          rw [sub_add_cancel]
    _ = (algebraMap ℂ (V →L[ℂ] V) z - T) * Ring.inverse (algebraMap ℂ (V →L[ℂ] V) z - T) +
        T * Ring.inverse (algebraMap ℂ (V →L[ℂ] V) z - T) := by
          rw [add_mul]
    _ = 1 + T * Ring.inverse (algebraMap ℂ (V →L[ℂ] V) z - T) := by
          rw [Ring.mul_inverse_cancel _ hz]

lemma circleIntegrable_comp
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : E →L[ℂ] F) {f : ℂ → E} {c : ℂ} {R : ℝ}
    (h_int : CircleIntegrable f c R) :
    CircleIntegrable (fun z => L (f z)) c R :=
  ⟨L.integrable_comp h_int.1, L.integrable_comp h_int.2⟩

theorem momentOp_succ
    (T : V →L[ℂ] V) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) (k : ℕ)
    (h_inv : ∀ z ∈ Metric.sphere c |R|, IsUnit ((algebraMap ℂ (V →L[ℂ] V) z) - T))
    (h_int_k : CircleIntegrable (fun z => z ^ k • resolvent T z) c R) :
    momentOp T c R (k + 1) = T * momentOp T c R k := by
  unfold momentOp
  rw [mul_smul_comm]
  congr 1
  have h_eq : ∀ z ∈ Metric.sphere c |R|,
      z ^ (k + 1) • resolvent T z =
      z ^ k • (1 : V →L[ℂ] V) + T * (z ^ k • resolvent T z) := by
    intro z hz
    calc
      z ^ (k + 1) • resolvent T z
          = (z ^ k * z) • resolvent T z := by rw [pow_succ]
      _ = z ^ k • (z • resolvent T z) := by rw [mul_smul]
      _ = z ^ k • (1 + T * resolvent T z) := by rw [smul_resolvent_eq_one_add_mul T z (h_inv z hz)]
      _ = z ^ k • (1 : V →L[ℂ] V) + z ^ k • (T * resolvent T z) := by rw [smul_add]
      _ = z ^ k • (1 : V →L[ℂ] V) + T * (z ^ k • resolvent T z) := by rw [mul_smul_comm]
  have h_int_congr : (∮ z in C(c, R), z ^ (k + 1) • resolvent T z) =
      ∮ z in C(c, R), (z ^ k • (1 : V →L[ℂ] V) + T * (z ^ k • resolvent T z)) := by
    unfold circleIntegral
    apply intervalIntegral.integral_congr
    intro θ _
    dsimp only
    rw [h_eq (circleMap c R θ) (circleMap_mem_sphere' c R θ)]
  rw [h_int_congr]
  let mulT : (V →L[ℂ] V) →L[ℂ] (V →L[ℂ] V) :=
    (LinearMap.mulLeft ℂ T).toContinuousLinearMap
  have h_int_one : CircleIntegrable (fun z : ℂ => z ^ k • (1 : V →L[ℂ] V)) c R :=
    ((continuous_pow k).smul continuous_const).continuousOn.circleIntegrable hR
  have h_int_mulT : CircleIntegrable (fun z => T * (z ^ k • resolvent T z)) c R :=
    circleIntegrable_comp mulT h_int_k
  rw [circleIntegral.integral_add h_int_one h_int_mulT]
  have h_cauchy : (∮ z in C(c, R), z ^ k • (1 : V →L[ℂ] V)) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hR (s := ∅) Set.countable_empty
    · exact ((continuous_pow k).smul continuous_const).continuousOn
    · intro z _
      have hpow : DifferentiableAt ℂ (fun w : ℂ => w ^ k) z :=
        (differentiable_pow k).differentiableAt
      exact hpow.smul_const (1 : V →L[ℂ] V)
  rw [h_cauchy, zero_add]
  exact (circleIntegral_comp_comm mulT h_int_k).symm

theorem momentOp_eq_pow_mul_zero
    (T : V →L[ℂ] V) (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (h_inv : ∀ z ∈ Metric.sphere c |R|, IsUnit ((algebraMap ℂ (V →L[ℂ] V) z) - T))
    (h_int : ∀ n : ℕ, CircleIntegrable (fun z => z ^ n • resolvent T z) c R)
    (k : ℕ) :
    momentOp T c R k = T ^ k * momentOp T c R 0 := by
  induction k with
  | zero =>
      simp only [pow_zero, one_mul]
  | succ n ih =>
      rw [momentOp_succ T c R hR n h_inv (h_int n), ih, ← mul_assoc, ← pow_succ']


theorem recurrence_moments_hankel_resolution
    (T : V →L[ℂ] V) (c : ℂ) (R : ℝ) (hR : 0 < R)
    (hspec : ∀ μ ∈ spec T.toLinearMap, μ ∈ Metric.ball c R)
    (h_inv : ∀ z ∈ Metric.sphere c |R|, IsUnit ((algebraMap ℂ (V →L[ℂ] V) z) - T))
    (h_inv_eq : ∀ z ∈ Metric.sphere c |R|,
      (resolvent T z).toLinearMap = Ring.inverse ((algebraMap ℂ (End ℂ V) z) - T.toLinearMap))
    (h_int : ∀ n : ℕ, CircleIntegrable (fun z => z ^ n • resolvent T z) c R)
    (hM0 : momentOp T c R 0 = 1)
    (μ : ℕ → ℂ)
    (hμ : ∀ k : ℕ, μ k = resInt T.toLinearMap (phiMonomial k)) :
    -- (1)
    (∀ k : ℕ, μ k = LinearMap.trace ℂ V (momentOp T c R k).toLinearMap) ∧
    -- (2)
    (∀ k : ℕ,
      momentOp T c R (k + 1) = T * momentOp T c R k ∧
      μ (k + 1) = LinearMap.trace ℂ V (T * momentOp T c R k).toLinearMap ∧
      μ (k + 1) = resInt T.toLinearMap (fun z => z * phiMonomial k z)) ∧
    -- (3)
    (∀ k : ℕ,
      momentOp T c R k = T ^ k * momentOp T c R 0 ∧
      momentOp T c R k = T ^ k ∧
      μ 0 = (Module.finrank ℂ V : ℂ) ∧
      μ k = LinearMap.trace ℂ V (T ^ k * momentOp T c R 0).toLinearMap) := by
  have h1 : ∀ k : ℕ, μ k = LinearMap.trace ℂ V (momentOp T c R k).toLinearMap := by
    intro k
    rw [hμ k, ← trace_momentOp_eq_resInt T c R hR k hspec (h_int k) h_inv_eq]
  refine ⟨h1, ?_, ?_⟩
  · intro k
    have hstep := momentOp_succ T c R (le_of_lt hR) k h_inv (h_int k)
    refine ⟨hstep, ?_, ?_⟩
    · rw [h1 (k + 1), hstep]
    · rw [hμ (k + 1)]
      congr 1
      funext z
      simp only [phiMonomial, pow_succ']
  · intro k
    have hpow := momentOp_eq_pow_mul_zero T c R (le_of_lt hR) h_inv h_int k
    refine ⟨hpow, ?_, ?_, ?_⟩
    · rw [hpow, hM0, mul_one]
    · rw [h1 0, hM0]
      exact LinearMap.trace_one ℂ V
    · rw [h1 k, hpow]


-------------------------------------------------------------------------

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]

omit [FiniteDimensional ℂ H] in
lemma isCompl_range_ker_of_idempotent
    (P : End ℂ H) (hP : P * P = P) :
    IsCompl (LinearMap.range P) (LinearMap.ker P) := by
  have hP_apply : ∀ x : H, P (P x) = P x := fun x =>
    congrArg (fun f : End ℂ H => f x) hP
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx_range hx_ker
    rcases hx_range with ⟨y, rfl⟩
    rw [LinearMap.mem_ker] at hx_ker
    rw [← hP_apply y, hx_ker]
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    intro x
    refine ⟨P x, x - P x, ⟨x, rfl⟩, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hP_apply, sub_self]

lemma trace_idempotent_eq_finrank_range
    (P : End ℂ H) (hP : P * P = P) :
    LinearMap.trace ℂ H P = (Module.finrank ℂ
      (LinearMap.range P) : ℂ) := by
  have hP_apply : ∀ x : H, P (P x) = P x := fun x =>
    congrArg (fun f : End ℂ H => f x) hP
  have hcompl := isCompl_range_ker_of_idempotent P hP
  let e : (LinearMap.range P × LinearMap.ker P) ≃ₗ[ℂ] H :=
    Submodule.prodEquivOfIsCompl (LinearMap.range P) (LinearMap.ker P) hcompl
  let b1 := Module.finBasis ℂ (LinearMap.range P)
  let b2 := Module.finBasis ℂ (LinearMap.ker P)
  let b := (b1.prod b2).map e
  rw [LinearMap.trace_eq_matrix_trace ℂ b P, Matrix.trace]
  simp only [Matrix.diag_apply, LinearMap.toMatrix_apply, Fintype.sum_sum_type]
  have h_left : ∀ i, b.repr (P (b (Sum.inl i))) (Sum.inl i) = 1 := by
    intro i
    have h_mem : b (Sum.inl i) ∈ LinearMap.range P := by
      have h_eq : b (Sum.inl i) = (b1 i : H) := by
        simp only [b, Basis.map_apply, Basis.prod_apply]
        exact add_zero (b1 i : H)
      rw [h_eq]
      exact (b1 i).2
    rcases h_mem with ⟨y, hy⟩
    have h_fix : P (b (Sum.inl i)) = b (Sum.inl i) := by
      rw [← hy, hP_apply]
    rw [h_fix, b.repr_self, Finsupp.single_eq_same]
  have h_right : ∀ j, b.repr (P (b (Sum.inr j))) (Sum.inr j) = 0 := by
    intro j
    have h_mem : b (Sum.inr j) ∈ LinearMap.ker P := by
      have h_eq : b (Sum.inr j) = (b2 j : H) := by
        simp only [b, Basis.map_apply, Basis.prod_apply]
        exact zero_add (b2 j : H)
      rw [h_eq]
      exact (b2 j).2
    rw [LinearMap.mem_ker] at h_mem
    rw [h_mem, map_zero, Finsupp.zero_apply]
  simp [h_left, h_right]

omit [FiniteDimensional ℂ H] in
lemma pow_apply_eigenbasis
    {D : ℕ} (T : H →L[ℂ] H) (b : Basis (Fin D) ℂ H) (ω : Fin D → ℂ)
    (heig : ∀ r : Fin D, T (b r) = ω r • b r) (k : ℕ) (r : Fin D) :
    (T ^ k) (b r) = (ω r) ^ k • b r := by
  induction k with
  | zero =>
      simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp,
        ih, map_smul, heig r, smul_smul, pow_succ]

omit [FiniteDimensional ℂ H] in
lemma toMatrix_pow_eigenbasis
    {D : ℕ} (T : H →L[ℂ] H) (b : Basis (Fin D) ℂ H) (ω : Fin D → ℂ)
    (heig : ∀ r : Fin D, T (b r) = ω r • b r) (k : ℕ) :
    LinearMap.toMatrix b b (T ^ k).toLinearMap = Matrix.diagonal (fun r => (ω r) ^ k) := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change b.repr ((T ^ k) (b j)) i = Matrix.diagonal (fun r => (ω r) ^ k) i j
  rw [pow_apply_eigenbasis T b ω heig k j, map_smul, b.repr_self]
  by_cases hij : i = j <;> simp [hij]

theorem calcul_explicite_M0_T_general
    (T P_V : H →L[ℂ] H)
    (hP_idem : P_V.toLinearMap * P_V.toLinearMap = P_V.toLinearMap)
    (c : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (h_inv : ∀ z ∈ Metric.sphere c |R|, IsUnit ((algebraMap ℂ (H →L[ℂ] H) z) - T))
    (h_int : ∀ n : ℕ, CircleIntegrable (fun z => z ^ n • resolvent T z) c R)
    (hM0 : momentOp T c R 0 = P_V)
    (μ : ℕ → ℂ)
    (hμ_trace : ∀ k : ℕ, μ k = LinearMap.trace ℂ H (momentOp T c R k).toLinearMap)
    {D : ℕ} (b : Basis (Fin D) ℂ H) (ω : Fin D → ℂ)
    (heig : ∀ r : Fin D, T (b r) = ω r • b r) :
    -- (1)
    (momentOp T c R 0 = P_V ∧
      μ 0 = LinearMap.trace ℂ H (momentOp T c R 0).toLinearMap ∧
      μ 0 = (Module.finrank ℂ (LinearMap.range P_V.toLinearMap) : ℂ)) ∧
    -- (2)
    (∀ k : ℕ,
      LinearMap.toMatrix b b (T ^ k).toLinearMap = Matrix.diagonal (fun r => (ω r) ^ k)) ∧
    -- (3)
    (∀ k : ℕ,
      momentOp T c R k = T ^ k * momentOp T c R 0 ∧
      momentOp T c R k = T ^ k * P_V ∧
      μ k = LinearMap.trace ℂ H (T ^ k * momentOp T c R 0).toLinearMap) := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hM0, hμ_trace 0, ?_⟩
    rw [hμ_trace 0, hM0]
    exact trace_idempotent_eq_finrank_range P_V.toLinearMap hP_idem
  · intro k
    exact toMatrix_pow_eigenbasis T b ω heig k
  · intro k
    have hpow := momentOp_eq_pow_mul_zero T c R hR h_inv h_int k
    refine ⟨hpow, ?_, ?_⟩
    · rw [hpow, hM0]
    · rw [hμ_trace k, hpow]

open scoped BigOperators

def digitQ (Q k i : ℕ) : ℕ :=
  (k / Q ^ i) % Q

lemma sum_digitQ_mul_pow (Q : ℕ) (hQ : 0 < Q) :
    ∀ (n k : ℕ), k < Q ^ n →
      ∑ i : Fin n, digitQ Q k i.val * Q ^ i.val = k := by
  intro n
  induction n with
  | zero =>
      intro k hk
      simp only [pow_zero] at hk
      have hk0 : k = 0 := Nat.lt_one_iff.mp hk
      subst hk0
      simp
  | succ m ih =>
      intro k hk
      rw [Fin.sum_univ_succ]
      have h_div_lt : k / Q < Q ^ m := by
        rw [Nat.div_lt_iff_lt_mul hQ]
        simpa [pow_succ] using hk
      have h_shift : ∀ i : Fin m, digitQ Q k (i.val + 1) = digitQ Q (k / Q) i.val := by
        intro i
        unfold digitQ
        rw [pow_succ', Nat.div_div_eq_div_mul]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, h_shift, pow_succ']
      have h_pull : ∑ i : Fin m, digitQ Q (k / Q) i.val * (Q * Q ^ i.val) =
          Q * ∑ i : Fin m, digitQ Q (k / Q) i.val * Q ^ i.val := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h_pull, ih (k / Q) h_div_lt]
      unfold digitQ
      simp only [pow_zero, Nat.div_one]
      exact Nat.mod_add_div k Q

def digitOp (Q n : ℕ) (i : Fin n) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ :=
  Matrix.diagonal (fun k => (digitQ Q k.val i.val : ℂ))

def T_SAT (Q n : ℕ) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ :=
  Matrix.diagonal (fun k => (k.val : ℂ))

lemma T_SAT_eq_sum_digitOp (Q n : ℕ) (hQ : 0 < Q) :
    T_SAT Q n = ∑ i : Fin n, (Q ^ i.val : ℂ) • digitOp Q n i := by
  ext r c
  simp only [T_SAT, digitOp, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hrc : r = c
  · subst hrc
    simp only [↓reduceIte]
    have h_nat := sum_digitQ_mul_pow Q hQ n r.val r.isLt
    have h_cast : ((∑ i : Fin n, digitQ Q r.val i.val * Q ^ i.val : ℕ) : ℂ) = (r.val : ℂ) := by
      exact_mod_cast h_nat
    rw [← h_cast, Nat.cast_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  · simp [hrc]

lemma T_SAT_pow (Q n m : ℕ) :
    (T_SAT Q n) ^ m = Matrix.diagonal (fun k => (k.val : ℂ) ^ m) := by
  unfold T_SAT
  rw [Matrix.diagonal_pow]
  rfl

lemma matrix_diagonal_list_prod {ι R : Type*}
    [Fintype ι] [DecidableEq ι] [Semiring R]
    (L : List (ι → R)) :
    (L.map Matrix.diagonal).prod =
      Matrix.diagonal (fun k => (L.map (fun f => f k)).prod) := by
  induction L with
  | nil =>
      simp [Matrix.diagonal_one]
  | cons f fs ih =>
      simp only [List.map_cons, List.prod_cons,
        ih, Matrix.diagonal_mul_diagonal]

def projVar (Q n : ℕ) (i : Fin n) (a : ℕ) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ :=
  Matrix.diagonal (fun k => if digitQ Q k.val i.val = a then 1 else 0)

def evalClause' (Q n : ℕ) (clause : List (Fin n × ℕ)) (k : Fin (Q ^ n)) : Bool :=
  clause.any (fun l => decide (digitQ Q k.val l.1.val = l.2))

def evalCNF (Q n : ℕ) (cnf : List (List (Fin n × ℕ))) (k : Fin (Q ^ n)) : Bool :=
  cnf.all (fun clause => evalClause' Q n clause k)

def v_SAT {Q n : ℕ} (eval : Fin (Q ^ n) → Bool) (k : Fin (Q ^ n)) : ℂ :=
  if eval k then 1 else 0

def M0_SAT {Q n : ℕ} (eval : Fin (Q ^ n) → Bool) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ :=
  Matrix.diagonal (v_SAT eval)

def projClause (Q n : ℕ) (clause : List (Fin n × ℕ)) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ :=
  1 - (clause.map (fun l => (1 : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ) -
    projVar Q n l.1 l.2)).prod

lemma projClause_eq_diagonal (Q n : ℕ) (clause : List (Fin n × ℕ)) :
    projClause Q n clause = Matrix.diagonal (v_SAT (evalClause' Q n clause)) := by
  unfold projClause
  have h_map : clause.map (fun l =>
    (1 : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ) - projVar Q n l.1 l.2) =
      (clause.map (fun l k => (1 : ℂ) - if
        digitQ Q k.val l.1.val = l.2 then 1 else 0)).map
          Matrix.diagonal := by
    rw [List.map_map]
    refine List.map_congr_left fun l _ => ?_
    ext r c
    by_cases hrc : r = c <;> simp [hrc, projVar]
  rw [h_map, matrix_diagonal_list_prod]
  have h_one : (1 : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ) = Matrix.diagonal (fun _ => 1) :=
    (Matrix.diagonal_one).symm
  rw [h_one, Matrix.diagonal_sub]
  congr 1
  funext k
  unfold v_SAT evalClause'
  clear h_map h_one
  induction clause with
  | nil =>
      simp
  | cons l ls ih =>
      simp only [List.map_cons, List.prod_cons, List.any_cons]
      by_cases hl : digitQ Q k.val l.1.val = l.2
      · simp [hl]
      · simp only [hl, ↓reduceIte, sub_zero, one_mul, decide_false, Bool.false_or]
        exact ih

lemma M0_SAT_eq_prod_projClause (Q n : ℕ) (cnf : List (List (Fin n × ℕ))) :
    M0_SAT (evalCNF Q n cnf) = (cnf.map (projClause Q n)).prod := by
  have h_map : cnf.map (projClause Q n) =
      (cnf.map (fun clause => v_SAT (evalClause' Q n clause))).map Matrix.diagonal := by
    rw [List.map_map]
    refine List.map_congr_left fun clause _ => ?_
    exact projClause_eq_diagonal Q n clause
  rw [h_map, matrix_diagonal_list_prod]
  unfold M0_SAT
  congr 1
  funext k
  unfold v_SAT evalCNF
  clear h_map
  induction cnf with
  | nil =>
      simp
  | cons c cs ih =>
      simp only [List.map_cons, List.prod_cons, List.all_cons]
      by_cases hc : evalClause' Q n c k = true
      · simp only [hc, Bool.true_and, ↓reduceIte, one_mul]
        exact ih
      · simp [hc]

lemma trace_M0_SAT {Q n : ℕ} (eval : Fin (Q ^ n) → Bool) :
    Matrix.trace (M0_SAT eval) = ∑ k : Fin (Q ^ n), v_SAT eval k ∧
    Matrix.trace (M0_SAT eval) =
      ((Finset.univ.filter (fun k : Fin
        (Q ^ n) => eval k = true)).card : ℂ) := by
  have h1 : Matrix.trace (M0_SAT eval) = ∑ k :
    Fin (Q ^ n), v_SAT eval k := by
    simp [M0_SAT, Matrix.trace_diagonal]
  refine ⟨h1, ?_⟩
  rw [h1]
  simp [v_SAT, Finset.sum_boole]

lemma trace_T_pow_mul_M0 {Q n : ℕ} (eval : Fin (Q ^ n) → Bool) (m : ℕ) :
    Matrix.trace ((T_SAT Q n) ^ m * M0_SAT eval) =
      ∑ k : Fin (Q ^ n), (k.val : ℂ) ^ m * v_SAT eval k := by
  rw [T_SAT_pow, M0_SAT, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]

def T_SAT_mod (Q n p : ℕ) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) (ZMod p) :=
  Matrix.diagonal (fun k => (k.val : ZMod p))

def M0_SAT_mod {Q n : ℕ} (eval : Fin (Q ^ n) → Bool) (p : ℕ) :
    Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) (ZMod p) :=
  Matrix.diagonal (fun k => if eval k then (1 : ZMod p) else 0)

lemma trace_T_pow_mul_M0_mod {Q n : ℕ} (eval : Fin (Q ^ n) → Bool) (p m : ℕ) :
    Matrix.trace ((T_SAT_mod Q n p) ^ m * M0_SAT_mod eval p) =
      ∑ k : Fin (Q ^ n), (k.val : ZMod p) ^ m *
        (if eval k then (1 : ZMod p) else 0) := by
  unfold T_SAT_mod M0_SAT_mod
  rw [Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  simp only [Pi.pow_apply]

lemma cast_moment_int_eq_trace_mod {Q n : ℕ} (eval : Fin (Q ^ n) → Bool) (p m : ℕ) :
    ((∑ k : Fin (Q ^ n), (k.val : ℤ) ^ m * (if eval k then (1 : ℤ) else 0) : ℤ) : ZMod p) =
      Matrix.trace ((T_SAT_mod Q n p) ^ m * M0_SAT_mod eval p) := by
  rw [trace_T_pow_mul_M0_mod, Int.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : eval k = true <;> simp [hk]

theorem caracterisation_moments_SAT_T_M0
    (Q n : ℕ) (hQ : 2 ≤ Q) (cnf : List (List (Fin n × ℕ))) :
    -- (1)
    (T_SAT Q n = ∑ i : Fin n, (Q ^ i.val : ℂ) • digitOp Q n i ∧
      ∀ m : ℕ, (T_SAT Q n) ^ m = Matrix.diagonal
        (fun k => (k.val : ℂ) ^ m)) ∧
    -- (2)
    (M0_SAT (evalCNF Q n cnf) = (cnf.map (projClause Q n)).prod ∧
      Matrix.trace (M0_SAT (evalCNF Q n cnf)) = ∑ k :
        Fin (Q ^ n), v_SAT (evalCNF Q n cnf) k ∧
      Matrix.trace (M0_SAT (evalCNF Q n cnf)) =
        ((Finset.univ.filter (fun k : Fin (Q ^ n) =>
          evalCNF Q n cnf k = true)).card : ℂ)) ∧
    -- (3)
    ((∀ m : ℕ, Matrix.trace ((T_SAT Q n) ^ m *
      M0_SAT (evalCNF Q n cnf)) =
        ∑ k : Fin (Q ^ n), (k.val : ℂ) ^ m * v_SAT
          (evalCNF Q n cnf) k) ∧
      (∀ p m : ℕ, Matrix.trace ((T_SAT_mod Q n p) ^ m *
        M0_SAT_mod (evalCNF Q n cnf) p) =
        ∑ k : Fin (Q ^ n), (k.val : ZMod p) ^ m *
          (if evalCNF Q n cnf k then (1 : ZMod p) else 0)) ∧
      (∀ p m : ℕ,
        ((∑ k : Fin (Q ^ n), (k.val : ℤ) ^ m *
          (if evalCNF Q n cnf k then (1 : ℤ) else 0) : ℤ) : ZMod p) =
          Matrix.trace ((T_SAT_mod Q n p) ^ m * M0_SAT_mod
            (evalCNF Q n cnf) p))) := by
  have hQ_pos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have h_tr := trace_M0_SAT (evalCNF Q n cnf)
  refine ⟨⟨T_SAT_eq_sum_digitOp Q n hQ_pos, T_SAT_pow Q n⟩,
    ⟨M0_SAT_eq_prod_projClause Q n cnf, h_tr.1, h_tr.2⟩,
    ⟨trace_T_pow_mul_M0 (evalCNF Q n cnf),
      trace_T_pow_mul_M0_mod (evalCNF Q n cnf),
      cast_moment_int_eq_trace_mod (evalCNF Q n cnf)⟩⟩




--------------------------------------------------------------------------

abbrev ClauseSATPlus (Q : ℕ) := List (ℕ × Fin Q)
abbrev InstanceSATPlus (Q : ℕ) := List (ClauseSATPlus Q)

def evalLitSATPlus (Q n : ℕ) (lit : ℕ × Fin Q) (k : Fin (Q ^ n)) : Bool :=
  decide ((k.val / Q ^ lit.1) % Q = lit.2.val)

def evalClauseSATPlus (Q n : ℕ) (c : ClauseSATPlus Q) (k : Fin (Q ^ n)) : Bool :=
  c.any (fun lit => evalLitSATPlus Q n lit k)


def evalSATPlus (Q n : ℕ) (F : InstanceSATPlus Q) (k : Fin (Q ^ n)) : Bool :=
  F.all (fun c => evalClauseSATPlus Q n c k)

def T_F_SAT (Q n : ℕ) (F : InstanceSATPlus Q) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ :=
  M0_SAT (evalSATPlus Q n F) * T_SAT Q n * M0_SAT (evalSATPlus Q n F)

def T_F_SAT_mod (Q n p : ℕ) (F : InstanceSATPlus Q) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) (ZMod p) :=
  M0_SAT_mod (evalSATPlus Q n F) p * T_SAT_mod Q n p * M0_SAT_mod (evalSATPlus Q n F) p


def M_m_SAT (Q n : ℕ) (F : InstanceSATPlus Q) (m : ℕ) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ :=
  (T_SAT Q n) ^ m * M0_SAT (evalSATPlus Q n F)

def M_m_SAT_mod (Q n p : ℕ) (F : InstanceSATPlus Q) (m : ℕ) :
  Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) (ZMod p) :=
  (T_SAT_mod Q n p) ^ m * M0_SAT_mod (evalSATPlus Q n F) p

noncomputable def N_eff_SAT (Q n : ℕ) (F : InstanceSATPlus Q) : ℕ :=
  Module.finrank ℂ
    (LinearMap.range (Matrix.toLin' (M0_SAT (evalSATPlus Q n F))))

lemma diag_indicator_mul_self {R : Type*} [Semiring R] (Q n : ℕ) (F : InstanceSATPlus Q) :
    let M : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) R :=
      Matrix.diagonal (fun k : Fin (Q ^ n) => if evalSATPlus Q n F k then (1 : R) else (0 : R))
    M * M = M := by
  intro M
  dsimp [M]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  ext k
  by_cases hk : evalSATPlus Q n F k = true
  · simp [hk]
  · simp [hk]

lemma M0_SAT_mul_self (Q n : ℕ) (F : InstanceSATPlus Q) :
    M0_SAT (evalSATPlus Q n F) * M0_SAT (evalSATPlus Q n F) = M0_SAT (evalSATPlus Q n F) := by
  unfold M0_SAT v_SAT
  exact diag_indicator_mul_self Q n F

lemma M0_SAT_mod_mul_self (Q n p : ℕ) (F : InstanceSATPlus Q) :
    M0_SAT_mod (evalSATPlus Q n F) p * M0_SAT_mod
      (evalSATPlus Q n F) p = M0_SAT_mod (evalSATPlus Q n F) p := by
  unfold M0_SAT_mod
  exact diag_indicator_mul_self Q n F

lemma compressed_diagonal_pow {R : Type*} [CommSemiring R] (Q n : ℕ)
    (d : Fin (Q ^ n) → R) (F : InstanceSATPlus Q) :
    let D : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) R := Matrix.diagonal d
    let P : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) R :=
      Matrix.diagonal (fun k : Fin (Q ^ n) => if evalSATPlus Q n F k then (1 : R) else (0 : R))
    (P * D * P = D * P) ∧
    (∀ m : ℕ, 1 ≤ m → (P * D * P) ^ m = D ^ m * P) ∧
    (∀ m : ℕ, 1 ≤ m → (P * D * P) ^ m * P = (P * D * P) ^ m) := by
  intro D P
  have hPDP : P * D * P = Matrix.diagonal
    (fun k : Fin (Q ^ n) => if evalSATPlus Q n F k then d k else 0) := by
    dsimp [D, P]
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; ext k
    by_cases hk : evalSATPlus Q n F k = true <;> simp [hk]
  have hDP : D * P = Matrix.diagonal (fun k : Fin (Q ^ n) =>
    if evalSATPlus Q n F k then d k else 0) := by
    dsimp [D, P]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1; ext k
    by_cases hk : evalSATPlus Q n F k = true <;> simp [hk]
  have h1 : P * D * P = D * P := hPDP.trans hDP.symm
  have h2 : ∀ m : ℕ, 1 ≤ m → (P * D * P) ^ m = D ^ m * P := by
    intro m hm
    rw [hPDP]
    dsimp [D, P]
    rw [Matrix.diagonal_pow, Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal]
    congr 1; ext k
    by_cases hk : evalSATPlus Q n F k = true
    · simp [hk]
    · have hm0 : m ≠ 0 := by omega
      simp [hk, zero_pow hm0]
  refine ⟨h1, h2, ?_⟩
  intro m hm
  rw [h2 m hm, mul_assoc]
  have hPP : P * P = P := diag_indicator_mul_self Q n F
  rw [hPP]

lemma moment_SAT_compressed_identities (Q n p : ℕ) (F : InstanceSATPlus Q) (m : ℕ) (hm : 1 ≤ m) :
    (T_F_SAT Q n F ^ m = M_m_SAT Q n F m) ∧
    (M_m_SAT Q n F m = T_F_SAT Q n F * M_m_SAT Q n F (m - 1)) ∧
    (M_m_SAT Q n F m = T_F_SAT Q n F ^ m * M0_SAT (evalSATPlus Q n F)) ∧
    (T_F_SAT_mod Q n p F ^ m = M_m_SAT_mod Q n p F m) ∧
    (M_m_SAT_mod Q n p F m = T_F_SAT_mod Q n p F * M_m_SAT_mod Q n p F (m - 1)) ∧
    (M_m_SAT_mod Q n p F m = T_F_SAT_mod Q n p F ^ m * M0_SAT_mod (evalSATPlus Q n F) p) ∧
    (Matrix.trace (M_m_SAT_mod Q n p F m) =
      Matrix.trace (T_F_SAT_mod Q n p F ^ m * M0_SAT_mod (evalSATPlus Q n F) p)) ∧
    (Matrix.trace (T_F_SAT_mod Q n p F ^ m * M0_SAT_mod (evalSATPlus Q n F) p) =
      Matrix.trace (T_F_SAT_mod Q n p F ^ m)) := by
  have hC := compressed_diagonal_pow Q n (fun k : Fin (Q ^ n) => (k.val : ℂ)) F
  have hMod := compressed_diagonal_pow Q n (fun k : Fin (Q ^ n) => (k.val : ZMod p)) F
  have hTF_pow_C : T_F_SAT Q n F ^ m = M_m_SAT Q n F m := by
    unfold T_F_SAT M_m_SAT T_SAT M0_SAT v_SAT
    exact hC.2.1 m hm
  have hRec_C : M_m_SAT Q n F m = T_F_SAT Q n F * M_m_SAT Q n F (m - 1) := by
    unfold M_m_SAT T_F_SAT T_SAT M0_SAT v_SAT
    rw [hC.1]
    have hm_split : m = 1 + (m - 1) := by omega
    conv_lhs => rw [hm_split, pow_add, pow_one]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc]
    have hP_comm : Matrix.diagonal (fun k : Fin (Q ^ n) =>
      if evalSATPlus Q n F k then (1 : ℂ) else (0 : ℂ)) *
        Matrix.diagonal (fun k : Fin (Q ^ n) => (k.val : ℂ)) ^ (m - 1) =
        Matrix.diagonal (fun k : Fin (Q ^ n) => (k.val : ℂ)) ^ (m - 1) *
        Matrix.diagonal (fun k : Fin (Q ^ n) => if evalSATPlus
          Q n F k then (1 : ℂ) else (0 : ℂ)) := by
      rw [Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; ext k; ring
    rw [hP_comm, mul_assoc, diag_indicator_mul_self Q n F]
  have hTF_M0_C : M_m_SAT Q n F m = T_F_SAT Q n F ^ m * M0_SAT (evalSATPlus Q n F) := by
    rw [← hTF_pow_C]
    unfold T_F_SAT T_SAT M0_SAT v_SAT
    exact (hC.2.2 m hm).symm
  have hTF_pow_Mod : T_F_SAT_mod Q n p F ^ m = M_m_SAT_mod Q n p F m := by
    unfold T_F_SAT_mod M_m_SAT_mod T_SAT_mod M0_SAT_mod
    exact hMod.2.1 m hm
  have hRec_Mod : M_m_SAT_mod Q n p F m = T_F_SAT_mod Q n p F * M_m_SAT_mod Q n p F (m - 1) := by
    unfold M_m_SAT_mod T_F_SAT_mod T_SAT_mod M0_SAT_mod
    rw [hMod.1]
    have hm_split : m = 1 + (m - 1) := by omega
    conv_lhs => rw [hm_split, pow_add, pow_one]
    simp only [mul_assoc]
    congr 1
    rw [← mul_assoc]
    have hP_comm : Matrix.diagonal (fun k : Fin (Q ^ n) =>
      if evalSATPlus Q n F k then (1 : ZMod p) else (0 : ZMod p)) *
        Matrix.diagonal (fun k : Fin (Q ^ n) => (k.val : ZMod p)) ^ (m - 1) =
        Matrix.diagonal (fun k : Fin (Q ^ n) => (k.val : ZMod p)) ^ (m - 1) *
        Matrix.diagonal (fun k : Fin (Q ^ n) => if evalSATPlus
          Q n F k then (1 : ZMod p) else (0 : ZMod p)) := by
      rw [Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1; ext k; ring
    rw [hP_comm, mul_assoc, diag_indicator_mul_self Q n F]
  have hTF_M0_Mod : M_m_SAT_mod Q n p F m = T_F_SAT_mod
    Q n p F ^ m * M0_SAT_mod (evalSATPlus Q n F) p := by
    rw [← hTF_pow_Mod]
    unfold T_F_SAT_mod T_SAT_mod M0_SAT_mod
    exact (hMod.2.2 m hm).symm
  refine ⟨hTF_pow_C, hRec_C, hTF_M0_C, hTF_pow_Mod, hRec_Mod, hTF_M0_Mod, ?_, ?_⟩
  · rw [hTF_M0_Mod]
  · rw [← hTF_M0_Mod, hTF_pow_Mod]

lemma trace_M_m_SAT_mod_eq_sum (Q n p : ℕ) (F : InstanceSATPlus Q) (m : ℕ) :
    let Sol := Finset.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true) Finset.univ
    ((∑ k ∈ Sol, ((k : ℕ) : ℤ) ^ m : ℤ) : ZMod p) =
      Matrix.trace (M_m_SAT_mod Q n p F m) := by
  intro Sol
  unfold M_m_SAT_mod T_SAT_mod M0_SAT_mod
  rw [Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  dsimp [Sol]
  rw [Finset.sum_filter]
  push_cast
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : evalSATPlus Q n F k = true <;> simp [hk]

lemma N_eff_SAT_eq_card_solutions (Q n : ℕ) (F : InstanceSATPlus Q) (K : ℕ)
    (hK : (Finset.filter (fun k : Fin (Q ^ n) =>
      evalSATPlus Q n F k = true) Finset.univ).card = K) :
    let P_lin := Matrix.toLin' (M0_SAT (evalSATPlus Q n F))
    (P_lin * P_lin = P_lin) ∧
    (Matrix.trace (M0_SAT (evalSATPlus Q n F)) = (N_eff_SAT Q n F : ℂ)) ∧
    (N_eff_SAT Q n F = K) := by
  intro P_lin
  have hP_idem : P_lin * P_lin = P_lin := by
    dsimp [P_lin]
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, M0_SAT_mul_self Q n F]
  have h_trace_eq_rank : Matrix.trace (M0_SAT (evalSATPlus Q n F)) = (N_eff_SAT Q n F : ℂ) := by
    have h_lin_trace := trace_idempotent_eq_finrank_range P_lin hP_idem
    have h_mat : LinearMap.trace ℂ (Fin (Q ^ n) → ℂ) P_lin =
      Matrix.trace (M0_SAT (evalSATPlus Q n F)) := by
      dsimp [P_lin]
      rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin (Q ^ n))),
          ← Matrix.toLin_eq_toLin', LinearMap.toMatrix_toLin]
    rw [← h_mat]
    exact h_lin_trace
  have h_rank_eq_K : N_eff_SAT Q n F = K := by
    have h_trace_card := (trace_M0_SAT (evalSATPlus Q n F)).2
    rw [hK] at h_trace_card
    have h_cast : (N_eff_SAT Q n F : ℂ) = (K : ℂ) := by
      rw [← h_trace_eq_rank, h_trace_card]
    exact Nat.cast_injective h_cast
  exact ⟨hP_idem, h_trace_eq_rank, h_rank_eq_K⟩

theorem reduction_operatoire_sommes_newton
    (Q n d K r : ℕ) (_ : 1 ≤ n) (_ : 2 ≤ Q)
    (F : InstanceSATPlus Q)
    (hK_card : (Finset.filter (fun k : Fin (Q ^ n) =>
      evalSATPlus Q n F k = true) Finset.univ).card = K)
    (_ : 1 ≤ K ∧ K ≤ d)
    (p : Fin r → ℕ) :
    let Sol := Finset.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true) Finset.univ
    (∀ (i : Fin r) (m : ℕ), m ∈ Finset.Icc 1 K →
      (M_m_SAT Q n F m = T_F_SAT Q n F * M_m_SAT Q n F (m - 1) ∧
       M_m_SAT Q n F m = T_F_SAT Q n F ^ m * M0_SAT (evalSATPlus Q n F) ∧
       T_F_SAT Q n F ^ m = M_m_SAT Q n F m) ∧
      (M_m_SAT_mod Q n (p i) F m = T_F_SAT_mod Q n (p i) F * M_m_SAT_mod Q n (p i) F (m - 1) ∧
       M_m_SAT_mod Q n (p i) F m = T_F_SAT_mod Q n (p i) F ^ m *
        M0_SAT_mod (evalSATPlus Q n F) (p i) ∧
       T_F_SAT_mod Q n (p i) F ^ m = M_m_SAT_mod Q n (p i) F m) ∧
      (let mu_m_int : ℤ := ∑ k ∈ Sol, ((k : ℕ) : ℤ) ^ m
       let mu_m_mod : ZMod (p i) := (mu_m_int : ZMod (p i))
       mu_m_mod = Matrix.trace (M_m_SAT_mod Q n (p i) F m) ∧
       Matrix.trace (M_m_SAT_mod Q n (p i) F m) =
         Matrix.trace (T_F_SAT_mod Q n (p i) F ^ m * M0_SAT_mod (evalSATPlus Q n F) (p i)) ∧
       Matrix.trace (T_F_SAT_mod Q n (p i) F ^ m * M0_SAT_mod (evalSATPlus Q n F) (p i)) =
         Matrix.trace (T_F_SAT_mod Q n (p i) F ^ m))) ∧
    (Matrix.toLin' (M0_SAT (evalSATPlus Q n F)) * Matrix.toLin' (M0_SAT (evalSATPlus Q n F)) =
       Matrix.toLin' (M0_SAT (evalSATPlus Q n F)) ∧
     Matrix.trace (M0_SAT (evalSATPlus Q n F)) = (N_eff_SAT Q n F : ℂ) ∧
     N_eff_SAT Q n F = K) := by
  intro Sol
  refine ⟨?_, ?_⟩
  · intro i m hm_Icc
    have hm : 1 ≤ m := (Finset.mem_Icc.mp hm_Icc).1
    have h_ident := moment_SAT_compressed_identities Q n (p i) F m hm
    rcases h_ident with ⟨hTF_C, hRec_C, hTF_M0_C, hTF_Mod, hRec_Mod, hTF_M0_Mod, hTr1, hTr2⟩
    refine ⟨⟨hRec_C, hTF_M0_C, hTF_C⟩, ⟨hRec_Mod, hTF_M0_Mod, hTF_Mod⟩, ?_⟩
    have h_mu_trace := trace_M_m_SAT_mod_eq_sum Q n (p i) F m
    exact ⟨h_mu_trace, hTr1, hTr2⟩
  · exact N_eff_SAT_eq_card_solutions Q n F K hK_card

---------------------------------------------------------------------------

noncomputable def T_etape2_clos (N_eff K r n : ℕ) (T_vF : ℝ) : ℝ :=
  (N_eff : ℝ) * T_vF + (r : ℝ) * (K : ℝ) * (n : ℝ) + (r : ℝ) * (K : ℝ) ^ 2

noncomputable def T_total_5_etapes
  (N_eff n _sizeF K r w : ℕ) (p_max T_vF : ℝ) : ℝ :=
  -- Étape 1 : O(r^2 * w + r * n)
  ((r : ℝ) ^ 2 * (w : ℝ) + (r : ℝ) * (n : ℝ)) +
  -- Étape 2 close : N_eff * T_vF + r * K * n + r * K^2
  T_etape2_clos N_eff K r n T_vF +
  -- Étape 3 : Newton-Girard O(r * K^2)
  ((r : ℝ) * (K : ℝ) ^ 2) +
  -- Étape 4 : Shoup + Horner (is null if the principal terme K = 1)
  (if 1 < K then (r : ℝ) * ((K : ℝ) ^ 2 + (K : ℝ) *
    Real.sqrt p_max * Real.log p_max) else (r : ℝ)) +
  -- Étape 5 : CRT Garner + base Q : O(K * r^2 + K * r * n)
  ((K : ℝ) * (r : ℝ) ^ 2 + (K : ℝ) * (r : ℝ) * (n : ℝ))

noncomputable def T_clos_bound (n Q sizeF K w : ℕ) (p_max : ℝ) : ℝ :=
  let L : ℝ := (n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)
  (K : ℝ) * ((n : ℝ) + (sizeF : ℝ)) +
  ((K : ℝ) * (n : ℝ) * L + (K : ℝ) * L ^ 2) +
  (if 1 < K then L * ((K : ℝ) ^ 2 + (K : ℝ) *
    Real.sqrt p_max * Real.log p_max) else 0)

noncomputable def T_clos_bound_K1 (n Q sizeF w : ℕ) : ℝ :=
  let L : ℝ := (n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)
  (n : ℝ) + (sizeF : ℝ) + (n : ℝ) * L + L ^ 2

noncomputable def E_clos_model (sizeF K n r : ℕ) : ℝ :=
  (sizeF : ℝ) + (K : ℝ) * (n : ℝ) + (r : ℝ) * (K : ℝ) + (r : ℝ) ^ 2

noncomputable def E_clos_bound (n Q sizeF K w : ℕ) : ℝ :=
  let L : ℝ := (n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)
  (sizeF : ℝ) + (K : ℝ) * (n : ℝ) *
    (1 + Real.logb 2 (Q : ℝ) / (w : ℝ)) + L ^ 2

lemma etape2_clos_substitution_K (Q n K r : ℕ) (F : InstanceSATPlus Q) (T_vF : ℝ)
    (hNeff : N_eff_SAT Q n F = K) :
    T_etape2_clos (N_eff_SAT Q n F) K r n T_vF =
      (K : ℝ) * T_vF + (r : ℝ) * (K : ℝ) * (n : ℝ) + (r : ℝ) * (K : ℝ) ^ 2 := by
  unfold T_etape2_clos
  rw [hNeff]

lemma T_clos_bound_eq_K1 (n Q sizeF w : ℕ) (p_max : ℝ) :
    T_clos_bound n Q sizeF 1 w p_max = T_clos_bound_K1 n Q sizeF w := by
  unfold T_clos_bound T_clos_bound_K1
  simp only [lt_self_iff_false, ↓reduceIte, Nat.cast_one, one_mul, add_zero]
  ring

lemma T_etape1_le (n K r w : ℕ) (L C_r : ℝ)
    (hK : 1 ≤ K) (hw : 1 ≤ w) (hCr : 1 ≤ C_r) (hL : 0 ≤ L)
    (hr : (r : ℝ) ≤ C_r * L) :
    (r : ℝ) ^ 2 * (w : ℝ) + (r : ℝ) * (n : ℝ) ≤
      C_r ^ 2 * (w : ℝ) * ((K : ℝ) * L ^ 2) + C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) := by
  have hK_pos : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hw_pos : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hCrw : C_r ≤ C_r ^ 2 * (w : ℝ) := by nlinarith
  have h1 : (r : ℝ) ^ 2 * (w : ℝ) ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * L ^ 2) := by
    have hr2 : (r : ℝ) ^ 2 ≤ C_r ^ 2 * L ^ 2 := by nlinarith
    have hL2 : L ^ 2 ≤ (K : ℝ) * L ^ 2 := by nlinarith [sq_nonneg L]
    have hCw : 0 ≤ C_r ^ 2 * (w : ℝ) := by positivity
    nlinarith
  have h2 : (r : ℝ) * (n : ℝ) ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) := by
    have hnL : 0 ≤ (n : ℝ) * L := by positivity
    have h_rn : (r : ℝ) * (n : ℝ) ≤ C_r * ((n : ℝ) * L) := by nlinarith
    have h_nL : (n : ℝ) * L ≤ (K : ℝ) * (n : ℝ) * L := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hK_pos hnL
    have h_Cr : C_r * ((n : ℝ) * L) ≤ C_r * ((K : ℝ) * (n : ℝ) * L) :=
      mul_le_mul_of_nonneg_left h_nL (by linarith)
    have h_Crw : C_r * ((K : ℝ) * (n : ℝ) * L) ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) :=
      mul_le_mul_of_nonneg_right hCrw (by positivity)
    linarith
  linarith

lemma T_etape2_clos_le (n sizeF K r w : ℕ) (L T_vF C_r C_v : ℝ)
    (hw : 1 ≤ w) (hCr : 1 ≤ C_r) (hL : 0 ≤ L)
    (hr : (r : ℝ) ≤ C_r * L)
    (hTvF : T_vF ≤ C_v * ((n : ℝ) + (sizeF : ℝ))) :
    T_etape2_clos K K r n T_vF ≤
      C_v * ((K : ℝ) * ((n : ℝ) + (sizeF : ℝ))) +
      C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) +
      (r : ℝ) * (K : ℝ) ^ 2 := by
  unfold T_etape2_clos
  have hw_pos : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hCrw : C_r ≤ C_r ^ 2 * (w : ℝ) := by nlinarith
  have h1 : (K : ℝ) * T_vF ≤ C_v * ((K : ℝ) * ((n : ℝ) + (sizeF : ℝ))) := by
    nlinarith
  have h2 : (r : ℝ) * (K : ℝ) * (n : ℝ) ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) := by
    have ha : (r : ℝ) * (K : ℝ) * (n : ℝ) ≤ C_r * ((K : ℝ) * (n : ℝ) * L) := by
      have hKn : 0 ≤ (K : ℝ) * (n : ℝ) := by positivity
      calc (r : ℝ) * (K : ℝ) * (n : ℝ)
          = (r : ℝ) * ((K : ℝ) * (n : ℝ)) := by ring
        _ ≤ (C_r * L) * ((K : ℝ) * (n : ℝ)) := mul_le_mul_of_nonneg_right hr hKn
        _ = C_r * ((K : ℝ) * (n : ℝ) * L) := by ring
    have hb : C_r * ((K : ℝ) * (n : ℝ) * L) ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) :=
      mul_le_mul_of_nonneg_right hCrw (by positivity)
    linarith
  linarith

lemma T_etape5_le (n K r w : ℕ) (L C_r : ℝ)
    (hw : 1 ≤ w) (hCr : 1 ≤ C_r) (hL : 0 ≤ L)
    (hr : (r : ℝ) ≤ C_r * L) :
    (K : ℝ) * (r : ℝ) ^ 2 + (K : ℝ) * (r : ℝ) * (n : ℝ) ≤
      C_r ^ 2 * (w : ℝ) * ((K : ℝ) * L ^ 2) + C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) := by
  have hw_pos : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hK_nonneg : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have hCr2_w : C_r ^ 2 ≤ C_r ^ 2 * (w : ℝ) := by nlinarith
  have hCrw : C_r ≤ C_r ^ 2 * (w : ℝ) := by nlinarith
  have h1 : (K : ℝ) * (r : ℝ) ^ 2 ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * L ^ 2) := by
    have hr2 : (r : ℝ) ^ 2 ≤ C_r ^ 2 * L ^ 2 := by nlinarith
    have ha : (K : ℝ) * (r : ℝ) ^ 2 ≤ C_r ^ 2 * ((K : ℝ) * L ^ 2) := by
      calc (K : ℝ) * (r : ℝ) ^ 2
          ≤ (K : ℝ) * (C_r ^ 2 * L ^ 2) := mul_le_mul_of_nonneg_left hr2 hK_nonneg
        _ = C_r ^ 2 * ((K : ℝ) * L ^ 2) := by ring
    have hb : C_r ^ 2 * ((K : ℝ) * L ^ 2) ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * L ^ 2) :=
      mul_le_mul_of_nonneg_right hCr2_w (by positivity)
    linarith
  have h2 : (K : ℝ) * (r : ℝ) * (n : ℝ) ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) := by
    have hKn : 0 ≤ (K : ℝ) * (n : ℝ) := by positivity
    have ha : (K : ℝ) * (r : ℝ) * (n : ℝ) ≤ C_r * ((K : ℝ) * (n : ℝ) * L) := by
      calc (K : ℝ) * (r : ℝ) * (n : ℝ)
          = (r : ℝ) * ((K : ℝ) * (n : ℝ)) := by ring
        _ ≤ (C_r * L) * ((K : ℝ) * (n : ℝ)) := mul_le_mul_of_nonneg_right hr hKn
        _ = C_r * ((K : ℝ) * (n : ℝ) * L) := by ring
    have hb : C_r * ((K : ℝ) * (n : ℝ) * L) ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) :=
      mul_le_mul_of_nonneg_right hCrw (by positivity)
    linarith
  linarith

lemma T_total_5_etapes_le_bound
    (n Q sizeF K r w : ℕ) (p_max T_vF C_r C_v : ℝ)
    (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hK : 1 ≤ K) (hw : 1 ≤ w)
    (hCr : 1 ≤ C_r) (hCv : 1 ≤ C_v)
    (hpmax : 1 ≤ p_max)
    (hr : (r : ℝ) ≤ C_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)))
    (hTvF : T_vF ≤ C_v * ((n : ℝ) + (sizeF : ℝ))) :
    T_total_5_etapes K n sizeF K r w p_max T_vF ≤
      (C_v + 6 * C_r ^ 2 * (w : ℝ)) * T_clos_bound n Q sizeF K w p_max := by
  set L : ℝ := (n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)
  have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hw_pos : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  have hQ_ge2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hlogQ : 1 ≤ Real.logb 2 (Q : ℝ) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num : (1 : ℝ) < 2) (by linarith)]
    simpa using hQ_ge2
  have hL_nonneg : 0 ≤ L := by dsimp [L]; positivity
  have hCrw : C_r ≤ C_r ^ 2 * (w : ℝ) := by nlinarith
  have hShoup_nonneg : 0 ≤ (K : ℝ) * Real.sqrt p_max * Real.log p_max := by
    have hlogp : 0 ≤ Real.log p_max := Real.log_nonneg hpmax
    positivity
  have h_e1 := T_etape1_le n K r w L C_r hK hw hCr hL_nonneg hr
  have h_e2 := T_etape2_clos_le n sizeF K r w L T_vF C_r C_v hw hCr hL_nonneg hr hTvF
  have h_e5 := T_etape5_le n K r w L C_r hw hCr hL_nonneg hr
  unfold T_total_5_etapes T_clos_bound
  dsimp only
  change _ ≤ (C_v + 6 * C_r ^ 2 * (w : ℝ)) *
    ((K : ℝ) * ((n : ℝ) + (sizeF : ℝ)) + ((K : ℝ) * (n : ℝ) * L + (K : ℝ) * L ^ 2) +
     if 1 < K then L * ((K : ℝ) ^ 2 + (K : ℝ) * Real.sqrt p_max * Real.log p_max) else 0)
  split_ifs with hK1
  · set S : ℝ := L * ((K : ℝ) ^ 2 + (K : ℝ) * Real.sqrt p_max * Real.log p_max)
    have hS_nonneg : 0 ≤ S := by dsimp [S]; positivity
    have h_rK2 : (r : ℝ) * (K : ℝ) ^ 2 ≤ C_r ^ 2 * (w : ℝ) * S := by
      have h1 : (r : ℝ) * (K : ℝ) ^ 2 ≤ C_r * (L * (K : ℝ) ^ 2) := by
        calc (r : ℝ) * (K : ℝ) ^ 2
            ≤ (C_r * L) * (K : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hr (by positivity)
          _ = C_r * (L * (K : ℝ) ^ 2) := by ring
      have h2 : L * (K : ℝ) ^ 2 ≤ S := by dsimp [S]; nlinarith
      have h3 : C_r * (L * (K : ℝ) ^ 2) ≤ C_r * S := mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : C_r * S ≤ C_r ^ 2 * (w : ℝ) * S := mul_le_mul_of_nonneg_right hCrw hS_nonneg
      linarith
    have h_e4 : (r : ℝ) * ((K : ℝ) ^ 2 + (K : ℝ) * Real.sqrt p_max * Real.log p_max) ≤
        C_r ^ 2 * (w : ℝ) * S := by
      have h1 : (r : ℝ) * ((K : ℝ) ^ 2 + (K : ℝ) * Real.sqrt p_max * Real.log p_max) ≤ C_r * S := by
        have h_pos : 0 ≤ (K : ℝ) ^ 2 + (K : ℝ) * Real.sqrt p_max * Real.log p_max := by positivity
        dsimp [S]; nlinarith
      have h2 : C_r * S ≤ C_r ^ 2 * (w : ℝ) * S := mul_le_mul_of_nonneg_right hCrw hS_nonneg
      linarith
    have h_p1 : 0 ≤ 6 * C_r ^ 2 * (w : ℝ) * ((K : ℝ) * ((n : ℝ) + (sizeF : ℝ))) := by positivity
    have h_p2 : 0 ≤ C_v * ((K : ℝ) * (n : ℝ) * L + (K : ℝ) * L ^ 2) := by positivity
    have h_p3 : 0 ≤ C_v * S := by positivity
    have h_p4 : 0 ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * (n : ℝ) * L) := by positivity
    have h_p5 : 0 ≤ C_r ^ 2 * (w : ℝ) * ((K : ℝ) * L ^ 2) := by positivity
    have h_p6 : 0 ≤ C_r ^ 2 * (w : ℝ) * S := by positivity
    linarith
  · have hK_eq1 : K = 1 := by omega
    subst hK_eq1
    have h_r_le : (r : ℝ) ≤ C_r ^ 2 * (w : ℝ) * ((1 : ℝ) * (n : ℝ) * L) := by
      have h2 : L ≤ (1 : ℝ) * (n : ℝ) * L := by nlinarith
      have h3 : C_r * L ≤ C_r * ((1 : ℝ) * (n : ℝ) * L) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : C_r * ((1 : ℝ) * (n : ℝ) * L) ≤ C_r ^ 2 * (w : ℝ) * ((1 : ℝ) * (n : ℝ) * L) :=
        mul_le_mul_of_nonneg_right hCrw (by positivity)
      linarith
    have h_p1 : 0 ≤ 6 * C_r ^ 2 * (w : ℝ) * ((1 : ℝ) * ((n : ℝ) + (sizeF : ℝ))) := by positivity
    have h_p2 : 0 ≤ C_v * ((1 : ℝ) * (n : ℝ) * L + (1 : ℝ) * L ^ 2) := by positivity
    have h_p4 : 0 ≤ C_r ^ 2 * (w : ℝ) * ((1 : ℝ) * (n : ℝ) * L) := by positivity
    have h_p5 : 0 ≤ C_r ^ 2 * (w : ℝ) * ((1 : ℝ) * L ^ 2) := by positivity
    simp only [Nat.cast_one, one_pow, mul_one, add_zero] at *
    linarith

lemma E_clos_model_theta
    (n Q sizeF K r w : ℕ) (c_r C_r : ℝ)
    (hcr_pos : 0 < c_r) (hcr_le : c_r ≤ 1) (hCr_ge : 1 ≤ C_r)
    (hr_lo : c_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)) ≤ (r : ℝ))
    (hr_hi : (r : ℝ) ≤ C_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ))) :
    c_r ^ 2 * E_clos_bound n Q sizeF K w ≤ E_clos_model sizeF K n r ∧
    E_clos_model sizeF K n r ≤ C_r ^ 2 * E_clos_bound n Q sizeF K w := by
  set L : ℝ := (n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)
  have hL_nonneg : 0 ≤ L := by
    have hr_nonneg : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith
  have h_ident : (K : ℝ) * (n : ℝ) * (1 + Real.logb 2 (Q : ℝ) / (w : ℝ)) =
      (K : ℝ) * (n : ℝ) + (K : ℝ) * L := by
    dsimp [L]; ring
  have hcr2_le_cr : c_r ^ 2 ≤ c_r := by nlinarith
  have hcr2_le_1 : c_r ^ 2 ≤ 1 := by nlinarith
  have h1_le_Cr2 : 1 ≤ C_r ^ 2 := by nlinarith
  have hCr_le_Cr2 : C_r ≤ C_r ^ 2 := by nlinarith
  have hr_nonneg : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have h_r2_lo : c_r ^ 2 * L ^ 2 ≤ (r : ℝ) ^ 2 := by
    have h1 : (c_r * L) ^ 2 ≤ (r : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hr_lo 2
    linarith [show (c_r * L) ^ 2 = c_r ^ 2 * L ^ 2 by ring]
  have h_r2_hi : (r : ℝ) ^ 2 ≤ C_r ^ 2 * L ^ 2 := by
    have h1 : (r : ℝ) ^ 2 ≤ (C_r * L) ^ 2 :=
      pow_le_pow_left₀ hr_nonneg hr_hi 2
    linarith [show (C_r * L) ^ 2 = C_r ^ 2 * L ^ 2 by ring]
  have h_sizeF_nonneg : 0 ≤ (sizeF : ℝ) := Nat.cast_nonneg sizeF
  have h_Kn_nonneg : 0 ≤ (K : ℝ) * (n : ℝ) := by positivity
  have h_KL_nonneg : 0 ≤ (K : ℝ) * L := by positivity
  unfold E_clos_model E_clos_bound
  dsimp only
  rw [h_ident]
  constructor
  · have h1 : c_r ^ 2 * (sizeF : ℝ) ≤ (sizeF : ℝ) := by nlinarith
    have h2 : c_r ^ 2 * ((K : ℝ) * (n : ℝ)) ≤ (K : ℝ) * (n : ℝ) := by nlinarith
    have h3 : c_r ^ 2 * ((K : ℝ) * L) ≤ (r : ℝ) * (K : ℝ) := by nlinarith
    linarith
  · have h1 : (sizeF : ℝ) ≤ C_r ^ 2 * (sizeF : ℝ) := by nlinarith
    have h2 : (K : ℝ) * (n : ℝ) ≤ C_r ^ 2 * ((K : ℝ) * (n : ℝ)) := by nlinarith
    have h3 : (r : ℝ) * (K : ℝ) ≤ C_r ^ 2 * ((K : ℝ) * L) := by nlinarith
    linarith


theorem cloture_algebrique_elimination_Nloc_SAT
    (Q n d K r w sizeF : ℕ)
    (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hw : 1 ≤ w)
    (F : InstanceSATPlus Q)
    (hK_card : (Finset.filter (fun k : Fin (Q ^ n) =>
      evalSATPlus Q n F k = true) Finset.univ).card = K)
    (hK_bounds : 1 ≤ K ∧ K ≤ d)
    (p : Fin r → ℕ)
    (p_max T_vF c_r C_r C_v : ℝ)
    (hpmax : 1 ≤ p_max)
    (hcr_pos : 0 < c_r) (hcr_le : c_r ≤ 1) (hCr_ge : 1 ≤ C_r) (hCv_ge : 1 ≤ C_v)
    (hr_lo : c_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)) ≤ (r : ℝ))
    (hr_hi : (r : ℝ) ≤ C_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)))
    (hTvF : T_vF ≤ C_v * ((n : ℝ) + (sizeF : ℝ))) :
    (N_eff_SAT Q n F = K ∧
     T_etape2_clos (N_eff_SAT Q n F) K r n T_vF =
       (K : ℝ) * T_vF + (r : ℝ) * (K : ℝ) * (n : ℝ) + (r : ℝ) * (K : ℝ) ^ 2 ∧
     (∀ (i : Fin r) (m : ℕ), m ∈ Finset.Icc 1 K →
       M_m_SAT_mod Q n (p i) F m = T_F_SAT_mod Q n (p i) F * M_m_SAT_mod Q n (p i) F (m - 1) ∧
       Matrix.trace (M_m_SAT_mod Q n (p i) F m) = Matrix.trace (T_F_SAT_mod Q n (p i) F ^ m))) ∧
    (T_total_5_etapes (N_eff_SAT Q n F) n sizeF K r w p_max T_vF ≤
       (C_v + 6 * C_r ^ 2 * (w : ℝ)) * T_clos_bound n Q sizeF K w p_max ∧
     T_clos_bound n Q sizeF 1 w p_max = T_clos_bound_K1 n Q sizeF w) ∧
    (c_r ^ 2 * E_clos_bound n Q sizeF K w ≤ E_clos_model sizeF K n r ∧
     E_clos_model sizeF K n r ≤ C_r ^ 2 * E_clos_bound n Q sizeF K w) := by
  have hRed := reduction_operatoire_sommes_newton Q n d K r hn hQ F hK_card hK_bounds p
  have hNeff : N_eff_SAT Q n F = K := hRed.2.2.2
  refine ⟨⟨hNeff, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact etape2_clos_substitution_K Q n K r F T_vF hNeff
  · intro i m hm
    have h_im := hRed.1 i m hm
    exact ⟨h_im.2.1.1, h_im.2.2.2.1.trans h_im.2.2.2.2⟩
  · rw [hNeff]
    exact T_total_5_etapes_le_bound n Q sizeF K r w p_max T_vF C_r C_v
      hn hQ hK_bounds.1 hw hCr_ge hCv_ge hpmax hr_hi hTvF
  · exact T_clos_bound_eq_K1 n Q sizeF w p_max
  · exact E_clos_model_theta n Q sizeF K r w c_r C_r hcr_pos hcr_le hCr_ge hr_lo hr_hi

theorem synthese_cloture_polynomiale_SAT
    (Q n d K sizeF r w : ℕ) (p_max T_vF c_r C_r C_v : ℝ)
    (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hw : 1 ≤ w)
    (hcr_pos : 0 < c_r) (hcr_le : c_r ≤ 1)
    (hCr : 1 ≤ C_r) (hCv : 1 ≤ C_v) (hpmax : 1 ≤ p_max)
    (F : InstanceSATPlus Q)
    (hK_card : (Finset.filter (fun k : Fin (Q ^ n) =>
      evalSATPlus Q n F k = true) Finset.univ).card = K)
    (hK_bounds : 1 ≤ K ∧ K ≤ d)
    (p : Fin r → ℕ)
    (hr_lo : c_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)) ≤ (r : ℝ))
    (hr_hi : (r : ℝ) ≤ C_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)))
    (hTvF : T_vF ≤ C_v * ((n : ℝ) + (sizeF : ℝ))) :
    -- (1)
    (∀ (i : Fin r) (m : ℕ), m ∈ Finset.Icc 1 K →
      (M_m_SAT Q n F m = T_F_SAT Q n F * M_m_SAT Q n F (m - 1) ∧
       M_m_SAT Q n F m = T_F_SAT Q n F ^ m * M0_SAT (evalSATPlus Q n F) ∧
       T_F_SAT Q n F ^ m = M_m_SAT Q n F m) ∧
      (M_m_SAT_mod Q n (p i) F m = T_F_SAT_mod Q n (p i) F * M_m_SAT_mod Q n (p i) F (m - 1) ∧
       M_m_SAT_mod Q n (p i) F m = T_F_SAT_mod Q n (p i) F ^ m *
        M0_SAT_mod (evalSATPlus Q n F) (p i) ∧
       T_F_SAT_mod Q n (p i) F ^ m = M_m_SAT_mod Q n (p i) F m) ∧
      (Matrix.trace (M_m_SAT_mod Q n (p i) F m) =
         Matrix.trace (T_F_SAT_mod Q n (p i) F ^ m * M0_SAT_mod (evalSATPlus Q n F) (p i)) ∧
       Matrix.trace (T_F_SAT_mod Q n (p i) F ^ m * M0_SAT_mod (evalSATPlus Q n F) (p i)) =
         Matrix.trace (T_F_SAT_mod Q n (p i) F ^ m))) ∧
    -- (2)
    (N_eff_SAT Q n F = K) ∧
    -- (3)
    (T_total_5_etapes (N_eff_SAT Q n F) n sizeF K r w p_max T_vF ≤
      (C_v + 6 * C_r ^ 2 * (w : ℝ)) * T_clos_bound n Q sizeF K w p_max) ∧
    -- (4)
    (c_r ^ 2 * E_clos_bound n Q sizeF K w ≤ E_clos_model sizeF K n r ∧
     E_clos_model sizeF K n r ≤ C_r ^ 2 * E_clos_bound n Q sizeF K w) := by
  have h_red := reduction_operatoire_sommes_newton Q n d K r hn hQ F hK_card hK_bounds p
  have hNeff : N_eff_SAT Q n F = K := h_red.2.2.2
  refine ⟨?_, hNeff, ?_, ?_⟩
  · intro i m hm
    have h := h_red.1 i m hm
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  · rw [hNeff]
    exact T_total_5_etapes_le_bound n Q sizeF K r w p_max T_vF C_r C_v
      hn hQ hK_bounds.1 hw hCr hCv hpmax hr_hi hTvF
  · exact E_clos_model_theta n Q sizeF K r w c_r C_r hcr_pos hcr_le hCr hr_lo hr_hi

-- So P = NP

end P_NP
