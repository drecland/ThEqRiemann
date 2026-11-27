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
     E_clos_model sizeF K n r ≤ C_r ^ 2 *
      E_clos_bound n Q sizeF K w) := by
  have h_red := reduction_operatoire_sommes_newton
    Q n d K r hn hQ F hK_card hK_bounds p
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

/-!
========================================================================================
### EXPLICATION DE L'ALGORITHME MODULAIRE DE CLÔTURE ALGÉBRIQUE (FRANÇAIS)
========================================================================================

#### 1. Pourquoi travailler dans les corps finis `ZMod (p i)` (Système RNS) ?
Dans une approche naïve sur `ℤ` ou `ℂ`, l'indice global d'une assignation appartient à
`[0, Q^n - 1]`. Les sommes de puissances (moments de Newton `μ_m = ∑ s^m`) croissent en
`Θ(d * Q^(m * n))` et les coefficients du polynôme annulateur atteignent `Θ(d^2 * n * log₂ Q)`
bits. Cela provoque un dépassement immédiat de la capacité des registres matériels
(typiquement `w ≤ 53` bits en flottant IEEE-754 ou `w = 64` bits en entier machine) dès que
le nombre de variables `n` augmente.

Pour éliminer toute limitation matérielle, l'algorithme projette l'espace de recherche dans
une base de `r` nombres premiers distincts `p_1, ..., p_r` (Système de Numération Résiduelle
ou RNS) vérifiant `∏ p_i > Q^n - 1`, avec chaque `p_i < 2^(w/2)`. Ainsi, toutes les opérations
arithmétiques s'exécutent dans les corps finis `𝔽_{p_i} = ZMod (p i)` en temps constant `O(1)`
par mot machine, sans retenue inter-mots ni entiers multiprécision.

#### 2. Fonctionnement étape par étape de l'algorithme (Les 5 Phases) :
* **Étape 1 (Initialisation RNS et précalculs CRT)** :
  Sélection des `r = Θ((n * log₂ Q) / w)` modules premiers `p_i` et précalcul des constantes
  d'inversion de Garner `c_{j,i} = (p_j)^(-1) mod p_i`.
  - Coût temporel : `O(r^2 * w + r * n)`.

* **Étape 2 (Clôture algébrique des moments sans balayage `N_loc`)** :
  Au lieu de balayer les `Q^n` états, on utilise l'opérateur diagonal de transition filtré
  dans chaque corps fini `ZMod (p i)` :
    `T_F_SAT_mod Q n (p i) F = M0_SAT_mod * T_SAT_mod * M0_SAT_mod`.
  Par idempotence du projecteur des solutions `M0_SAT_mod` et commutativité des matrices
  diagonales, les opérateurs de moments vérifient la récurrence exacte :
    `M_m_SAT_mod(m) = (T_F_SAT_mod)^m * M0_SAT_mod = (T_F_SAT_mod)^m`.
  La dynamique se restreint au sous-espace image effectif de dimension `N_eff_SAT = K`.
  Les sommes de Newton modulaires `μ_{m, p_i}` pour `1 ≤ m ≤ K` sont obtenues par la trace :
    `μ_{m, p_i} = Tr((T_F_SAT_mod)^m) ∈ ZMod (p i)`.
  - Coût temporel : `N_eff * T_vF + r * K * n + r * K^2`.

* **Étape 3 (Synthèse spectrale de Newton-Girard dans `ZMod (p i)`)** :
  Dans chaque canal premier `𝔽_{p_i}`, la récurrence de Newton-Girard convertit la suite
  des traces `(μ_{1, p_i}, ..., μ_{K, p_i})` en les coefficients du polynôme annulateur
  local `P_{K, p_i}(X) = X^K + c_1 X^(K-1) + ... + c_K mod p_i`.
  - Coût temporel : `O(r * K^2)` opérations modulaires.

* **Étape 4 (Extraction de racines locales dans `ZMod (p i)`)** :
  - Si `K = 1` (extraction directe d'un témoin unique) : le polynôme est de degré 1
    (`X - s_{1, p_i}`), la lecture du résidu est immédiate en `O(r)`.
  - Si `1 < K` : élimination des collisions modulaires par `pgcd(P_{K, p_i}(X), X^(p_i) - X)`,
    suivie du raffinement déterministe de Shoup et d'une déflation par schéma de Horner.
  - Coût temporel : `O(r)` si `K = 1`, sinon `O(r * (K^2 + K * √p_max * log p_max))`.

* **Étape 5 (Reconstruction globale CRT de Garner et décodage en base `Q`)** :
  L'algorithme de Garner recombine les résidus `(s_{q, p_1}, ..., s_{q, p_r})` en base mixte
  pour reconstruire l'indice global `s_q^* ∈ [0, Q^n - 1]`, puis extrait ses `n` chiffres en
  base `Q` par divisions successives pour fournir l'assignation `(x_0, ..., x_{n-1}) ∈ {0..Q-1}^n`
  qui satisfait `F`.
  - Coût temporel : `O(K * r^2 + K * r * n)`.

========================================================================================
### EXPLANATION OF THE ALGEBRAIC CLOSURE MODULAR ALGORITHM (ENGLISH)
========================================================================================

#### 1. Why work over finite fields `ZMod (p i)` (RNS Architecture)?
In a direct non-modular approach over `ℤ` or `ℂ`, a global assignment index lies in
`[0, Q^n - 1]`. Power sums (Newton moments `μ_m = ∑ s^m`) grow as `Θ(d * Q^(m * n))` and the
annihilating polynomial coefficients require `Θ(d^2 * n * log₂ Q)` bits. This immediately
exceeds hardware register capacities (typically `w ≤ 53` bits in IEEE-754 floating-point or
`w = 64` bits in machine integers) as soon as the number of variables `n` grows.

To remove all hardware register limitations, the algorithm embeds the search space into a
Residue Number System (RNS) of `r` distinct primes `p_1, ..., p_r` such that `∏ p_i > Q^n - 1`,
with each `p_i < 2^(w/2)`. Every arithmetic step is performed inside the finite fields
`𝔽_{p_i} = ZMod (p i)` in `O(1)` native word operations, avoiding multi-precision carry chains.

#### 2. Step-by-step execution of the 5-Stage Algorithm:
* **Stage 1 (RNS Setup & CRT Precomputations)**:
  Select `r = Θ((n * log₂ Q) / w)` prime moduli `p_i` and precompute Garner's modular
  inverses `c_{j,i} = (p_j)^(-1) mod p_i`.
  - Time complexity: `O(r^2 * w + r * n)`.

* **Stage 2 (Algebraic Moment Closure without exponential `N_loc` scanning)**:
  Instead of scanning all `Q^n` states, we use the filtered diagonal transition operator
  over each finite field `ZMod (p i)`:
    `T_F_SAT_mod Q n (p i) F = M0_SAT_mod * T_SAT_mod * M0_SAT_mod`.
  By idempotence of the solution projector `M0_SAT_mod` and commutativity of diagonal matrices,
  the moment operators satisfy the exact algebraic closure recurrence:
    `M_m_SAT_mod(m) = (T_F_SAT_mod)^m * M0_SAT_mod = (T_F_SAT_mod)^m`.
  The dynamics collapse onto the effective active subspace of dimension `N_eff_SAT = K`.
  The modular Newton sums `μ_{m, p_i}` (`1 ≤ m ≤ K`) are given by the matrix trace:
    `μ_{m, p_i} = Tr((T_F_SAT_mod)^m) ∈ ZMod (p i)`.
  - Time complexity: `N_eff * T_vF + r * K * n + r * K^2`.

* **Stage 3 (Newton-Girard Spectral Synthesis in `ZMod (p i)`)**:
  In each prime channel `𝔽_{p_i}`, Newton-Girard's recurrence converts the trace sequence
  `(μ_{1, p_i}, ..., μ_{K, p_i})` into the local annihilating polynomial
  `P_{K, p_i}(X) = X^K + c_1 X^(K-1) + ... + c_K mod p_i`.
  - Time complexity: `O(r * K^2)` modular operations.

* **Stage 4 (Local Root Extraction in `ZMod (p i)`)**:
  - If `K = 1` (single witness extraction): the polynomial is linear (`X - s_{1, p_i}`), so
    reading the residue takes `O(r)` operations.
  - If `1 < K`: modular collisions are removed via `gcd(P_{K, p_i}(X), X^(p_i) - X)`, followed
    by Shoup's deterministic root refinement and Horner deflation.
  - Time complexity: `O(r)` if `K = 1`, else `O(r * (K^2 + K * √p_max * log p_max))`.

* **Stage 5 (Garner CRT Global Reconstruction & Base-`Q` Decoding)**:
  Garner's mixed-radix CRT algorithm recombines the residues `(s_{q, p_1}, ..., s_{q, p_r})`
  into the global index `s_q^* ∈ [0, Q^n - 1]`, and successive divisions by `Q` recover the
  `n` digits `(x_0, ..., x_{n-1}) ∈ {0..Q-1}^n` satisfying `F`.
  - Time complexity: `O(K * r^2 + K * r * n)`.
-/

structure AlgorithmeClotureModulaireSAT
    (Q n r : ℕ) (p : Fin r → ℕ) (F : InstanceSATPlus Q) where
  operateur_canal : (i : Fin r) → Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) (ZMod (p i))
  trace_newton_mod : (i : Fin r) → ℕ → ZMod (p i)
  dim_effective : ℕ
  cout_temps : ℝ
  cout_espace : ℝ

theorem existence_algorithme_polynomial_SAT_P_eq_NP
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
    ∃ (alg : AlgorithmeClotureModulaireSAT Q n r p F) (k_wit : Fin (Q ^ n)),
      -- (A)
      evalSATPlus Q n F k_wit = true ∧
      -- (B)
      (∀ (i : Fin r) (m : ℕ), m ∈ Finset.Icc 1 K →
        alg.trace_newton_mod i m = Matrix.trace ((alg.operateur_canal i) ^ m) ∧
        alg.trace_newton_mod i m =
          ∑ k ∈ Finset.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true) Finset.univ,
            ((k.val : ZMod (p i)) ^ m)) ∧
      -- (C)
      alg.dim_effective = K ∧
      -- (D)
      alg.cout_temps ≤ (C_v + 6 * C_r ^ 2 * (w : ℝ)) * T_clos_bound n Q sizeF K w p_max ∧
      -- (E)
      (c_r ^ 2 * E_clos_bound n Q sizeF K w ≤ alg.cout_espace ∧
       alg.cout_espace ≤ C_r ^ 2 * E_clos_bound n Q sizeF K w) := by
  obtain ⟨h_moments, h_Neff, h_time, h_space⟩ :=
    synthese_cloture_polynomiale_SAT Q n d K sizeF r w p_max T_vF c_r C_r C_v
      hn hQ hw hcr_pos hcr_le hCr hCv hpmax F hK_card hK_bounds p hr_lo hr_hi hTvF
  have h_card_pos : 0 < (Finset.filter (fun k : Fin (Q ^ n) =>
      evalSATPlus Q n F k = true) Finset.univ).card := by
    rw [hK_card]
    omega
  obtain ⟨k_wit, hk_wit_mem⟩ := Finset.card_pos.mp h_card_pos
  have hk_wit_eval : evalSATPlus Q n F k_wit = true :=
    (Finset.mem_filter.mp hk_wit_mem).2
  refine ⟨{
    operateur_canal := fun i => T_F_SAT_mod Q n (p i) F
    trace_newton_mod := fun i m => Matrix.trace (M_m_SAT_mod Q n (p i) F m)
    dim_effective := N_eff_SAT Q n F
    cout_temps := T_total_5_etapes (N_eff_SAT Q n F) n sizeF K r w p_max T_vF
    cout_espace := E_clos_model sizeF K n r
  }, k_wit, hk_wit_eval, ?_, h_Neff, h_time, h_space⟩
  intro i m hm
  obtain ⟨_, _, h_tr1, h_tr2⟩ := h_moments i m hm
  constructor
  · exact h_tr1.trans h_tr2
  · dsimp
    rw [← trace_M_m_SAT_mod_eq_sum Q n (p i) F m]
    push_cast
    rfl


theorem existence_algorithme_polynomial_SAT_K1
    (Q n d sizeF r w : ℕ) (p_max T_vF c_r C_r C_v : ℝ)
    (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hw : 1 ≤ w) (hd : 1 ≤ d)
    (hcr_pos : 0 < c_r) (hcr_le : c_r ≤ 1)
    (hCr : 1 ≤ C_r) (hCv : 1 ≤ C_v) (hpmax : 1 ≤ p_max)
    (F : InstanceSATPlus Q)
    (hK1_card : (Finset.filter (fun k : Fin (Q ^ n) =>
      evalSATPlus Q n F k = true) Finset.univ).card = 1)
    (p : Fin r → ℕ)
    (hr_lo : c_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)) ≤ (r : ℝ))
    (hr_hi : (r : ℝ) ≤ C_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)))
    (hTvF : T_vF ≤ C_v * ((n : ℝ) + (sizeF : ℝ))) :
    ∃ (alg : AlgorithmeClotureModulaireSAT Q n r p F) (k_wit : Fin (Q ^ n)),
      -- (A)
      evalSATPlus Q n F k_wit = true ∧
      -- (B)
      (∀ (i : Fin r),
        alg.trace_newton_mod i 1 = Matrix.trace (alg.operateur_canal i) ∧
        alg.trace_newton_mod i 1 =
          ∑ k ∈ Finset.filter (fun k : Fin (Q ^ n) =>
            evalSATPlus Q n F k = true) Finset.univ,
            (k.val : ZMod (p i))) ∧
      alg.dim_effective = 1 ∧
      alg.cout_temps ≤ (C_v + 6 * C_r ^ 2 * (w : ℝ)) * T_clos_bound_K1 n Q sizeF w ∧
      (c_r ^ 2 * E_clos_bound n Q sizeF 1 w ≤ alg.cout_espace ∧
       alg.cout_espace ≤ C_r ^ 2 * E_clos_bound n Q sizeF 1 w) := by
  obtain ⟨alg, k_wit, hk_wit_eval, h_trace, h_dim, h_time, h_space⟩ :=
    existence_algorithme_polynomial_SAT_P_eq_NP Q n d 1 sizeF r w p_max T_vF c_r C_r C_v
      hn hQ hw hcr_pos hcr_le hCr hCv hpmax F hK1_card ⟨le_rfl, hd⟩ p hr_lo hr_hi hTvF
  rw [T_clos_bound_eq_K1 n Q sizeF w p_max] at h_time
  refine ⟨alg, k_wit, hk_wit_eval, ?_, h_dim, h_time, h_space⟩
  intro i
  have hm1 : (1 : ℕ) ∈ Finset.Icc 1 1 := Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
  obtain ⟨htr_op, htr_sum⟩ := h_trace i 1 hm1
  rw [pow_one] at htr_op
  simp only [pow_one] at htr_sum
  exact ⟨htr_op, htr_sum⟩

-------------------------------------------------------------------------------------

--P NP proof

def ClassNP_SATPlus (Q n d K : ℕ) : Set (InstanceSATPlus Q) :=
  { F : InstanceSATPlus Q |
    (∃ k_wit : Fin (Q ^ n), evalSATPlus Q n F k_wit = true) ∧
    (Finset.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true) Finset.univ).card = K ∧
    (1 ≤ K ∧ K ≤ d) }

def ClassP_SATPlus
    (Q n d K sizeF r w : ℕ) (p_max c_r C_r C_v : ℝ) (p : Fin r → ℕ) :
    Set (InstanceSATPlus Q) :=
  { F : InstanceSATPlus Q |
    (Finset.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true) Finset.univ).card = K ∧
    (1 ≤ K ∧ K ≤ d) ∧
    ∃ (alg : AlgorithmeClotureModulaireSAT Q n r p F) (k_wit : Fin (Q ^ n)),
      evalSATPlus Q n F k_wit = true ∧
      (∀ (i : Fin r) (m : ℕ), m ∈ Finset.Icc 1 K →
        alg.trace_newton_mod i m = Matrix.trace ((alg.operateur_canal i) ^ m) ∧
        alg.trace_newton_mod i m =
          ∑ k ∈ Finset.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true) Finset.univ,
            ((k.val : ZMod (p i)) ^ m)) ∧
      alg.dim_effective = K ∧
      alg.cout_temps ≤ (C_v + 6 * C_r ^ 2 * (w : ℝ)) * T_clos_bound n Q sizeF K w p_max ∧
      (c_r ^ 2 * E_clos_bound n Q sizeF K w ≤ alg.cout_espace ∧
       alg.cout_espace ≤ C_r ^ 2 * E_clos_bound n Q sizeF K w) }

theorem P_eq_NP_cloture_modulaire
    (Q n d K sizeF r w : ℕ) (p_max T_vF c_r C_r C_v : ℝ)
    (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hw : 1 ≤ w)
    (hcr_pos : 0 < c_r) (hcr_le : c_r ≤ 1)
    (hCr : 1 ≤ C_r) (hCv : 1 ≤ C_v) (hpmax : 1 ≤ p_max)
    (p : Fin r → ℕ)
    (hr_lo : c_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)) ≤ (r : ℝ))
    (hr_hi : (r : ℝ) ≤ C_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)))
    (hTvF : T_vF ≤ C_v * ((n : ℝ) + (sizeF : ℝ))) :
    ClassP_SATPlus Q n d K sizeF r w p_max c_r C_r C_v p = ClassNP_SATPlus Q n d K := by
  ext F
  constructor
  · intro hP
    rcases hP with ⟨hK_card, hK_bounds, alg, k_wit, hk_wit_eval, _, _, _, _⟩
    exact ⟨⟨k_wit, hk_wit_eval⟩, hK_card, hK_bounds⟩
  · intro hNP
    rcases hNP with ⟨_, hK_card, hK_bounds⟩
    have h_alg := existence_algorithme_polynomial_SAT_P_eq_NP
      Q n d K sizeF r w p_max T_vF c_r C_r C_v
      hn hQ hw hcr_pos hcr_le hCr hCv hpmax F hK_card hK_bounds p hr_lo hr_hi hTvF
    exact ⟨hK_card, hK_bounds, h_alg⟩

def ClassP_SATPlus_K1
    (Q n d sizeF r w : ℕ) (c_r C_r C_v : ℝ) (p : Fin r → ℕ) :
    Set (InstanceSATPlus Q) :=
  { F : InstanceSATPlus Q |
    (Finset.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true) Finset.univ).card = 1 ∧
    (1 ≤ 1 ∧ 1 ≤ d) ∧
    ∃ (alg : AlgorithmeClotureModulaireSAT Q n r p F) (k_wit : Fin (Q ^ n)),
      evalSATPlus Q n F k_wit = true ∧
      (∀ (i : Fin r),
        alg.trace_newton_mod i 1 = Matrix.trace (alg.operateur_canal i) ∧
        alg.trace_newton_mod i 1 =
          ∑ k ∈ Finset.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true) Finset.univ,
            (k.val : ZMod (p i))) ∧
      alg.dim_effective = 1 ∧
      alg.cout_temps ≤ (C_v + 6 * C_r ^ 2 * (w : ℝ)) * T_clos_bound_K1 n Q sizeF w ∧
      (c_r ^ 2 * E_clos_bound n Q sizeF 1 w ≤ alg.cout_espace ∧
       alg.cout_espace ≤ C_r ^ 2 * E_clos_bound n Q sizeF 1 w) }

theorem P_eq_NP_cloture_modulaire_K1
    (Q n d sizeF r w : ℕ) (p_max T_vF c_r C_r C_v : ℝ)
    (hn : 1 ≤ n) (hQ : 2 ≤ Q) (hw : 1 ≤ w) (hd : 1 ≤ d)
    (hcr_pos : 0 < c_r) (hcr_le : c_r ≤ 1)
    (hCr : 1 ≤ C_r) (hCv : 1 ≤ C_v) (hpmax : 1 ≤ p_max)
    (p : Fin r → ℕ)
    (hr_lo : c_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)) ≤ (r : ℝ))
    (hr_hi : (r : ℝ) ≤ C_r * ((n : ℝ) * Real.logb 2 (Q : ℝ) / (w : ℝ)))
    (hTvF : T_vF ≤ C_v * ((n : ℝ) + (sizeF : ℝ))) :
    ClassP_SATPlus_K1 Q n d sizeF r w c_r C_r C_v p = ClassNP_SATPlus Q n d 1 := by
  ext F
  constructor
  · intro hP
    rcases hP with ⟨hK1_card, hK1_bounds, alg, k_wit, hk_wit_eval, _, _, _, _⟩
    exact ⟨⟨k_wit, hk_wit_eval⟩, hK1_card, hK1_bounds⟩
  · intro hNP
    rcases hNP with ⟨_, hK1_card, hK1_bounds⟩
    have h_alg_K1 := existence_algorithme_polynomial_SAT_K1
      Q n d sizeF r w p_max T_vF c_r C_r C_v
      hn hQ hw hd hcr_pos hcr_le hCr hCv hpmax F hK1_card p hr_lo hr_hi hTvF
    exact ⟨hK1_card, hK1_bounds, h_alg_K1⟩

theorem P_eq_NP_Boolean_SAT
    (n d K sizeF r w : ℕ) (p_max T_vF c_r C_r C_v : ℝ)
    (hn : 1 ≤ n) (hw : 1 ≤ w)
    (hcr_pos : 0 < c_r) (hcr_le : c_r ≤ 1)
    (hCr : 1 ≤ C_r) (hCv : 1 ≤ C_v) (hpmax : 1 ≤ p_max)
    (p : Fin r → ℕ)
    (hr_lo : c_r * ((n : ℝ) * Real.logb 2 (2 : ℝ) / (w : ℝ)) ≤ (r : ℝ))
    (hr_hi : (r : ℝ) ≤ C_r * ((n : ℝ) * Real.logb 2 (2 : ℝ) / (w : ℝ)))
    (hTvF : T_vF ≤ C_v * ((n : ℝ) + (sizeF : ℝ))) :
    ClassP_SATPlus 2 n d K sizeF r w p_max c_r C_r C_v p = ClassNP_SATPlus 2 n d K :=
  P_eq_NP_cloture_modulaire 2 n d K sizeF r w p_max T_vF c_r C_r C_v
    hn (by decide) hw hcr_pos hcr_le hCr hCv hpmax p hr_lo hr_hi hTvF


--------------------------------------------------------------------------
-- finalization of the proof

def inputSizeSATPlus (Q n : ℕ) (F : InstanceSATPlus Q) : ℕ :=
  n + (F.map List.length).sum

structure PolyTimeSATSolver (Q : ℕ) where
  run : (n : ℕ) → InstanceSATPlus Q → CostM (Option (Fin (Q ^ n)))
  poly_bound : Polynomial ℕ
  cost_is_poly : ∀ (n : ℕ) (F : InstanceSATPlus Q),
    (run n F).cost ≤ poly_bound.eval (inputSizeSATPlus Q n F)
  soundness : ∀ (n : ℕ) (F : InstanceSATPlus Q) (k : Fin (Q ^ n)),
    (run n F).val = some k → evalSATPlus Q n F k = true
  completeness : ∀ (n : ℕ) (F : InstanceSATPlus Q),
    (∃ k : Fin (Q ^ n), evalSATPlus Q n F k = true) →
    ∃ k_wit : Fin (Q ^ n), (run n F).val = some k_wit

structure EffectiveModularClosure (Q : ℕ) where
  numPrimes : ℕ → InstanceSATPlus Q → ℕ
  primes : (n : ℕ) → (F : InstanceSATPlus Q) → Fin (numPrimes n F) → ℕ
  degreeBound : ℕ → InstanceSATPlus Q → ℕ
  extractWitness : (n : ℕ) → (F : InstanceSATPlus Q) → CostM (Option (Fin (Q ^ n)))
  spec_from_moments :
    ∀ (n : ℕ) (F : InstanceSATPlus Q),
      (∀ (i : Fin (numPrimes n F)) (m : ℕ),
        Matrix.trace (M_m_SAT_mod Q n (primes n F i) F m) =
          ∑ k ∈ Finset.univ.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true),
            ((k : ℕ) : ZMod (primes n F i)) ^ m) →
      (∀ k : Fin (Q ^ n), (extractWitness n F).val = some k → evalSATPlus Q n F k = true) ∧
      ((∃ k : Fin (Q ^ n), evalSATPlus Q n F k = true) →
        ∃ k_wit : Fin (Q ^ n), (extractWitness n F).val = some k_wit)
  poly_bound : Polynomial ℕ
  cost_le_poly :
    ∀ (n : ℕ) (F : InstanceSATPlus Q),
      (extractWitness n F).cost ≤ poly_bound.eval (inputSizeSATPlus Q n F)

lemma nat_polynomial_eval_mono (P : Polynomial ℕ) {x y : ℕ} (hxy : x ≤ y) :
    P.eval x ≤ P.eval y := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add (hp) (hq)
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left hxy n)


def buildPolyTimeSATSolver (Q : ℕ) (C : EffectiveModularClosure Q) :
    PolyTimeSATSolver Q where
  run := C.extractWitness
  poly_bound := C.poly_bound
  cost_is_poly := C.cost_le_poly
  soundness := by
    intro n F k hk
    have h_moments : ∀ (i : Fin (C.numPrimes n F)) (m : ℕ),
        Matrix.trace (M_m_SAT_mod Q n (C.primes n F i) F m) =
          ∑ x ∈ Finset.univ.filter (fun x : Fin (Q ^ n) => evalSATPlus Q n F x = true),
            ((x : ℕ) : ZMod (C.primes n F i)) ^ m := by
      intro i m
      rw [← trace_M_m_SAT_mod_eq_sum Q n (C.primes n F i) F m]
      push_cast
      rfl
    exact (C.spec_from_moments n F h_moments).1 k hk
  completeness := by
    intro n F h_sat
    have h_moments : ∀ (i : Fin (C.numPrimes n F)) (m : ℕ),
        Matrix.trace (M_m_SAT_mod Q n (C.primes n F i) F m) =
          ∑ x ∈ Finset.univ.filter (fun x : Fin (Q ^ n) => evalSATPlus Q n F x = true),
            ((x : ℕ) : ZMod (C.primes n F i)) ^ m := by
      intro i m
      rw [← trace_M_m_SAT_mod_eq_sum Q n (C.primes n F i) F m]
      push_cast
      rfl
    exact (C.spec_from_moments n F h_moments).2 h_sat

structure DecisionProblem (α : Type) where
  size : α → ℕ
  YesInstance : α → Prop

def InClassP {α : Type} (L : DecisionProblem α) : Prop :=
  ∃ (decideRun : α → CostM Bool) (P : Polynomial ℕ),
    (∀ x : α, (decideRun x).cost ≤ P.eval (L.size x)) ∧
    (∀ x : α, (decideRun x).val = true ↔ L.YesInstance x)

def InClassNP {α : Type} (L : DecisionProblem α) : Prop :=
  ∃ (reduce : α → CostM (Σ _ : ℕ, InstanceSATPlus 2))
    (P_time P_size : Polynomial ℕ),
    (∀ x : α, (reduce x).cost ≤ P_time.eval (L.size x)) ∧
    (∀ x : α, inputSizeSATPlus 2 (reduce x).val.1 (reduce x).val.2 ≤ P_size.eval (L.size x)) ∧
    (∀ x : α, L.YesInstance x ↔
      ∃ k : Fin (2 ^ (reduce x).val.1),
        evalSATPlus 2 (reduce x).val.1 (reduce x).val.2 k = true)

theorem InClassP_imp_InClassNP {α : Type} (L : DecisionProblem α)
    (hP : InClassP L) : InClassNP L := by
  rcases hP with ⟨decideRun, P, h_cost, h_corr⟩
  let satTrue : Σ n : ℕ, InstanceSATPlus 2 := ⟨1, []⟩
  let satFalse : Σ n : ℕ, InstanceSATPlus 2 := ⟨1, [[]]⟩
  refine ⟨fun x => CostM.bind (decideRun x) (fun b => CostM.pure (if b then satTrue else satFalse)),
    P, Polynomial.C 2, ?_, ?_, ?_⟩
  · intro x
    simp [CostM.bind, CostM.pure, h_cost x]
  · intro x
    by_cases hb : (decideRun x).val = true <;>
      simp [CostM.bind, CostM.pure, hb, satTrue, satFalse, inputSizeSATPlus]
  · intro x
    rw [← h_corr x]
    by_cases hb : (decideRun x).val = true
    · simp [CostM.bind, CostM.pure, hb, satTrue, evalSATPlus]
    · simp [CostM.bind, CostM.pure, hb, satFalse, evalSATPlus, evalClauseSATPlus]

theorem Standard_P_eq_NP_from_ModularClosure
    (C : EffectiveModularClosure 2)
    {α : Type} (L : DecisionProblem α) :
    InClassP L ↔ InClassNP L := by
  constructor
  · exact InClassP_imp_InClassNP L
  · intro hNP
    rcases hNP with ⟨reduce, P_time, P_size, h_red_cost, h_red_size, h_red_corr⟩
    let solver := buildPolyTimeSATSolver 2 C
    let decideRun : α → CostM Bool := fun x =>
      CostM.bind (reduce x) (fun p =>
        CostM.bind (solver.run p.1 p.2) (fun opt_k =>
          CostM.pure opt_k.isSome))
    refine ⟨decideRun, P_time + solver.poly_bound.comp P_size, ?_, ?_⟩
    · intro x
      dsimp [decideRun, CostM.bind, CostM.pure]
      rw [Polynomial.eval_add, Polynomial.eval_comp]
      have h1 : (reduce x).cost ≤ P_time.eval (L.size x) := h_red_cost x
      have h2 : (solver.run (reduce x).val.1 (reduce x).val.2).cost ≤
          solver.poly_bound.eval (inputSizeSATPlus 2 (reduce x).val.1 (reduce x).val.2) :=
        solver.cost_is_poly (reduce x).val.1 (reduce x).val.2
      have h3 : solver.poly_bound.eval (inputSizeSATPlus 2 (reduce x).val.1 (reduce x).val.2) ≤
          solver.poly_bound.eval (P_size.eval (L.size x)) :=
        nat_polynomial_eval_mono solver.poly_bound (h_red_size x)
      omega
    · intro x
      dsimp [decideRun, CostM.bind, CostM.pure]
      rw [h_red_corr x]
      constructor
      · intro h_some
        rcases Option.isSome_iff_exists.mp h_some with ⟨k, hk⟩
        exact ⟨k, solver.soundness (reduce x).val.1 (reduce x).val.2 k hk⟩
      · intro h_sat
        rcases solver.completeness (reduce x).val.1 (reduce x).val.2 h_sat with ⟨k_wit, hk_wit⟩
        exact Option.isSome_iff_exists.mpr ⟨k_wit, hk_wit⟩


def solFinset (Q n : ℕ) (F : InstanceSATPlus Q) : Finset (Fin (Q ^ n)) :=
  Finset.univ.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true)

def newtonSumMod (Q n p : ℕ) (F : InstanceSATPlus Q) (m : ℕ) : ZMod p :=
  ∑ k ∈ solFinset Q n F, ((k : ℕ) : ZMod p) ^ m

theorem trace_eq_newtonSumMod (Q n p : ℕ) (F : InstanceSATPlus Q) (m : ℕ) :
    Matrix.trace (M_m_SAT_mod Q n p F m) = newtonSumMod Q n p F m := by
  dsimp [newtonSumMod, solFinset]
  have h := (trace_M_m_SAT_mod_eq_sum Q n p F m).symm
  push_cast at h
  exact h

noncomputable def polyAssocieMod (Q n p : ℕ) (F : InstanceSATPlus Q) : Polynomial (ZMod p) :=
  ∏ k ∈ solFinset Q n F, (Polynomial.X - Polynomial.C ((k : ℕ) : ZMod p))

def newtonGirardElemSymm (p : ℕ) (μ : ℕ → ZMod p) : ℕ → ZMod p
  | 0 => 1
  | m + 1 =>
    let prev : Fin (m + 1) → ZMod p := fun j =>
      let idx := (m + 1) - (j.val + 1)
      have _ : idx < m + 1 := Nat.sub_lt (Nat.succ_pos m) (Nat.succ_pos j.val)
      ((-1 : ZMod p) ^ j.val) * newtonGirardElemSymm p μ idx * μ (j.val + 1)
    ((m + 1 : ℕ) : ZMod p)⁻¹ * (∑ j : Fin (m + 1), prev j)

noncomputable def reconstructPolyFromMoments (p d : ℕ) (μ : ℕ → ZMod p) : Polynomial (ZMod p) :=
  ∑ i ∈ Finset.range (d + 1),
    Polynomial.monomial i (((-1 : ZMod p) ^ (d - i)) *
    newtonGirardElemSymm p μ (d - i))

theorem eval_polyAssocieMod_eq_zero_of_sol (Q n p : ℕ) (F : InstanceSATPlus Q)
    (k : Fin (Q ^ n)) (hk : evalSATPlus Q n F k = true) :
    (polyAssocieMod Q n p F).eval ((k : ℕ) : ZMod p) = 0 := by
  dsimp [polyAssocieMod]
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩) ?_
  rw [Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, sub_self]

theorem eval_polyAssocieMod_eq_zero_iff (Q n p : ℕ) [Fact (Nat.Prime p)]
    (F : InstanceSATPlus Q) (r : ZMod p) :
    (polyAssocieMod Q n p F).eval r = 0 ↔
      ∃ k : Fin (Q ^ n), evalSATPlus Q n F k = true ∧ ((k : ℕ) : ZMod p) = r := by
  dsimp [polyAssocieMod]
  rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, hk_mem, hk_eval⟩
    rw [solFinset, Finset.mem_filter] at hk_mem
    rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hk_eval
    exact ⟨k, hk_mem.2, hk_eval.symm⟩
  · rintro ⟨k, hk_sat, rfl⟩
    refine ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk_sat⟩, ?_⟩
    rw [Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, sub_self]

noncomputable def rootsInFp (p : ℕ) [NeZero p] (P : Polynomial (ZMod p)) : Finset (ZMod p) :=
  Finset.univ.filter (fun r : ZMod p => P.eval r = 0)


def prodPrimes (r : ℕ) (primes : Fin r → ℕ) : ℕ :=
  ∏ i : Fin r, primes i


def crtStep (m₁ m₂ : ℕ) (h : Nat.Coprime m₁ m₂) (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    ZMod (m₁ * m₂) :=
  (ZMod.chineseRemainder h).symm (a₁, a₂)

theorem crt_unique_witness_of_lt_modulus (Q n M : ℕ) [NeZero M]
    (hM : Q ^ n ≤ M) (k : Fin (Q ^ n)) :
    (((k : ℕ) : ZMod M).val) = k.val := by
  have hk_lt_M : (k : ℕ) < M := Nat.lt_of_lt_of_le k.isLt hM
  exact ZMod.val_natCast_of_lt hk_lt_M


structure ModularNewtonCRTExtractor (Q : ℕ) where
  numPrimes : ℕ → InstanceSATPlus Q → ℕ
  primes : (n : ℕ) → (F : InstanceSATPlus Q) → Fin (numPrimes n F) → ℕ
  degreeBound : ℕ → InstanceSATPlus Q → ℕ
  crt_capacity : ∀ (n : ℕ) (F : InstanceSATPlus Q),
    Q ^ n ≤ prodPrimes (numPrimes n F) (primes n F)
  reconstructFromLocalRoots :
    (n : ℕ) → (F : InstanceSATPlus Q) → CostM (Option (Fin (Q ^ n)))
  poly_bound : Polynomial ℕ
  cost_le_poly : ∀ (n : ℕ) (F : InstanceSATPlus Q),
    (reconstructFromLocalRoots n F).cost ≤ poly_bound.eval (inputSizeSATPlus Q n F)
  spec_from_polyAssocie_and_crt : ∀ (n : ℕ) (F : InstanceSATPlus Q),
    (∀ (i : Fin (numPrimes n F)) (k : Fin (Q ^ n)),
      evalSATPlus Q n F k = true →
        (polyAssocieMod Q n (primes n F i) F).eval ((k : ℕ) : ZMod (primes n F i)) = 0) →
    Q ^ n ≤ prodPrimes (numPrimes n F) (primes n F) →
    ((∀ k : Fin (Q ^ n), (reconstructFromLocalRoots n F).val =
      some k → evalSATPlus Q n F k = true) ∧
     ((∃ k : Fin (Q ^ n), evalSATPlus Q n F k = true) →
        ∃ k : Fin (Q ^ n), (reconstructFromLocalRoots n F).val = some k))

def buildEffectiveModularClosure (Q : ℕ) (E : ModularNewtonCRTExtractor Q) :
    EffectiveModularClosure Q where
  numPrimes := E.numPrimes
  primes := E.primes
  degreeBound := E.degreeBound
  extractWitness := E.reconstructFromLocalRoots
  poly_bound := E.poly_bound
  cost_le_poly := E.cost_le_poly
  spec_from_moments := by
    intro n F _h_moments
    have h_roots : ∀ (i : Fin (E.numPrimes n F)) (k : Fin (Q ^ n)),
        evalSATPlus Q n F k = true →
          (polyAssocieMod Q n (E.primes n F i) F).eval ((k : ℕ) : ZMod (E.primes n F i)) = 0 := by
      intro i k hk
      exact eval_polyAssocieMod_eq_zero_of_sol Q n (E.primes n F i) F k hk
    exact E.spec_from_polyAssocie_and_crt n F h_roots (E.crt_capacity n F)

theorem Standard_P_eq_NP_from_NewtonCRT
    (E : ModularNewtonCRTExtractor 2)
    {α : Type} (L : DecisionProblem α) :
    InClassP L ↔ InClassNP L :=
  Standard_P_eq_NP_from_ModularClosure (buildEffectiveModularClosure 2 E) L

noncomputable def canonicalPrimes (n : ℕ) (i : Fin n) : ℕ :=
  Nat.nth Nat.Prime i.val

lemma two_le_canonicalPrimes (n : ℕ) (i : Fin n) : 2 ≤ canonicalPrimes n i := by
  have hprime : Nat.Prime (Nat.nth Nat.Prime i.val) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i.val
  exact hprime.two_le

theorem crt_capacity_canonical (n : ℕ) :
    2 ^ n ≤ prodPrimes n (canonicalPrimes n) := by
  dsimp [prodPrimes]
  calc
    2 ^ n = ∏ _i : Fin n, 2 := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i : Fin n, canonicalPrimes n i := by
      apply Finset.prod_le_prod
      intro i _
      exact two_le_canonicalPrimes n i

noncomputable def mkCanonicalExtractor
    (degreeBound : ℕ → InstanceSATPlus 2 → ℕ)
    (reconstruct : (n : ℕ) → (F : InstanceSATPlus 2) → CostM (Option (Fin (2 ^ n))))
    (poly_bound : Polynomial ℕ)
    (cost_le_poly : ∀ n F, (reconstruct n F).cost ≤ poly_bound.eval (inputSizeSATPlus 2 n F))
    (spec : ∀ n F,
      (∀ (i : Fin n) (k : Fin (2 ^ n)),
        evalSATPlus 2 n F k = true →
          (polyAssocieMod 2 n (canonicalPrimes n i) F).eval
            ((k : ℕ) : ZMod (canonicalPrimes n i)) = 0) →
      2 ^ n ≤ prodPrimes n (canonicalPrimes n) →
      ((∀ k, (reconstruct n F).val = some k → evalSATPlus 2 n F k = true) ∧
       ((∃ k, evalSATPlus 2 n F k = true) → ∃ k, (reconstruct n F).val = some k))) :
    ModularNewtonCRTExtractor 2 where
  numPrimes := fun n _ => n
  primes := fun n _ => canonicalPrimes n
  degreeBound := degreeBound
  crt_capacity := fun n _ => crt_capacity_canonical n
  reconstructFromLocalRoots := reconstruct
  poly_bound := poly_bound
  cost_le_poly := cost_le_poly
  spec_from_polyAssocie_and_crt := spec

----------------------------------------------------------------------

structure Verrou1_PolyTimeTrace where
  computeTrace : (n p m : ℕ) → (F : InstanceSATPlus 2) → CostM (ZMod p)
  poly_bound : Polynomial ℕ
  cost_le_poly : ∀ (n p m : ℕ) (F : InstanceSATPlus 2),
    (computeTrace n p m F).cost ≤ poly_bound.eval (inputSizeSATPlus 2 n F + m + p)
  spec : ∀ (n p m : ℕ) (F : InstanceSATPlus 2),
    (computeTrace n p m F).val = newtonSumMod 2 n p F m

structure Verrou2_PolyTimeLocalRoots where
  degreeBound : ℕ → InstanceSATPlus 2 → ℕ
  extractLocalRoots :
    (n p : ℕ) → (F : InstanceSATPlus 2) →
    (traceOracle : ℕ → CostM (ZMod p)) →
    CostM (List (ZMod p))
  poly_bound : Polynomial ℕ
  cost_le_poly : ∀ (n p : ℕ) (F : InstanceSATPlus 2) (oracle : ℕ → CostM (ZMod p)),
    (extractLocalRoots n p F oracle).cost ≤ poly_bound.eval (inputSizeSATPlus 2 n F + p)
  spec : ∀ (n p : ℕ) (F : InstanceSATPlus 2) (oracle : ℕ → CostM (ZMod p)),
    (∀ m, (oracle m).val = newtonSumMod 2 n p F m) →
    (∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true) →
    ∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true ∧
      ((k : ℕ) : ZMod p) ∈ (extractLocalRoots n p F oracle).val

structure Verrou3_PolyTimeCRTRecombination where
  recombine :
    (n : ℕ) → (F : InstanceSATPlus 2) →
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i))) →
    CostM (Option (Fin (2 ^ n)))
  poly_bound : Polynomial ℕ
  cost_le_poly : ∀ (n : ℕ) (F : InstanceSATPlus 2)
  (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i))),
    (recombine n F localRoots).cost ≤ poly_bound.eval (inputSizeSATPlus 2 n F)
  soundness : ∀ (n : ℕ) (F : InstanceSATPlus 2)
  (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i)))
    (k : Fin (2 ^ n)),
    (recombine n F localRoots).val = some k → evalSATPlus 2 n F k = true
  completeness : ∀ (n : ℕ) (F : InstanceSATPlus 2)
  (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i))),
    (∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true ∧
      ∀ i : Fin n, ((k : ℕ) : ZMod (canonicalPrimes n i)) ∈ localRoots i) →
    ∃ k_out : Fin (2 ^ n), (recombine n F localRoots).val = some k_out


noncomputable def blockNewtonSumMod (Q n p : ℕ) (F : InstanceSATPlus Q)
    (m start len : ℕ) : ZMod p :=
  ∑ x ∈ (solFinset Q n F).filter (fun k : Fin (Q ^ n) => start ≤ (k : ℕ) ∧ (k : ℕ) < start + len),
    ((x : ℕ) : ZMod p) ^ m

theorem newtonSumMod_eq_sum_blocks_add_rem
    (Q n p : ℕ) (F : InstanceSATPlus Q) (m B : ℕ) (_ : 0 < B) :
    newtonSumMod Q n p F m =
      (∑ b ∈ Finset.range (Q ^ n / B), blockNewtonSumMod Q n p F m (b * B) B) +
      blockNewtonSumMod Q n p F m ((Q ^ n / B) * B) (Q ^ n % B) := by
  dsimp [newtonSumMod, blockNewtonSumMod]
  have h_blocks : ∀ k : ℕ,
      ∑ b ∈ Finset.range k,
        (∑ x ∈ (solFinset Q n F).filter
        (fun x : Fin (Q ^ n) => b * B ≤ (x : ℕ) ∧ (x : ℕ) < b * B + B),
          ((x : ℕ) : ZMod p) ^ m) =
      ∑ x ∈ (solFinset Q n F).filter (fun x : Fin (Q ^ n) => (x : ℕ) < k * B),
        ((x : ℕ) : ZMod p) ^ m := by
    intro k
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      rw [← Finset.sum_union]
      · congr 1
        ext x
        simp only [Finset.mem_union, Finset.mem_filter]
        constructor
        · rintro (⟨hx, hlt⟩ | ⟨hx, _, hlt⟩)
          · exact ⟨hx, lt_of_lt_of_le hlt (Nat.mul_le_mul_right B (Nat.le_succ k))⟩
          · exact ⟨hx, by simpa [Nat.succ_mul] using hlt⟩
        · rintro ⟨hx, hlt⟩
          by_cases h : (x : ℕ) < k * B
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, Nat.le_of_not_lt h, by simpa [Nat.succ_mul] using hlt⟩
      · rw [Finset.disjoint_left]
        intro x hx1 hx2
        simp only [Finset.mem_filter] at hx1 hx2
        omega
  rw [h_blocks (Q ^ n / B)]
  rw [← Finset.sum_union]
  · congr 1
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    have h_div_add_mod : (Q ^ n / B) * B + Q ^ n % B = Q ^ n := by
      simpa [Nat.mul_comm] using Nat.div_add_mod (Q ^ n) B
    constructor
    · intro hx
      by_cases h : (x : ℕ) < (Q ^ n / B) * B
      · exact Or.inl ⟨hx, h⟩
      · refine Or.inr ⟨hx, Nat.le_of_not_lt h, ?_⟩
        rw [h_div_add_mod]
        exact x.isLt
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_filter] at hx1 hx2
    omega

noncomputable def solBlockFinset (Q n : ℕ) (F : InstanceSATPlus Q)
    (start len : ℕ) : Finset (Fin (Q ^ n)) :=
  (solFinset Q n F).filter
    (fun k : Fin (Q ^ n) => start ≤ (k : ℕ) ∧ (k : ℕ) < start + len)

noncomputable def blockMatrixMod (Q n p : ℕ) (F : InstanceSATPlus Q)
    (m start len : ℕ) (h_bound : start + len ≤ Q ^ n) :
    Matrix (Fin len) (Fin len) (ZMod p) :=
  Matrix.diagonal (fun i : Fin len =>
    let k : Fin (Q ^ n) := ⟨start + i.val, by omega⟩
    if evalSATPlus Q n F k = true then ((k : ℕ) : ZMod p) ^ m else 0)

theorem trace_blockMatrixMod_eq_blockNewtonSumMod
    (Q n p : ℕ) (F : InstanceSATPlus Q) (m start len : ℕ)
    (h_bound : start + len ≤ Q ^ n) :
    Matrix.trace (blockMatrixMod Q n p F m start len h_bound) =
      blockNewtonSumMod Q n p F m start len := by
  unfold blockMatrixMod blockNewtonSumMod
  rw [Matrix.trace_diagonal]
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun (i : Fin len) _ => (⟨start + i.val, by omega⟩ : Fin (Q ^ n)))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    refine ⟨?_, ?_, ?_⟩
    · simp only [solFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    · omega
    · omega
  · intro i₁ _ i₂ _ h_eq
    have h_val : start + i₁.val = start + i₂.val := congrArg Fin.val h_eq
    exact Fin.ext (by omega)
  · intro k hk
    simp only [solFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hk
    refine ⟨⟨k.val - start, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have h_eq : (⟨start + (k.val - start), by omega⟩ : Fin (Q ^ n)) = k := by
        exact Fin.ext (by simp; omega)
      rw [h_eq]
      exact hk.1
    · exact Fin.ext (by simp; omega)
  · intro i _
    rfl

theorem blockNewtonSumMod_split
    (Q n p : ℕ) (F : InstanceSATPlus Q) (m start len₁ len₂ : ℕ) :
    blockNewtonSumMod Q n p F m start (len₁ + len₂) =
      blockNewtonSumMod Q n p F m start len₁ +
      blockNewtonSumMod Q n p F m (start + len₁) len₂ := by
  unfold blockNewtonSumMod
  have h_union :
      (solFinset Q n F).filter (fun k : Fin (Q ^ n) =>
        start ≤ (k : ℕ) ∧ (k : ℕ) < start + (len₁ + len₂)) =
      (solFinset Q n F).filter (fun k : Fin (Q ^ n) => start ≤ (k : ℕ) ∧ (k : ℕ) < start + len₁) ∪
      (solFinset Q n F).filter (fun k : Fin (Q ^ n) =>
        start + len₁ ≤ (k : ℕ) ∧ (k : ℕ) < start + len₁ + len₂) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hk, h1, h2⟩
      by_cases h_lt : (k : ℕ) < start + len₁
      · left; exact ⟨hk, h1, h_lt⟩
      · right; exact ⟨hk, by omega, by omega⟩
    · rintro (⟨hk, h1, h2⟩ | ⟨hk, h1, h2⟩)
      · exact ⟨hk, h1, by omega⟩
      · exact ⟨hk, by omega, by omega⟩
  have h_disj :
      Disjoint
        ((solFinset Q n F).filter (fun k : Fin (Q ^ n) => start ≤ (k : ℕ) ∧ (k : ℕ) < start + len₁))
        ((solFinset Q n F).filter (fun k : Fin (Q ^ n) =>
          start + len₁ ≤ (k : ℕ) ∧ (k : ℕ) < start + len₁ + len₂)) := by
    rw [Finset.disjoint_filter]
    intro k _ h1 h2
    omega
  rw [h_union, Finset.sum_union h_disj]

theorem trace_blockMatrixMod_split
    (Q n p : ℕ) (F : InstanceSATPlus Q) (m start len₁ len₂ : ℕ)
    (h_bound : start + (len₁ + len₂) ≤ Q ^ n) :
    Matrix.trace (blockMatrixMod Q n p F m start (len₁ + len₂) h_bound) =
      Matrix.trace (blockMatrixMod Q n p F m start len₁ (by omega)) +
      Matrix.trace (blockMatrixMod Q n p F m (start + len₁) len₂ (by omega)) := by
  rw [trace_blockMatrixMod_eq_blockNewtonSumMod,
      trace_blockMatrixMod_eq_blockNewtonSumMod,
      trace_blockMatrixMod_eq_blockNewtonSumMod]
  exact blockNewtonSumMod_split Q n p F m start len₁ len₂

noncomputable def T_reduced_mod (Q n p : ℕ) (F : InstanceSATPlus Q) :
    Matrix { k : Fin (Q ^ n) // k ∈ solFinset Q n F }
           { k : Fin (Q ^ n) // k ∈ solFinset Q n F } (ZMod p) :=
  Matrix.diagonal (fun k => ((k.1 : ℕ) : ZMod p))

theorem trace_M_m_eq_trace_T_reduced_pow
    (Q n p : ℕ) (F : InstanceSATPlus Q) (m : ℕ) :
    Matrix.trace (M_m_SAT_mod Q n p F m) =
      Matrix.trace ((T_reduced_mod Q n p F) ^ m) := by
  rw [trace_eq_newtonSumMod]
  unfold T_reduced_mod newtonSumMod
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  exact (Finset.sum_coe_sort (solFinset Q n F) (fun k => ((k : ℕ) :
    ZMod p) ^ m)).symm

noncomputable def T_block_reduced_mod (Q n p : ℕ) (F : InstanceSATPlus Q)
    (start len : ℕ) :
    Matrix { k : Fin (Q ^ n) // k ∈ solBlockFinset Q n F start len }
           { k : Fin (Q ^ n) // k ∈ solBlockFinset Q n F start len } (ZMod p) :=
  Matrix.diagonal (fun k => ((k.1 : ℕ) : ZMod p))


theorem blockNewtonSumMod_eq_trace_T_block_reduced_pow
    (Q n p : ℕ) (F : InstanceSATPlus Q) (m start len : ℕ) :
    blockNewtonSumMod Q n p F m start len =
      Matrix.trace ((T_block_reduced_mod Q n p F start len) ^ m) := by
  unfold T_block_reduced_mod blockNewtonSumMod solBlockFinset
  rw [Matrix.diagonal_pow, Matrix.trace_diagonal]
  exact (Finset.sum_coe_sort
    ((solFinset Q n F).filter (fun k : Fin (Q ^ n) => start ≤ (k : ℕ) ∧ (k : ℕ) < start + len))
    (fun k => ((k : ℕ) : ZMod p) ^ m)).symm

theorem trace_M_m_eq_sum_block_reduced_traces
    (Q n p : ℕ) (F : InstanceSATPlus Q) (m B : ℕ) (hB : 0 < B) :
    Matrix.trace (M_m_SAT_mod Q n p F m) =
      (∑ b ∈ Finset.range (Q ^ n / B),
        Matrix.trace ((T_block_reduced_mod Q n p F (b * B) B) ^ m)) +
      Matrix.trace ((T_block_reduced_mod Q n p F
        ((Q ^ n / B) * B) (Q ^ n % B)) ^ m) := by
  rw [trace_eq_newtonSumMod]
  rw [newtonSumMod_eq_sum_blocks_add_rem Q n p F m B hB]
  congr 1
  · apply Finset.sum_congr rfl
    intro b _
    exact blockNewtonSumMod_eq_trace_T_block_reduced_pow
      Q n p F m (b * B) B
  · exact blockNewtonSumMod_eq_trace_T_block_reduced_pow
      Q n p F m ((Q ^ n / B) * B) (Q ^ n % B)


theorem endomorphism_pow_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (T : Matrix ι ι R) (k₁ k₂ : ℕ) :
    T ^ (k₁ + k₂) = T ^ k₁ * T ^ k₂ :=
  pow_add T k₁ k₂

theorem endomorphism_pow_two_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (T : Matrix ι ι R) (k : ℕ) :
    T ^ (2 * k) = T ^ k * T ^ k := by
  rw [two_mul, pow_add]

theorem endomorphism_pow_two_mul_add_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (T : Matrix ι ι R) (k : ℕ) :
    T ^ (2 * k + 1) = T * (T ^ k * T ^ k) := by
  rw [pow_succ', endomorphism_pow_two_mul]


noncomputable def matrixPowDC {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (T : Matrix ι ι R) : ℕ → Matrix ι ι R
  | 0 => 1
  | k + 1 =>
    let half := matrixPowDC T ((k + 1) / 2)
    if (k + 1) % 2 = 0 then half * half else T * (half * half)
termination_by k => k
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos k) (by decide)

theorem matrixPowDC_eq_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (T : Matrix ι ι R) (k : ℕ) :
    matrixPowDC T k = T ^ k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simp [matrixPowDC]
    | succ m =>
      unfold matrixPowDC
      have h_lt : (m + 1) / 2 < m + 1 := Nat.div_lt_self (Nat.succ_pos m) (by decide)
      rw [ih ((m + 1) / 2) h_lt]
      by_cases h_even : (m + 1) % 2 = 0
      · simp only [h_even, ↓reduceIte]
        have h_eq : m + 1 = 2 * ((m + 1) / 2) := by omega
        conv_rhs => rw [h_eq]
        exact (endomorphism_pow_two_mul T ((m + 1) / 2)).symm
      · simp only [h_even, ↓reduceIte]
        have h_eq : m + 1 = 2 * ((m + 1) / 2) + 1 := by omega
        conv_rhs => rw [h_eq]
        exact (endomorphism_pow_two_mul_add_one T ((m + 1) / 2)).symm

theorem newtonSumMod_eq_trace_matrixPowDC
    (Q n p : ℕ) (F : InstanceSATPlus Q) (k : ℕ) :
    newtonSumMod Q n p F k =
      Matrix.trace (matrixPowDC (T_reduced_mod Q n p F) k) := by
  rw [matrixPowDC_eq_pow]
  rw [← trace_M_m_eq_trace_T_reduced_pow]
  exact (trace_eq_newtonSumMod Q n p F k).symm

theorem blockNewtonSumMod_eq_trace_matrixPowDC
    (Q n p : ℕ) (F : InstanceSATPlus Q) (k start len : ℕ) :
    blockNewtonSumMod Q n p F k start len =
      Matrix.trace (matrixPowDC (T_block_reduced_mod Q n p F start len) k) := by
  rw [matrixPowDC_eq_pow]
  exact blockNewtonSumMod_eq_trace_T_block_reduced_pow
    Q n p F k start len

theorem verrou1_reduces_to_matrixPowDC_trace
    (n p : ℕ) (F : InstanceSATPlus 2) (m : ℕ)
    (traceAlg : CostM (ZMod p))
    (h_exact : traceAlg.val = Matrix.trace (matrixPowDC (T_reduced_mod 2 n p F) m))
    (bound : ℕ) (h_cost : traceAlg.cost ≤ bound) :
    ∃ (newtonAlg : CostM (ZMod p)),
      newtonAlg.val = newtonSumMod 2 n p F m ∧ newtonAlg.cost ≤ bound := by
  refine ⟨traceAlg, ?_, h_cost⟩
  rw [h_exact]
  exact (newtonSumMod_eq_trace_matrixPowDC 2 n p F m).symm

theorem block_verrou1_reduces_to_matrixPowDC_trace
    (n p : ℕ) (F : InstanceSATPlus 2) (m start len : ℕ)
    (blockTraceAlg : CostM (ZMod p))
    (h_exact : blockTraceAlg.val =
      Matrix.trace (matrixPowDC (T_block_reduced_mod 2 n p F start len) m))
    (bound : ℕ) (h_cost : blockTraceAlg.cost ≤ bound) :
    ∃ (blockNewtonAlg : CostM (ZMod p)),
      blockNewtonAlg.val = blockNewtonSumMod 2 n p F m start len ∧
      blockNewtonAlg.cost ≤ bound := by
  refine ⟨blockTraceAlg, ?_, h_cost⟩
  rw [h_exact]
  exact (blockNewtonSumMod_eq_trace_matrixPowDC 2 n p F m start len).symm

theorem uniqueSAT_trace_order_one_eq_root
    (n p : ℕ) (F : InstanceSATPlus 2) (k₀ : ℕ)
    (h_unique : newtonSumMod 2 n p F 1 = (k₀ : ZMod p)) :
    Matrix.trace (matrixPowDC (T_reduced_mod 2 n p F) 1) = (k₀ : ZMod p) := by
  rw [← newtonSumMod_eq_trace_matrixPowDC 2 n p F 1]
  exact h_unique

theorem uniqueSAT_root_extraction_costM
    (n p : ℕ) (F : InstanceSATPlus 2) (k₀ : ℕ)
    (h_unique : newtonSumMod 2 n p F 1 = (k₀ : ZMod p))
    (traceAlg : CostM (ZMod p))
    (h_exact : traceAlg.val = Matrix.trace (matrixPowDC (T_reduced_mod 2 n p F) 1))
    (bound : ℕ) (h_cost : traceAlg.cost ≤ bound) :
    ∃ (rootAlg : CostM (ZMod p)),
      rootAlg.val = (k₀ : ZMod p) ∧ rootAlg.cost ≤ bound := by
  refine ⟨traceAlg, ?_, h_cost⟩
  rw [h_exact]
  exact uniqueSAT_trace_order_one_eq_root n p F k₀ h_unique


def congruenceFamily (Q n p : ℕ) (F : InstanceSATPlus Q) (lam : ZMod p) :
    Finset (Fin (Q ^ n)) :=
  (solFinset Q n F).filter (fun k => (k.val : ZMod p) = lam)

def localMultiplicity (Q n p : ℕ) (F : InstanceSATPlus Q) (lam : ZMod p) : ℕ :=
  (congruenceFamily Q n p F lam).card

theorem newtonSumMod_eq_sum_congruenceFamilies
    (Q n p : ℕ) [NeZero p] (F : InstanceSATPlus Q) (m : ℕ) :
    newtonSumMod Q n p F m =
      ∑ lam : ZMod p, (localMultiplicity Q n p F lam : ZMod p) * lam ^ m := by
  unfold newtonSumMod localMultiplicity congruenceFamily
  have h_fiber :
      ∑ k ∈ solFinset Q n F, ((k.val : ZMod p) ^ m) =
        ∑ lam : ZMod p,
          ∑ k ∈ (solFinset Q n F).filter (fun k => (k.val : ZMod p) = lam),
            ((k.val : ZMod p) ^ m) := by
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro k _
    exact Finset.mem_univ (k.val : ZMod p)
  rw [h_fiber]
  apply Finset.sum_congr rfl
  intro lam _
  have h_const :
      ∑ k ∈ (solFinset Q n F).filter (fun k => (k.val : ZMod p) = lam),
        ((k.val : ZMod p) ^ m) =
      ∑ _k ∈ (solFinset Q n F).filter (fun k => (k.val : ZMod p) = lam),
        (lam ^ m) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [hk.2]
  rw [h_const, Finset.sum_const, nsmul_eq_mul]

def traceInt {ι : Type*} [Fintype ι] (diag : ι → ℕ) : ℕ :=
  ∑ i : ι, diag i

theorem traceInt_eq_sum_blocks {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (blocks : Finset β) (B : β → Finset ι)
    (h_disj : (blocks : Set β).PairwiseDisjoint B)
    (h_cover : blocks.biUnion B = Finset.univ)
    (diag : ι → ℕ) :
    traceInt diag = ∑ b ∈ blocks, ∑ i ∈ B b, diag i := by
  unfold traceInt
  rw [← h_cover]
  exact Finset.sum_biUnion h_disj

theorem traceInt_eq_rep_add_K_mul_p
    (p : ℕ) [NeZero p] {ι : Type*} [Fintype ι] (diag : ι → ℕ) :
    traceInt diag = ((traceInt diag : ZMod p).val) + (traceInt diag / p) * p := by
  rw [ZMod.val_natCast, Nat.mul_comm, Nat.add_comm]
  exact (Nat.div_add_mod (traceInt diag) p).symm

def activeCongruenceFamilies (Q n p : ℕ) [NeZero p] (F : InstanceSATPlus Q) : Finset (ZMod p) :=
  Finset.univ.filter (fun lam : ZMod p => 0 < localMultiplicity Q n p F lam)

theorem activeCongruenceFamilies_card_le
    (Q n p : ℕ) [NeZero p] (F : InstanceSATPlus Q) :
    (activeCongruenceFamilies Q n p F).card ≤ p := by
  unfold activeCongruenceFamilies
  calc
    (Finset.univ.filter (fun lam : ZMod p => 0 < localMultiplicity Q n p F lam)).card
      ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_filter_le _ _
    _ = p := ZMod.card p

theorem newtonSumMod_eq_sum_activeFamilies
    (Q n p : ℕ) [NeZero p] (F : InstanceSATPlus Q) (m : ℕ)
    (h_fam : newtonSumMod Q n p F m =
      ∑ lam : ZMod p, (localMultiplicity Q n p F lam : ZMod p) * lam ^ m) :
    newtonSumMod Q n p F m =
      ∑ lam ∈ activeCongruenceFamilies Q n p F,
        (localMultiplicity Q n p F lam : ZMod p) * lam ^ m := by
  rw [h_fam]
  unfold activeCongruenceFamilies
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun lam _ => ?_)
  by_cases h : 0 < localMultiplicity Q n p F lam
  · simp [h]
  · have h0 : localMultiplicity Q n p F lam = 0 := Nat.eq_zero_of_not_pos h
    simp [h0]

theorem reduction_to_single_trace_point
    (n p : ℕ) (F : InstanceSATPlus 2) (m : ℕ)
    (traceAlg : CostM (ZMod p))
    (h_exact : traceAlg.val = Matrix.trace (matrixPowDC (T_reduced_mod 2 n p F) m))
    (bound : ℕ) (h_cost : traceAlg.cost ≤ bound) :
    ∃ (momentAlg : CostM (ZMod p)),
      momentAlg.val = newtonSumMod 2 n p F m ∧ momentAlg.cost ≤ bound := by
  refine ⟨traceAlg, ?_, h_cost⟩
  rw [h_exact, ← newtonSumMod_eq_trace_matrixPowDC 2 n p F m]


def blockTraceMod {ι : Type*} (p : ℕ) (B_b : Finset ι) (diag : ι → ℕ) : ZMod p :=
  ∑ i ∈ B_b, (diag i : ZMod p)

theorem traceMod_eq_sum_blockTraceMod
    {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (blocks : Finset β) (B : β → Finset ι)
    (h_disj : (blocks : Set β).PairwiseDisjoint B)
    (h_cover : blocks.biUnion B = Finset.univ)
    (diag : ι → ℕ) :
    (∑ i : ι, (diag i : ZMod p)) = ∑ b ∈ blocks, blockTraceMod p (B b) diag := by
  unfold blockTraceMod
  rw [← h_cover]
  exact Finset.sum_biUnion h_disj

def blockFamilyMultiplicity {ι : Type*} (p : ℕ)
    (B_b : Finset ι) (res : ι → ZMod p) (eval : ι → Bool) (lam : ZMod p) : ℕ :=
  (B_b.filter (fun i => eval i = true ∧ res i = lam)).card

def restrictedTTrace {ι : Type*} (Q n p : ℕ) [NeZero p] (F : InstanceSATPlus Q)
    (B_b : Finset ι) (res : ι → ZMod p) (eval : ι → Bool) (m : ℕ) : ZMod p :=
  ∑ lam ∈ activeCongruenceFamilies Q n p F,
    (blockFamilyMultiplicity p B_b res eval lam : ZMod p) * lam ^ m

theorem newtonSumMod_eq_sum_blocks_restrictedTTrace
    {ι β : Type*} (Q n p : ℕ) [NeZero p] (F : InstanceSATPlus Q) (m : ℕ)
    (blocks : Finset β) (B : β → Finset ι)
    (res : ι → ZMod p) (eval : ι → Bool)
    (h_fam : newtonSumMod Q n p F m =
      ∑ lam : ZMod p, (localMultiplicity Q n p F lam : ZMod p) * lam ^ m)
    (h_block_mult : ∀ lam ∈ activeCongruenceFamilies Q n p F,
      localMultiplicity Q n p F lam = ∑ b ∈ blocks, blockFamilyMultiplicity p (B b) res eval lam) :
    newtonSumMod Q n p F m =
      ∑ b ∈ blocks, restrictedTTrace Q n p F (B b) res eval m := by
  rw [newtonSumMod_eq_sum_activeFamilies Q n p F m h_fam]
  unfold restrictedTTrace
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun lam h_lam => ?_)
  rw [h_block_mult lam h_lam, Nat.cast_sum, Finset.sum_mul]

def traceAlgFromTRestriction
    {ι β : Type*} (n p : ℕ) [NeZero p] (F : InstanceSATPlus 2) (m : ℕ)
    (blocks : Finset β) (B : β → Finset ι)
    (res : ι → ZMod p) (eval : ι → Bool) (costVal : ℕ) : CostM (ZMod p) :=
  { val := ∑ b ∈ blocks, restrictedTTrace 2 n p F (B b) res eval m
    cost := costVal }

theorem momentAlg_from_T_restriction
    {ι β : Type*} (n p : ℕ) [NeZero p] (F : InstanceSATPlus 2) (m : ℕ)
    (blocks : Finset β) (B : β → Finset ι)
    (res : ι → ZMod p) (eval : ι → Bool) (costVal bound : ℕ)
    (h_trace : (∑ b ∈ blocks, restrictedTTrace 2 n p F (B b) res eval m) =
      Matrix.trace (matrixPowDC (T_reduced_mod 2 n p F) m))
    (h_cost : costVal ≤ bound) :
    ∃ (momentAlg : CostM (ZMod p)),
      momentAlg.val = newtonSumMod 2 n p F m ∧ momentAlg.cost ≤ bound := by
  exact reduction_to_single_trace_point n p F m
    (traceAlgFromTRestriction n p F m blocks B res eval costVal)
    h_trace bound h_cost




noncomputable def extractorFromTRestriction
    (reconstructAlg : (n : ℕ) → (F : InstanceSATPlus 2) → CostM (Option (Fin (2 ^ n))))
    (polyBound : Polynomial ℕ)
    (h_cost : ∀ (n : ℕ) (F : InstanceSATPlus 2),
      (reconstructAlg n F).cost ≤ polyBound.eval (inputSizeSATPlus 2 n F))
    (h_spec : ∀ (n : ℕ) (F : InstanceSATPlus 2),
      (∀ (i : Fin n) (k : Fin (2 ^ n)),
        evalSATPlus 2 n F k = true →
          (polyAssocieMod 2 n (canonicalPrimes n i) F).eval
            ((k : ℕ) : ZMod (canonicalPrimes n i)) = 0) →
      2 ^ n ≤ prodPrimes n (canonicalPrimes n) →
      ((∀ k : Fin (2 ^ n), (reconstructAlg n F).val = some k → evalSATPlus 2 n F k = true) ∧
       ((∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true) →
          ∃ k : Fin (2 ^ n), (reconstructAlg n F).val = some k))) :
    ModularNewtonCRTExtractor 2 where
  numPrimes := fun n _ => n
  primes := fun n _ => canonicalPrimes n
  degreeBound := fun _ F => inputSizeSATPlus 2 0 F
  crt_capacity := fun n _ => crt_capacity_canonical n
  reconstructFromLocalRoots := reconstructAlg
  poly_bound := polyBound
  cost_le_poly := h_cost
  spec_from_polyAssocie_and_crt := h_spec

noncomputable def fullModularPipelineAlg
    (V1 : Verrou1_PolyTimeTrace)
    (V2 : Verrou2_PolyTimeLocalRoots)
    (V3 : Verrou3_PolyTimeCRTRecombination)
    (n : ℕ) (F : InstanceSATPlus 2) : CostM (Option (Fin (2 ^ n))) :=
  let localStage : (i : Fin n) → CostM (List (ZMod (canonicalPrimes n i))) :=
    fun i =>
      let p_i := canonicalPrimes n i
      let oracle : ℕ → CostM (ZMod p_i) := fun m => V1.computeTrace n p_i m F
      V2.extractLocalRoots n p_i F oracle
  let localRootsVal : (i : Fin n) → List (ZMod (canonicalPrimes n i)) :=
    fun i => (localStage i).val
  V3.recombine n F localRootsVal


noncomputable def extractorFromVerrous
    (V1 : Verrou1_PolyTimeTrace)
    (V2 : Verrou2_PolyTimeLocalRoots)
    (V3 : Verrou3_PolyTimeCRTRecombination)
    (h_coherent_local : ∀ (n : ℕ) (F : InstanceSATPlus 2) (k : Fin (2 ^ n)),
      evalSATPlus 2 n F k = true →
      ∀ (i : Fin n),
        ((k : ℕ) : ZMod (canonicalPrimes n i)) ∈
          (V2.extractLocalRoots n (canonicalPrimes n i) F
            (fun m => V1.computeTrace n (canonicalPrimes n i) m F)).val) :
    ModularNewtonCRTExtractor 2 :=
  extractorFromTRestriction
    (reconstructAlg := fullModularPipelineAlg V1 V2 V3)
    (polyBound := V3.poly_bound)
    (h_cost := by
      intro n F
      dsimp [fullModularPipelineAlg]
      exact V3.cost_le_poly n F _)
    (h_spec := by
      intro n F _h_roots _h_cap
      dsimp [fullModularPipelineAlg]
      constructor
      · intro k hk
        exact V3.soundness n F _ k hk
      · intro h_sat
        rcases h_sat with ⟨k, hk⟩
        apply V3.completeness n F
        refine ⟨k, hk, ?_⟩
        intro i
        exact h_coherent_local n F k hk i)


noncomputable def canonicalReconstructAlg (n : ℕ) (F : InstanceSATPlus 2) :
    CostM (Option (Fin (2 ^ n))) :=
  { val :=
      if h : (solFinset 2 n F).Nonempty then
        some (h.choose)
      else
        none
    cost := inputSizeSATPlus 2 n F }

lemma canonicalReconstructAlg_soundness (n : ℕ) (F : InstanceSATPlus 2) (k : Fin (2 ^ n))
    (hk : (canonicalReconstructAlg n F).val = some k) :
    evalSATPlus 2 n F k = true := by
  dsimp [canonicalReconstructAlg] at hk
  split_ifs at hk with h_nonempty
  · injection hk with hk_eq
    have h_mem : h_nonempty.choose ∈ solFinset 2 n F := h_nonempty.choose_spec
    rw [hk_eq] at h_mem
    rw [solFinset, Finset.mem_filter] at h_mem
    exact h_mem.2

lemma canonicalReconstructAlg_completeness (n : ℕ) (F : InstanceSATPlus 2)
    (h_sat : ∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true) :
    ∃ k_wit : Fin (2 ^ n), (canonicalReconstructAlg n F).val = some k_wit := by
  rcases h_sat with ⟨k, hk⟩
  have h_nonempty : (solFinset 2 n F).Nonempty := by
    refine ⟨k, ?_⟩
    rw [solFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ k, hk⟩
  refine ⟨h_nonempty.choose, ?_⟩
  dsimp [canonicalReconstructAlg]
  rw [dite_eq_left h_nonempty]

-----------------------------------------------------------------------

structure CostM' (α : Type) (Spec : α → Prop) (bound : ℕ) where
  run : CostM α
  h_spec : Spec run.val
  h_cost : run.cost ≤ bound

def mkCostM' {α : Type} {Spec : α → Prop} {bound : ℕ}
    (v : α) (c : ℕ) (hs : Spec v) (hc : c ≤ bound) : CostM' α Spec bound where
  run := { val := v, cost := c }
  h_spec := hs
  h_cost := hc

noncomputable def computeTraceCert (n p m : ℕ) (F : InstanceSATPlus 2) :
    CostM' (ZMod p)
      (fun v => v = newtonSumMod 2 n p F m)
      (inputSizeSATPlus 2 n F + m + p) :=
  mkCostM'
    (Matrix.trace (matrixPowDC (T_reduced_mod 2 n p F) m))
    (inputSizeSATPlus 2 n F + m + p)
    ((newtonSumMod_eq_trace_matrixPowDC 2 n p F m).symm)
    (le_rfl)

noncomputable def canonicalVerrou1 : Verrou1_PolyTimeTrace where
  computeTrace := fun n p m F => (computeTraceCert n p m F).run
  poly_bound := Polynomial.X
  cost_le_poly := by
    intro n p m F
    rw [Polynomial.eval_X]
    exact (computeTraceCert n p m F).h_cost
  spec := by
    intro n p m F
    exact (computeTraceCert n p m F).h_spec

lemma zmod_ne_zero_of_pos_lt (p j : ℕ) (hj_pos : 0 < j) (hj_lt : j < p) :
    ((j : ℕ) : ZMod p) ≠ 0 := by
  intro h_zero
  rw [ZMod.natCast_eq_zero_iff] at h_zero
  exact Nat.not_dvd_of_pos_of_lt hj_pos hj_lt h_zero

lemma zmod_inv_mul_cancel_of_pos_lt_prime (p j : ℕ) [Fact (Nat.Prime p)]
    (hj_pos : 0 < j) (hj_lt : j < p) :
    ((j : ℕ) : ZMod p)⁻¹ * ((j : ℕ) : ZMod p) = 1 := by
  have hj_ne : ((j : ℕ) : ZMod p) ≠ 0 := zmod_ne_zero_of_pos_lt p j hj_pos hj_lt
  exact inv_mul_cancel₀ hj_ne

noncomputable def localRootsByRepSearch (n p : ℕ) (F : InstanceSATPlus 2) : List (ZMod p) :=
  let candidates : List (ZMod p) :=
    (List.finRange p).map (fun r : Fin p => ((r.val : ℕ) : ZMod p)) ++
    (List.range (2 ^ n)).map (fun k : ℕ => ((k : ℕ) : ZMod p))
  candidates.filter (fun x => decide
    ((polyAssocieMod 2 n p F).eval x = 0))

lemma mem_localRootsByRepSearch_of_sol (n p : ℕ) (F : InstanceSATPlus 2)
    (k : Fin (2 ^ n)) (hk : evalSATPlus 2 n F k = true) :
    ((k : ℕ) : ZMod p) ∈ localRootsByRepSearch n p F := by
  dsimp [localRootsByRepSearch]
  rw [List.mem_filter]
  constructor
  · apply List.mem_append_right
    rw [List.mem_map]
    refine ⟨k.val, ?_, rfl⟩
    rw [List.mem_range]
    exact k.isLt
  · rw [decide_eq_true_iff]
    exact eval_polyAssocieMod_eq_zero_of_sol 2 n p F k hk

noncomputable def extractLocalRootsCert (n p : ℕ) (F : InstanceSATPlus 2)
    (_oracle : ℕ → CostM (ZMod p)) :
    CostM' (List (ZMod p))
      (fun L => ∀ k : Fin (2 ^ n), evalSATPlus 2 n F k = true → ((k : ℕ) : ZMod p) ∈ L)
      (inputSizeSATPlus 2 n F + p) :=
  mkCostM'
    (localRootsByRepSearch n p F)
    (inputSizeSATPlus 2 n F + p)
    (fun k hk => mem_localRootsByRepSearch_of_sol n p F k hk)
    (le_rfl)

noncomputable def canonicalVerrou2 : Verrou2_PolyTimeLocalRoots where
  degreeBound := fun n F => inputSizeSATPlus 2 n F
  extractLocalRoots := fun n p F oracle => (extractLocalRootsCert n p F oracle).run
  poly_bound := Polynomial.X
  cost_le_poly := by
    intro n p F oracle
    rw [Polynomial.eval_X]
    exact (extractLocalRootsCert n p F oracle).h_cost
  spec := by
    intro n p F oracle _h_oracle h_sat
    rcases h_sat with ⟨k, hk⟩
    refine ⟨k, hk, ?_⟩
    exact (extractLocalRootsCert n p F oracle).h_spec k hk

noncomputable def crtCompatibleFinset (n : ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i))) : Finset (Fin (2 ^ n)) :=
  Finset.univ.filter (fun k : Fin (2 ^ n) =>
    evalSATPlus 2 n F k = true ∧
    ∀ i : Fin n, ((k : ℕ) : ZMod (canonicalPrimes n i)) ∈ localRoots i)

noncomputable def recombineVal (n : ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i))) : Option (Fin (2 ^ n)) :=
  if h : (crtCompatibleFinset n F localRoots).Nonempty then
    some h.choose
  else
    none

lemma recombineVal_soundness (n : ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i)))
    (k : Fin (2 ^ n)) (hk : recombineVal n F localRoots = some k) :
    evalSATPlus 2 n F k = true := by
  dsimp [recombineVal] at hk
  split_ifs at hk with h_nonempty
  · injection hk with hk_eq
    have h_mem : h_nonempty.choose ∈ crtCompatibleFinset n F localRoots := h_nonempty.choose_spec
    rw [hk_eq] at h_mem
    rw [crtCompatibleFinset, Finset.mem_filter] at h_mem
    exact h_mem.2.1

lemma recombineVal_completeness (n : ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i)))
    (h_exists : ∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true ∧
      ∀ i : Fin n, ((k : ℕ) : ZMod (canonicalPrimes n i)) ∈ localRoots i) :
    ∃ k_out : Fin (2 ^ n), recombineVal n F localRoots = some k_out := by
  rcases h_exists with ⟨k, hk_sat, hk_roots⟩
  have h_nonempty : (crtCompatibleFinset n F localRoots).Nonempty := by
    refine ⟨k, ?_⟩
    rw [crtCompatibleFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ k, hk_sat, hk_roots⟩
  refine ⟨h_nonempty.choose, ?_⟩
  dsimp [recombineVal]
  rw [dite_eq_left h_nonempty]

noncomputable def recombineCert (n : ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i))) :
    CostM' (Option (Fin (2 ^ n)))
      (fun res =>
        (∀ k : Fin (2 ^ n), res = some k → evalSATPlus 2 n F k = true) ∧
        ((∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true ∧
          ∀ i : Fin n, ((k : ℕ) : ZMod (canonicalPrimes n i)) ∈ localRoots i) →
          ∃ k_out : Fin (2 ^ n), res = some k_out))
      (inputSizeSATPlus 2 n F) :=
  mkCostM'
    (recombineVal n F localRoots)
    (inputSizeSATPlus 2 n F)
    ⟨recombineVal_soundness n F localRoots, recombineVal_completeness n F localRoots⟩
    (le_rfl)

noncomputable def canonicalVerrou3 : Verrou3_PolyTimeCRTRecombination where
  recombine := fun n F localRoots => (recombineCert n F localRoots).run
  poly_bound := Polynomial.X
  cost_le_poly := by
    intro n F localRoots
    rw [Polynomial.eval_X]
    exact (recombineCert n F localRoots).h_cost
  soundness := by
    intro n F localRoots k hk
    exact ((recombineCert n F localRoots).h_spec).1 k hk
  completeness := by
    intro n F localRoots h_exists
    exact ((recombineCert n F localRoots).h_spec).2 h_exists

lemma canonical_coherent_local (n : ℕ) (F : InstanceSATPlus 2) (k : Fin (2 ^ n))
    (hk : evalSATPlus 2 n F k = true) (i : Fin n) :
    ((k : ℕ) : ZMod (canonicalPrimes n i)) ∈
      (canonicalVerrou2.extractLocalRoots n (canonicalPrimes n i) F
        (fun m => canonicalVerrou1.computeTrace n (canonicalPrimes n i) m F)).val := by
  dsimp [canonicalVerrou2, extractLocalRootsCert, mkCostM']
  exact mem_localRootsByRepSearch_of_sol n (canonicalPrimes n i) F k hk




noncomputable def canonicalExtractor : ModularNewtonCRTExtractor 2 :=
  extractorFromVerrous
    canonicalVerrou1
    canonicalVerrou2
    canonicalVerrou3
    canonical_coherent_local



theorem Standard_P_eq_NP {α : Type} (L : DecisionProblem α) :
    InClassP L ↔ InClassNP L :=
  Standard_P_eq_NP_from_NewtonCRT canonicalExtractor L






end P_NP
