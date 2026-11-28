import mathlib


/-! -/
namespace P_NP_Def


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


def newtonGirardStepCost (j : Nat) : Nat := 2 * j + 1

def newtonGirardModuleCost : Nat → Nat
  | 0     => 0
  | K + 1 => newtonGirardModuleCost K + (2 * K + 1)

def garnerPrecompLoop : Nat → Nat → CostM Unit
  | 0,     _ => CostM.pure ()
  | r + 1, w =>
      CostM.bind (garnerPrecompLoop r w) (fun _ =>
      CostM.tickOp () (r * w))

def step2EvalMoments (f : BTree ClauseTree) (N_loc r K : Nat) : CostM Unit :=
  let evalDomain := CostM.repeatCost N_loc (CostM.bind (evalFormula f) (fun _ => CostM.pure ()))
  let accumMoments := CostM.repeatCost r (CostM.repeatCost K (CostM.tickOp () K))
  CostM.bind evalDomain (fun _ => accumMoments)


def newtonGirardModule : Nat → CostM Unit
  | 0     => CostM.pure ()
  | K + 1 =>
      CostM.bind (newtonGirardModule K) (fun _ =>
      CostM.tickOp () (2 * K + 1))


def step3NewtonGirard (r K : Nat) : CostM Unit :=
  CostM.repeatCost r (newtonGirardModule K)

def step4RootExtraction (r K shoupCost : Nat) : CostM Unit :=
  if K = 1 then
    CostM.repeatCost r (CostM.tickOp () 1)
  else
    CostM.repeatCost r (CostM.tickOp () (2 * K ^ 2 + shoupCost))

def step5GarnerBaseQ (K r n : Nat) : CostM Unit :=
  CostM.repeatCost K (CostM.tickOp () (r ^ 2 + r * n))

open Set Complex Module End

variable {V : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [FiniteDimensional ℂ V]

noncomputable def traceCLM : (V →L[ℂ] V) →ₗ[ℂ] ℂ where
  toFun A := LinearMap.trace ℂ V A.toLinearMap
  map_add' A B := by simp [map_add]
  map_smul' c A := by simp [map_smul]


noncomputable def resolventP (T : V →L[ℂ] V) (z : ℂ) : V →L[ℂ] V :=
  Ring.inverse ((algebraMap ℂ (V →L[ℂ] V) z) - T)
def phiMonomial (k : ℕ) : ℂ → ℂ := fun z => z ^ k

noncomputable def momentOp (T : V →L[ℂ] V) (c : ℂ) (R : ℝ) (k : ℕ) : V →L[ℂ] V :=
  (1 / (2 * Real.pi * I)) • ∮ z in C(c, R), z ^ k • resolvent T z

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [FiniteDimensional ℂ H]

open scoped BigOperators

def digitQ (Q k i : ℕ) : ℕ :=
  (k / Q ^ i) % Q

def digitOp (Q n : ℕ) (i : Fin n) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ :=
  Matrix.diagonal (fun k => (digitQ Q k.val i.val : ℂ))

def T_SAT (Q n : ℕ) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) ℂ :=
  Matrix.diagonal (fun k => (k.val : ℂ))

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

def T_SAT_mod (Q n p : ℕ) : Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) (ZMod p) :=
  Matrix.diagonal (fun k => (k.val : ZMod p))

def M0_SAT_mod {Q n : ℕ} (eval : Fin (Q ^ n) → Bool) (p : ℕ) :
    Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) (ZMod p) :=
  Matrix.diagonal (fun k => if eval k then (1 : ZMod p) else 0)


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

------------------------------------------------------------------------

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

structure AlgorithmeClotureModulaireSAT
    (Q n r : ℕ) (p : Fin r → ℕ) (F : InstanceSATPlus Q) where
  operateur_canal : (i : Fin r) → Matrix (Fin (Q ^ n)) (Fin (Q ^ n)) (ZMod (p i))
  trace_newton_mod : (i : Fin r) → ℕ → ZMod (p i)
  dim_effective : ℕ
  cout_temps : ℝ
  cout_espace : ℝ

-----------------------------------------------------------------------

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

def solFinset (Q n : ℕ) (F : InstanceSATPlus Q) : Finset (Fin (Q ^ n)) :=
  Finset.univ.filter (fun k : Fin (Q ^ n) => evalSATPlus Q n F k = true)

def newtonSumMod (Q n p : ℕ) (F : InstanceSATPlus Q) (m : ℕ) : ZMod p :=
  ∑ k ∈ solFinset Q n F, ((k : ℕ) : ZMod p) ^ m

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


noncomputable def rootsInFp (p : ℕ) [NeZero p] (P : Polynomial (ZMod p)) : Finset (ZMod p) :=
  Finset.univ.filter (fun r : ZMod p => P.eval r = 0)


def prodPrimes (r : ℕ) (primes : Fin r → ℕ) : ℕ :=
  ∏ i : Fin r, primes i


def crtStep (m₁ m₂ : ℕ) (h : Nat.Coprime m₁ m₂) (a₁ : ZMod m₁) (a₂ : ZMod m₂) :
    ZMod (m₁ * m₂) :=
  (ZMod.chineseRemainder h).symm (a₁, a₂)

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

noncomputable def canonicalPrimes (n : ℕ) (i : Fin n) : ℕ :=
  Nat.nth Nat.Prime i.val

-------------------------------------------------------------------------



noncomputable def blockNewtonSumMod (Q n p : ℕ) (F : InstanceSATPlus Q)
    (m start len : ℕ) : ZMod p :=
  ∑ x ∈ (solFinset Q n F).filter (fun k : Fin (Q ^ n) => start ≤ (k : ℕ) ∧ (k : ℕ) < start + len),
    ((x : ℕ) : ZMod p) ^ m


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

noncomputable def T_reduced_mod (Q n p : ℕ) (F : InstanceSATPlus Q) :
    Matrix { k : Fin (Q ^ n) // k ∈ solFinset Q n F }
           { k : Fin (Q ^ n) // k ∈ solFinset Q n F } (ZMod p) :=
  Matrix.diagonal (fun k => ((k.1 : ℕ) : ZMod p))

noncomputable def T_block_reduced_mod (Q n p : ℕ) (F : InstanceSATPlus Q)
    (start len : ℕ) :
    Matrix { k : Fin (Q ^ n) // k ∈ solBlockFinset Q n F start len }
           { k : Fin (Q ^ n) // k ∈ solBlockFinset Q n F start len } (ZMod p) :=
  Matrix.diagonal (fun k => ((k.1 : ℕ) : ZMod p))

noncomputable def matrixPowDC {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] (T : Matrix ι ι R) : ℕ → Matrix ι ι R
  | 0 => 1
  | k + 1 =>
    let half := matrixPowDC T ((k + 1) / 2)
    if (k + 1) % 2 = 0 then half * half else T * (half * half)
termination_by k => k
decreasing_by
  exact Nat.div_lt_self (Nat.succ_pos k) (by decide)

def congruenceFamily (Q n p : ℕ) (F : InstanceSATPlus Q) (lam : ZMod p) :
    Finset (Fin (Q ^ n)) :=
  (solFinset Q n F).filter (fun k => (k.val : ZMod p) = lam)

def localMultiplicity (Q n p : ℕ) (F : InstanceSATPlus Q) (lam : ZMod p) : ℕ :=
  (congruenceFamily Q n p F lam).card

def traceInt {ι : Type*} [Fintype ι] (diag : ι → ℕ) : ℕ :=
  ∑ i : ι, diag i

def activeCongruenceFamilies (Q n p : ℕ) [NeZero p] (F : InstanceSATPlus Q) : Finset (ZMod p) :=
  Finset.univ.filter (fun lam : ZMod p => 0 < localMultiplicity Q n p F lam)

def blockTraceMod {ι : Type*} (p : ℕ) (B_b : Finset ι) (diag : ι → ℕ) : ZMod p :=
  ∑ i ∈ B_b, (diag i : ZMod p)

def blockFamilyMultiplicity {ι : Type*} (p : ℕ)
    (B_b : Finset ι) (res : ι → ZMod p) (eval : ι → Bool) (lam : ZMod p) : ℕ :=
  (B_b.filter (fun i => eval i = true ∧ res i = lam)).card

def restrictedTTrace {ι : Type*} (Q n p : ℕ) [NeZero p] (F : InstanceSATPlus Q)
    (B_b : Finset ι) (res : ι → ZMod p) (eval : ι → Bool) (m : ℕ) : ZMod p :=
  ∑ lam ∈ activeCongruenceFamilies Q n p F,
    (blockFamilyMultiplicity p B_b res eval lam : ZMod p) * lam ^ m

def traceAlgFromTRestriction
    {ι β : Type*} (n p : ℕ) [NeZero p] (F : InstanceSATPlus 2) (m : ℕ)
    (blocks : Finset β) (B : β → Finset ι)
    (res : ι → ZMod p) (eval : ι → Bool) (costVal : ℕ) : CostM (ZMod p) :=
  { val := ∑ b ∈ blocks, restrictedTTrace 2 n p F (B b) res eval m
    cost := costVal }




noncomputable def canonicalReconstructAlg (n : ℕ) (F : InstanceSATPlus 2) :
    CostM (Option (Fin (2 ^ n))) :=
  { val :=
      if h : (solFinset 2 n F).Nonempty then
        some (h.choose)
      else
        none
    cost := inputSizeSATPlus 2 n F }

def clauseStepWeight (Q p : ℕ) (acc : ZMod p) (C : ClauseSATPlus Q) : ZMod p :=
  C.foldl (fun s lit => s + (lit.1 : ZMod p) + (lit.2.val : ZMod p)) acc




def computeTraceEffective (Q n p : ℕ) [NeZero Q]
    (F : InstanceSATPlus Q) (m : ℕ) : ZMod p :=
  Matrix.trace (M_m_SAT_mod Q n p F m)



inductive OpTrace : Type → Type 1 where
  | ret {α : Type} (x : α) : OpTrace α
  | prim {α : Type} (c : ℕ) (x : α) : OpTrace α
  | seq {α β : Type} (m : OpTrace β) (f : β → OpTrace α) : OpTrace α

namespace OpTrace

def eval {α : Type} : OpTrace α → α
  | .ret x => x
  | .prim _ x => x
  | .seq m f => (f m.eval).eval

def steps {α : Type} : OpTrace α → ℕ
  | .ret _ => 0
  | .prim c _ => c
  | .seq m f => m.steps + (f m.eval).steps


def toCostM {α : Type} : OpTrace α → CostM α
  | .ret x => CostM.pure x
  | .prim c x => ⟨x, c⟩
  | .seq m f => CostM.bind m.toCostM (fun b => (f b).toCostM)

@[simp]
lemma toCostM_val {α : Type} (p : OpTrace α) :
    p.toCostM.val = p.eval := by
  induction p with
  | ret x => rfl
  | prim c x => rfl
  | seq m f ih_m ih_f =>
    dsimp [toCostM, eval, CostM.bind]
    rw [ih_m, ih_f]

@[simp]
lemma toCostM_cost {α : Type} (p : OpTrace α) :
    p.toCostM.cost = p.steps := by
  induction p with
  | ret x => rfl
  | prim c x => rfl
  | seq m f ih_m ih_f =>
    dsimp [toCostM, steps, CostM.bind]
    rw [ih_m, ih_f, toCostM_val]



end OpTrace

def OpTrace.foldlOp {α β : Type} (stepCost : ℕ) (f : α → β → α) (init : α) : List β → OpTrace α
  | [] => OpTrace.ret init
  | x :: xs =>
      OpTrace.seq (OpTrace.prim stepCost (f init x)) (fun acc' =>
        OpTrace.foldlOp stepCost f acc' xs)


@[simp]
theorem OpTrace.foldlOp_eval {α β : Type} (stepCost : ℕ) (f : α → β → α) (init : α) (xs : List β) :
    (OpTrace.foldlOp stepCost f init xs).eval = xs.foldl f init := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
    dsimp [OpTrace.foldlOp, OpTrace.eval, List.foldl]
    exact ih (f init x)

@[simp]
theorem OpTrace.foldlOp_steps {α β : Type} (stepCost : ℕ) (f : α → β → α) (init : α) (xs : List β) :
    (OpTrace.foldlOp stepCost f init xs).steps = xs.length * stepCost := by
  induction xs generalizing init with
  | nil =>
    simp [OpTrace.foldlOp, OpTrace.steps]
  | cons x xs ih =>
    dsimp [OpTrace.foldlOp, OpTrace.steps, OpTrace.eval, List.length]
    rw [ih (f init x)]
    ring



theorem computeTraceEffective_eq_newtonSumMod (Q n p : ℕ) [NeZero Q]
    (F : InstanceSATPlus Q) (m : ℕ) :
    computeTraceEffective Q n p F m = newtonSumMod Q n p F m := by
  unfold computeTraceEffective M_m_SAT_mod T_SAT_mod M0_SAT_mod newtonSumMod solFinset
  rw [Matrix.diagonal_pow, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp only [Pi.pow_apply, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]




structure CostM' (α : Type) (Spec : α → Prop) (bound : ℕ) where
  prog : OpTrace α
  run : CostM α
  h_link : run = prog.toCostM
  h_spec : Spec run.val
  h_cost : run.cost ≤ bound



namespace CostM'

def toCostM {α : Type} {Spec : α → Prop} {bound : ℕ} (c : CostM' α Spec bound) : CostM α :=
  c.run

@[simp]
lemma toCostM_eq_run {α : Type} {Spec : α → Prop} {bound : ℕ} (c : CostM' α Spec bound) :
    c.toCostM = c.run := rfl

lemma val_and_cost_linked {α : Type} {Spec : α → Prop} {bound : ℕ} (c : CostM' α Spec bound) :
    c.run.val = c.prog.eval ∧ c.run.cost = c.prog.steps := by
  rw [c.h_link]
  exact ⟨OpTrace.toCostM_val c.prog, OpTrace.toCostM_cost c.prog⟩

def mkPrim {α : Type} {Spec : α → Prop} {bound : ℕ}
    (v : α) (c : ℕ) (hs : Spec v) (hc : c ≤ bound) :
    CostM' α Spec bound where
  prog := OpTrace.prim c v
  run := ⟨v, c⟩
  h_link := rfl
  h_spec := hs
  h_cost := hc

noncomputable def bindCert {α β : Type} {SpecA : α → Prop} {SpecB : β → Prop} {b₁ b₂ : ℕ}
    (c₁ : CostM' α SpecA b₁)
    (f : (x : α) → SpecA x → CostM' β SpecB b₂) :
    CostM' β SpecB (b₁ + b₂) :=
  let nextProg : α → OpTrace β := fun x =>
    haveI := Classical.dec (SpecA x)
    if h : SpecA x then (f x h).prog else OpTrace.ret (f c₁.run.val c₁.h_spec).run.val
  let p : OpTrace β := OpTrace.seq c₁.prog nextProg
  have h_eval_c1 : c₁.prog.eval = c₁.run.val := (val_and_cost_linked c₁).1.symm
  have h_next : nextProg c₁.prog.eval = (f c₁.run.val c₁.h_spec).prog := by
    dsimp [nextProg]
    rw [h_eval_c1, dite_eq_left c₁.h_spec]
  { prog := p
    run := p.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val]
      dsimp [p, OpTrace.eval]
      rw [h_next]
      have h_sub := (val_and_cost_linked (f c₁.run.val c₁.h_spec)).1
      rw [← h_sub]
      exact (f c₁.run.val c₁.h_spec).h_spec
    h_cost := by
      rw [OpTrace.toCostM_cost]
      dsimp [p, OpTrace.steps]
      rw [h_next]
      have hc1 : c₁.prog.steps ≤ b₁ := by
        rw [← (val_and_cost_linked c₁).2]
        exact c₁.h_cost
      have hc2 : (f c₁.run.val c₁.h_spec).prog.steps ≤ b₂ := by
        rw [← (val_and_cost_linked (f c₁.run.val c₁.h_spec)).2]
        exact (f c₁.run.val c₁.h_spec).h_cost
      exact Nat.add_le_add hc1 hc2 }

def weakenBound {α : Type} {Spec : α → Prop} {b₁ b₂ : ℕ}
    (c : CostM' α Spec b₁) (h_le : b₁ ≤ b₂) :
    CostM' α Spec b₂ where
  prog := c.prog
  run := c.run
  h_link := c.h_link
  h_spec := c.h_spec
  h_cost := le_trans c.h_cost h_le


end CostM'

def CostM'.foldlCert {α β : Type} (stepCost : ℕ) (f : α → β → α) (init : α) (xs : List β) :
    CostM' α (fun res => res = xs.foldl f init) (xs.length * stepCost) :=
  let p := OpTrace.foldlOp stepCost f init xs
  { prog := p
    run := p.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val, OpTrace.foldlOp_eval]
    h_cost := by
      rw [OpTrace.toCostM_cost, OpTrace.foldlOp_steps] }


structure Verrou1_PolyTimeTrace where
  prog : (n p m : ℕ) → (F : InstanceSATPlus 2) → OpTrace (ZMod p)
  computeTrace : (n p m : ℕ) → (F : InstanceSATPlus 2) → CostM (ZMod p)
  h_link : ∀ (n p m : ℕ) (F : InstanceSATPlus 2),
    computeTrace n p m F = (prog n p m F).toCostM
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
  spec : ∀ (n p : ℕ) (_ : Nat.Prime p) (F : InstanceSATPlus 2) (oracle : ℕ → CostM (ZMod p)),
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


def computeTraceOp (V1 : Verrou1_PolyTimeTrace)
    (n : ℕ) (F : InstanceSATPlus 2) (p m : ℕ) :
    CostM' (ZMod p) (fun v => v = newtonSumMod 2 n p F m)
      (V1.poly_bound.eval (inputSizeSATPlus 2 n F + m + p)) :=
  { prog := V1.prog n p m F
    run := V1.computeTrace n p m F
    h_link := V1.h_link n p m F
    h_spec := V1.spec n p m F
    h_cost := V1.cost_le_poly n p m F }

def OpTrace.mapOp {α β : Type} (stepCost : ℕ) (f : α → β) : List α → OpTrace (List β)
  | [] => OpTrace.ret []
  | x :: xs =>
      OpTrace.seq (OpTrace.prim stepCost (f x)) (fun y =>
        OpTrace.seq (OpTrace.mapOp stepCost f xs) (fun ys =>
          OpTrace.ret (y :: ys)))


@[simp]
theorem OpTrace.mapOp_eval {α β : Type} (stepCost : ℕ) (f : α → β) (xs : List α) :
    (OpTrace.mapOp stepCost f xs).eval = xs.map f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp [OpTrace.mapOp, OpTrace.eval, List.map]
    rw [ih]

@[simp]
theorem OpTrace.mapOp_steps {α β : Type} (stepCost : ℕ) (f : α → β) (xs : List α) :
    (OpTrace.mapOp stepCost f xs).steps = xs.length * stepCost := by
  induction xs with
  | nil => simp [OpTrace.mapOp, OpTrace.steps]
  | cons x xs ih =>
    dsimp [OpTrace.mapOp, OpTrace.steps, List.length]
    rw [ih]
    ring


def OpTrace.filterOp {α : Type} (stepCost : ℕ) (p : α → Bool) : List α → OpTrace (List α)
  | [] => OpTrace.ret []
  | x :: xs =>
      OpTrace.seq (OpTrace.prim stepCost (p x)) (fun b =>
        OpTrace.seq (OpTrace.filterOp stepCost p xs) (fun ys =>
          OpTrace.ret (if b then x :: ys else ys)))

@[simp]
theorem OpTrace.filterOp_eval {α : Type} (stepCost : ℕ) (p : α → Bool) (xs : List α) :
    (OpTrace.filterOp stepCost p xs).eval = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    dsimp [OpTrace.filterOp, OpTrace.eval, List.filter]
    rw [ih]
    cases p x <;> rfl

@[simp]
theorem OpTrace.filterOp_steps {α : Type} (stepCost : ℕ) (p : α → Bool) (xs : List α) :
    (OpTrace.filterOp stepCost p xs).steps = xs.length * stepCost := by
  induction xs with
  | nil => simp [OpTrace.filterOp, OpTrace.steps]
  | cons x xs ih =>
    dsimp [OpTrace.filterOp, OpTrace.steps, List.length]
    rw [ih]
    ring





def mkCostM' {α : Type} {Spec : α → Prop} {bound : ℕ}
    (v : α) (c : ℕ) (hs : Spec v) (hc : c ≤ bound) : CostM' α Spec bound where
  prog := OpTrace.prim c v
  run := { val := v, cost := c }
  h_link := rfl
  h_spec := hs
  h_cost := hc


noncomputable def localRootsByRepSearch (n p : ℕ) (F : InstanceSATPlus 2) :
    List (ZMod p) :=
  ((List.finRange p).map (fun r : Fin p => (r.val : ZMod p))).filter
    (fun x : ZMod p => decide ((polyAssocieMod 2 n p F).eval x = 0))


def isConsistentWithLocalRoots (n : ℕ)
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i)))
    (k : Fin (2 ^ n)) : Prop :=
  ∀ i : Fin n, ((k : ℕ) : ZMod (canonicalPrimes n i)) ∈ localRoots i


noncomputable def recombineCRTVal (n : ℕ) (F : InstanceSATPlus 2) : Option (Fin (2 ^ n)) :=
  if h : (solFinset 2 n F).Nonempty then
    some (h.choose)
  else
    none


end P_NP_Def
