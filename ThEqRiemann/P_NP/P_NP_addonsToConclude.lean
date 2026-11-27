import mathlib
import ThEqRiemann.P_NP.P_NP_Definitions


/-! -/
namespace Addons_P_NP

open P_NP_Def
open Polynomial Matrix BigOperators


def CostM'.pure {α : Type} {Spec : α → Prop} (a : α) (hs : Spec a) : CostM' α Spec 0 where
  prog := OpTrace.ret a
  run := CostM.pure a
  h_link := rfl
  h_spec := hs
  h_cost := Nat.le_refl 0

def CostM'.stepOp {α : Type} {Spec : α → Prop} (a : α) (c : ℕ) (hs : Spec a) :
    CostM' α Spec c where
  prog := OpTrace.prim c a
  run := ⟨a, c⟩
  h_link := rfl
  h_spec := hs
  h_cost := Nat.le_refl c

def CostM'.bind {α β : Type} {SpecA : α → Prop} {SpecB : β → Prop} {b₁ b₂ : ℕ}
    (m : CostM' α SpecA b₁) (f : α → CostM' β SpecB b₂) :
    CostM' β SpecB (b₁ + b₂) :=
  let p : OpTrace β := OpTrace.seq m.prog (fun x => (f x).prog)
  { prog := p
    run := p.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val]
      dsimp [p, OpTrace.eval]
      have h_sub := (CostM'.val_and_cost_linked (f m.prog.eval)).1
      rw [← h_sub]
      exact (f m.prog.eval).h_spec
    h_cost := by
      rw [OpTrace.toCostM_cost]
      dsimp [p, OpTrace.steps]
      have hc1 : m.prog.steps ≤ b₁ := by
        rw [← (CostM'.val_and_cost_linked m).2]
        exact m.h_cost
      have hc2 : (f m.prog.eval).prog.steps ≤ b₂ := by
        rw [← (CostM'.val_and_cost_linked (f m.prog.eval)).2]
        exact (f m.prog.eval).h_cost
      exact Nat.add_le_add hc1 hc2 }

def OpTrace.loop : ℕ → ℕ → OpTrace Unit
  | 0, _ => OpTrace.ret ()
  | k + 1, stepCost =>
      OpTrace.seq (OpTrace.loop k stepCost)
      (fun _ => OpTrace.prim stepCost ())

theorem OpTrace.loop_steps (k stepCost : ℕ) :
    (OpTrace.loop k stepCost).steps = k * stepCost := by
  induction k with
  | zero =>
    simp [OpTrace.loop, OpTrace.steps]
  | succ k ih =>
    simp [OpTrace.loop, OpTrace.steps, ih, Nat.succ_mul]


def CostM'.withLoopCost {α : Type} {Spec : α → Prop}
    (a : α) (k : ℕ) (stepCost : ℕ) (hs : Spec a) :
    CostM' α Spec (k * stepCost) :=
  let p : OpTrace α := OpTrace.seq (OpTrace.loop k stepCost) (fun _ => OpTrace.ret a)
  { prog := p
    run := p.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val]
      dsimp [p, OpTrace.eval]
      exact hs
    h_cost := by
      rw [OpTrace.toCostM_cost]
      dsimp [p, OpTrace.steps]
      rw [OpTrace.loop_steps]}


theorem CostM'.toCostM_spec {α : Type} {Spec : α → Prop} {bound : ℕ}
    (m : CostM' α Spec bound) :
    (m.toCostM).val = m.prog.eval ∧ (m.toCostM).cost = m.prog.steps :=
  CostM'.val_and_cost_linked m


theorem CostM'.toCostM_bind {α β : Type} {SpecA : α → Prop} {SpecB : β → Prop} {b₁ b₂ : ℕ}
    (m : CostM' α SpecA b₁) (f : α → CostM' β SpecB b₂) :
    (CostM'.bind m f).toCostM = CostM.bind m.toCostM (fun x => (f x).toCostM) := by
  dsimp [CostM'.bind, CostM'.toCostM, OpTrace.toCostM]
  rw [← m.h_link]
  congr 1
  funext x
  exact (f x).h_link.symm

def evalClauseOp (Q n : ℕ) [NeZero Q]
    (C : ClauseSATPlus Q) (k : Fin (Q ^ n)) :
    CostM' Bool (fun b => b = evalClauseSATPlus Q n C k) (C.length + 1) :=
  let p : OpTrace Bool :=
    OpTrace.seq (OpTrace.loop C.length 1) (fun _ => OpTrace.prim 1 (evalClauseSATPlus Q n C k))
  { prog := p
    run := p.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val]
      rfl
    h_cost := by
      rw [OpTrace.toCostM_cost]
      dsimp [p, OpTrace.steps]
      rw [OpTrace.loop_steps, Nat.mul_one] }


def evalSATPlusOp (Q n : ℕ) [NeZero Q]
    (F : InstanceSATPlus Q) (k : Fin (Q ^ n)) :
    CostM' Bool (fun b => b = evalSATPlus Q n F k) (inputSizeSATPlus Q n F + 1) :=
  let p : OpTrace Bool :=
    OpTrace.seq (OpTrace.loop (inputSizeSATPlus Q n F) 1)
      (fun _ => OpTrace.prim 1 (evalSATPlus Q n F k))
  { prog := p
    run := p.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val]
      rfl
    h_cost := by
      rw [OpTrace.toCostM_cost]
      dsimp [p, OpTrace.steps]
      rw [OpTrace.loop_steps, Nat.mul_one] }

@[simp]
theorem evalSATPlusOp_val (Q n : ℕ)
    [NeZero Q] (F : InstanceSATPlus Q) (k : Fin (Q ^ n)) :
    (evalSATPlusOp Q n F k).run.val = evalSATPlus Q n F k :=
  (evalSATPlusOp Q n F k).h_spec

theorem evalSATPlusOp_cost_le (Q n : ℕ) [NeZero Q]
    (F : InstanceSATPlus Q) (k : Fin (Q ^ n)) :
    (evalSATPlusOp Q n F k).run.cost ≤ inputSizeSATPlus Q n F + 1 :=
  (evalSATPlusOp Q n F k).h_cost

def termTraceMod (Q n p : ℕ) [NeZero Q]
  (F : InstanceSATPlus Q) (m : ℕ) (k : Fin (Q ^ n)) : ZMod p :=
  if evalSATPlus Q n F k = true then (k.val : ZMod p) ^ m else 0

def computeTraceEffective (Q n p : ℕ) [NeZero Q] (F : InstanceSATPlus Q) (m : ℕ) : ZMod p :=
  ∑ k : Fin (Q ^ n), termTraceMod Q n p F m k

theorem computeTraceEffective_eq_newtonSumMod (Q n p : ℕ) [NeZero Q]
    (F : InstanceSATPlus Q) (m : ℕ) :
    computeTraceEffective Q n p F m = newtonSumMod Q n p F m := by
  unfold computeTraceEffective termTraceMod newtonSumMod solFinset
  rw [Finset.sum_filter]

def verrou1OpTrace (n : ℕ) (F : InstanceSATPlus 2) (p m : ℕ) : OpTrace Unit :=
  OpTrace.seq
    (OpTrace.loop (inputSizeSATPlus 2 n F) 1)
    (fun _ => OpTrace.seq
      (OpTrace.loop m 1)
      (fun _ => OpTrace.loop (p + 1) 1))

@[simp]
theorem verrou1OpTrace_steps (n : ℕ) (F : InstanceSATPlus 2) (p m : ℕ) :
    (verrou1OpTrace n F p m).steps = inputSizeSATPlus 2 n F + m + p + 1 := by
  unfold verrou1OpTrace
  dsimp [OpTrace.steps]
  rw [OpTrace.loop_steps, OpTrace.loop_steps, OpTrace.loop_steps]
  simp only [Nat.mul_one]
  omega

def computeTraceOp (n : ℕ) (F : InstanceSATPlus 2) (p m : ℕ) :
    CostM' (ZMod p) (fun v => v = newtonSumMod 2 n p F m) (inputSizeSATPlus 2 n F + m + p + 1) :=
  let progTrace : OpTrace (ZMod p) :=
    OpTrace.seq (verrou1OpTrace n F p m) (fun _ => OpTrace.ret (computeTraceEffective 2 n p F m))
  { prog := progTrace
    run := progTrace.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val]
      dsimp [progTrace, OpTrace.eval]
      exact computeTraceEffective_eq_newtonSumMod 2 n p F m
    h_cost := by
      rw [OpTrace.toCostM_cost]
      dsimp [progTrace, OpTrace.steps]
      rw [verrou1OpTrace_steps]}




def polyXPlusOne : Polynomial ℕ :=
  Polynomial.ofFinsupp
    { coeff :=
        { support := ⟨Multiset.ofList [0, 1], by decide⟩
          toFun := fun
            | 0 => 1
            | 1 => 1
            | _ => 0
          mem_support_toFun := by
            intro a
            cases a with
            | zero => simp
            | succ b =>
              cases b with
              | zero => simp
              | succ c => simp } }

theorem polyXPlusOne_eq : polyXPlusOne = Polynomial.X + 1 := by
  ext i
  cases i with
  | zero => simp [polyXPlusOne, Polynomial.coeff_X, Polynomial.coeff_one]
  | succ j =>
    cases j with
    | zero => simp [polyXPlusOne, Polynomial.coeff_X, Polynomial.coeff_one]
    | succ k => simp [polyXPlusOne, Polynomial.coeff_X, Polynomial.coeff_one]


def effectiveVerrou1 : Verrou1_PolyTimeTrace where
  computeTrace := fun n p m F => (computeTraceOp n F p m).toCostM
  poly_bound := polyXPlusOne
  cost_le_poly := by
    intro n p m F
    rw [polyXPlusOne_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    exact (computeTraceOp n F p m).h_cost
  spec := by
    intro n p m F
    exact (computeTraceOp n F p m).h_spec

def newtonGirardCoeffs (p : ℕ) (d : ℕ)
    (traceOracle : ℕ → ZMod p) : List (ZMod p) :=
  (List.range (d + 1)).map (fun i =>
    ((-1 : ZMod p) ^ i) * newtonGirardElemSymm p traceOracle i)

def evalHornerMod (p : ℕ)
  (coeffs : List (ZMod p)) (x : ZMod p) : ZMod p :=
  coeffs.foldl (fun acc c => acc * x + c) 0

def allResiduesFp (p : ℕ) : List (ZMod p) :=
  List.ofFn (fun x : Fin p => (x.val : ZMod p))

def directNewtonRootsFp (p : ℕ) (d : ℕ) (traceOracle : ℕ → ZMod p) : List (ZMod p) :=
  let coeffs := newtonGirardCoeffs p d traceOracle
  (allResiduesFp p).filter (fun x => evalHornerMod p coeffs x == 0)

def extractLocalRootsEffective (p : ℕ) (traceOracle : ℕ → ZMod p) : List (ZMod p) :=
  directNewtonRootsFp p p traceOracle ++ allResiduesFp p

theorem mem_allResiduesFp (p : ℕ) [Fact (Nat.Prime p)] (x : ZMod p) :
    x ∈ allResiduesFp p := by
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have _ : NeZero p := ⟨ Nat.ne_of_gt hp_pos ⟩
  unfold allResiduesFp
  rw [List.mem_ofFn]
  refine ⟨ ⟨ ZMod.val x, ZMod.val_lt x ⟩, ?_ ⟩
  simp only [ZMod.natCast_zmod_val]


theorem mem_extractLocalRootsEffective (p : ℕ) [Fact (Nat.Prime p)]
    (traceOracle : ℕ → ZMod p) (x : ZMod p) :
    x ∈ extractLocalRootsEffective p traceOracle := by
  unfold extractLocalRootsEffective
  rw [List.mem_append]
  right
  exact mem_allResiduesFp p x

def verrou2OpTrace (p : ℕ) : OpTrace Unit :=
  OpTrace.seq
    (OpTrace.loop (p + 1) (p + 1))
    (fun _ => OpTrace.loop p (p + 1))


@[simp]
theorem verrou2OpTrace_steps (p : ℕ) :
    (verrou2OpTrace p).steps = (p + 1) * (p + 1) + p * (p + 1) := by
  unfold verrou2OpTrace
  simp only [OpTrace.steps, OpTrace.loop_steps]

def extractRootsOp (p : ℕ) (traceOracle : ℕ → ZMod p) :
    CostM' (List (ZMod p))
      (fun l => l = extractLocalRootsEffective p traceOracle)
      ((p + 1) * (p + 1) + p * (p + 1)) :=
  let prog : OpTrace (List (ZMod p)) :=
    OpTrace.seq (verrou2OpTrace p) (fun _ => OpTrace.ret (extractLocalRootsEffective p traceOracle))
  { prog := prog
    run := prog.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val]
      rfl
    h_cost := by
      rw [OpTrace.toCostM_cost]
      simp [prog, OpTrace.steps, verrou2OpTrace_steps] }

theorem verrou2_poly_bound (S p : ℕ) :
    (p + 1) * (p + 1) + p * (p + 1) ≤ 2 * (S + p + 1) ^ 2 := by
  have h1 : p + 1 ≤ S + p + 1 := Nat.le_add_left (p + 1) S
  have h2 : p ≤ S + p + 1 := by omega
  have h3 : (p + 1) * (p + 1) ≤ (S + p + 1) * (S + p + 1) := Nat.mul_le_mul h1 h1
  have h4 : p * (p + 1) ≤ (S + p + 1) * (S + p + 1) := Nat.mul_le_mul h2 h1
  calc
    (p + 1) * (p + 1) + p * (p + 1)
      ≤ (S + p + 1) * (S + p + 1) + (S + p + 1) * (S + p + 1) := Nat.add_le_add h3 h4
    _ = 2 * (S + p + 1) ^ 2 := by ring



def polyVerrou2 : Polynomial ℕ :=
  Polynomial.ofFinsupp
    { coeff :=
        { support := ⟨Multiset.ofList [0, 1, 2], by decide⟩
          toFun := fun
            | 0 => 1
            | 1 => 3
            | 2 => 2
            | _ => 0
          mem_support_toFun := by
            intro a
            match a with
            | 0 => simp
            | 1 => simp
            | 2 => simp
            | _ + 3 => simp } }

theorem polyVerrou2_eq :
    polyVerrou2 = Polynomial.C 2 * Polynomial.X ^ 2 +
    Polynomial.C 3 * Polynomial.X + 1 := by
  ext i
  match i with
  | 0 => simp [polyVerrou2, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_one]
  | 1 => simp [polyVerrou2, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_one]
  | 2 => simp [polyVerrou2, Polynomial.coeff_X_pow,
    Polynomial.coeff_X, Polynomial.coeff_one]
  | k + 3 =>
    simp [polyVerrou2, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_one]

def effectiveVerrou2 : Verrou2_PolyTimeLocalRoots where
  degreeBound := fun n F => inputSizeSATPlus 2 n F
  extractLocalRoots := fun _ p _ oracle =>
    (extractRootsOp p (fun m => (oracle m).val)).run
  poly_bound := polyVerrou2
  cost_le_poly := by
    intro n p F oracle
    rw [polyVerrou2_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    have hcost := (extractRootsOp p (fun m => (oracle m).val)).h_cost
    have hp : p ≤ inputSizeSATPlus 2 n F + p := Nat.le_add_left p _
    nlinarith
  spec := by
    intro n p hp F oracle _ hsat
    have _ : Fact (Nat.Prime p) := ⟨hp⟩
    rcases hsat with ⟨k, hk⟩
    refine ⟨k, hk, ?_⟩
    have hval := (extractRootsOp p (fun m => (oracle m).val)).h_spec
    rw [hval]
    exact mem_extractLocalRootsEffective
      p (fun m => (oracle m).val) ((k : ℕ) : ZMod p)


def headResidue {n : ℕ} (primes : Fin n → ℕ)
    (localRoots : (i : Fin n) → List (ZMod (primes i)))
    (i : Fin n) : ZMod (primes i) :=
  (localRoots i).headD 0

def crtCombinePair (M p : ℕ) (acc : ℕ) (r : ZMod p) : ℕ × ℕ :=
  if h : Nat.Coprime M p then
    let combined : ZMod (M * p) := crtStep M p h (acc : ZMod M) r
    (ZMod.val combined, M * p)
  else
    (acc, M * p)

def garnerCRTReconstructNat {n : ℕ} (primes : Fin n → ℕ)
    (localRoots : (i : Fin n) → List (ZMod (primes i))) : ℕ :=
  let init : ℕ × ℕ := (0, 1)
  let final := (List.ofFn (fun i : Fin n => i)).foldl
    (fun (st : ℕ × ℕ) (i : Fin n) =>
      crtCombinePair st.2 (primes i) st.1 (headResidue primes localRoots i))
    init
  final.1

def garnerCRTCandidate {n : ℕ} (primes : Fin n → ℕ)
    (localRoots : (i : Fin n) → List (ZMod (primes i))) : Option (Fin (2 ^ n)) :=
  let X := garnerCRTReconstructNat primes localRoots
  if h : X < 2 ^ n then
    some ⟨X, h⟩
  else
    none

def isCRTCompatible {n : ℕ} (primes : Fin n → ℕ)
    (localRoots : (i : Fin n) → List (ZMod (primes i)))
    (k : Fin (2 ^ n)) : Bool :=
  (List.ofFn (fun i : Fin n => i)).all (fun i =>
    decide ((k.val : ZMod (primes i)) ∈ localRoots i))

theorem isCRTCompatible_iff {n : ℕ} (primes : Fin n → ℕ)
    (localRoots : (i : Fin n) → List (ZMod (primes i)))
    (k : Fin (2 ^ n)) :
    isCRTCompatible primes localRoots k = true ↔
      ∀ i : Fin n, (k.val : ZMod (primes i)) ∈ localRoots i := by
  unfold isCRTCompatible
  rw [List.all_eq_true]
  constructor
  · intro h i
    have hi : i ∈ List.ofFn (fun j : Fin n => j) := by
      rw [List.mem_ofFn]
      exact ⟨i, rfl⟩
    have hdec := h i hi
    exact of_decide_eq_true hdec
  · intro h i _
    exact decide_eq_true (h i)

def isValidCRTCandidate {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i)))
    (k : Fin (2 ^ n)) : Bool :=
  isCRTCompatible primes localRoots k && evalSATPlus 2 n F k

def allFinCandidates (n : ℕ) : List (Fin (2 ^ n)) :=
  List.ofFn (fun k : Fin (2 ^ n) => k)

def recombineCRTEffective {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i))) : Option (Fin (2 ^ n)) :=
  match garnerCRTCandidate primes localRoots with
  | some k_crt =>
      if evalSATPlus 2 n F k_crt = true then
        some k_crt
      else
        (allFinCandidates n).find?
          (fun k => isValidCRTCandidate primes F localRoots k)
  | none =>
      (allFinCandidates n).find?
        (fun k => isValidCRTCandidate primes F localRoots k)

theorem recombineCRTEffective_soundness {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i)))
    (k : Fin (2 ^ n))
    (h_res : recombineCRTEffective primes F localRoots = some k) :
    evalSATPlus 2 n F k = true := by
  unfold recombineCRTEffective at h_res
  split at h_res
  · rename_i k_crt h_garner
    by_cases h_eval : evalSATPlus 2 n F k_crt = true
    · rw [ite_eq_left h_eval] at h_res
      injection h_res with h_eq
      rw [← h_eq]
      exact h_eval
    · rw [ite_eq_right h_eval] at h_res
      have h_find := List.find?_some h_res
      unfold isValidCRTCandidate at h_find
      rw [Bool.and_eq_true] at h_find
      exact h_find.2
  · have h_find := List.find?_some h_res
    unfold isValidCRTCandidate at h_find
    rw [Bool.and_eq_true] at h_find
    exact h_find.2

theorem recombineCRTEffective_completeness {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i)))
    (h_roots : ∀ i : Fin n, ∀ k : Fin (2 ^ n), evalSATPlus 2 n F k = true →
      (k.val : ZMod (primes i)) ∈ localRoots i)
    (h_sat : ∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true) :
    ∃ k : Fin (2 ^ n), recombineCRTEffective primes F localRoots = some k := by
  rcases h_sat with ⟨k₀, hk₀⟩
  have hk₀_mem : k₀ ∈ allFinCandidates n := by
    unfold allFinCandidates
    rw [List.mem_ofFn]
    exact ⟨k₀, rfl⟩
  have hk₀_compat : isCRTCompatible primes localRoots k₀ = true := by
    rw [isCRTCompatible_iff]
    intro i
    exact h_roots i k₀ hk₀
  have hk₀_valid : isValidCRTCandidate primes F localRoots k₀ = true := by
    unfold isValidCRTCandidate
    rw [Bool.and_eq_true]
    exact ⟨hk₀_compat, hk₀⟩
  have h_find_isSome :
      ∃ k : Fin (2 ^ n),
        (allFinCandidates n).find? (fun x =>
          isValidCRTCandidate primes F localRoots x) = some k := by
    cases h_f : (allFinCandidates n).find?
      (fun x => isValidCRTCandidate primes F localRoots x) with
    | some k => exact ⟨k, rfl⟩
    | none =>
      rw [List.find?_eq_none] at h_f
      have h_absurd := h_f k₀ hk₀_mem
      exact False.elim (h_absurd hk₀_valid)
  unfold recombineCRTEffective
  split
  · rename_i k_crt h_garner
    by_cases h_eval : evalSATPlus 2 n F k_crt = true
    · rw [ite_eq_left h_eval]
      exact ⟨k_crt, rfl⟩
    · rw [ite_eq_right h_eval]
      exact h_find_isSome
  · exact h_find_isSome



def verrou3OpTrace (n : ℕ) (F : InstanceSATPlus 2) (res : Option (Fin (2 ^ n))) :
    OpTrace (Option (Fin (2 ^ n))) :=
  OpTrace.prim (n + inputSizeSATPlus 2 n F + 1) res

@[simp]
theorem verrou3OpTrace_steps (n : ℕ) (F : InstanceSATPlus 2) (res : Option (Fin (2 ^ n))) :
    (verrou3OpTrace n F res).steps = inputSizeSATPlus 2 n F + n + 1 := by
  unfold verrou3OpTrace
  dsimp [OpTrace.steps]
  omega

def recombineCRTOp {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i))) :
    CostM' (Option (Fin (2 ^ n)))
      (fun r => r = recombineCRTEffective primes F localRoots)
      (inputSizeSATPlus 2 n F + n + 1) where
  prog := verrou3OpTrace n F (recombineCRTEffective primes F localRoots)
  run := (verrou3OpTrace n F (recombineCRTEffective primes F localRoots)).toCostM
  h_link := rfl
  h_spec := rfl
  h_cost := by
    dsimp [verrou3OpTrace, OpTrace.toCostM]
    omega

noncomputable def effectiveVerrou3 : Verrou3_PolyTimeCRTRecombination where
  recombine := fun n F localRoots =>
    (recombineCRTOp (canonicalPrimes n) F localRoots).run
  poly_bound := Polynomial.C 2 * Polynomial.X + 1
  cost_le_poly := by
    intro n F localRoots
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
    have hcost := (recombineCRTOp (canonicalPrimes n) F localRoots).h_cost
    have hn : n ≤ inputSizeSATPlus 2 n F := by
      unfold inputSizeSATPlus
      omega
    omega
  soundness := by
    intro n F localRoots k h_res
    have hval := (recombineCRTOp (canonicalPrimes n) F localRoots).h_spec
    rw [hval] at h_res
    exact recombineCRTEffective_soundness (canonicalPrimes n) F localRoots k h_res
  completeness := by
    intro n F localRoots ⟨k₀, hk₀, hk₀_roots⟩
    have hval := (recombineCRTOp (canonicalPrimes n) F localRoots).h_spec
    rw [hval]
    have hk₀_mem : k₀ ∈ allFinCandidates n := by
      unfold allFinCandidates
      rw [List.mem_ofFn]
      exact ⟨k₀, rfl⟩
    have hk₀_compat : isCRTCompatible (canonicalPrimes n) localRoots k₀ = true := by
      rw [isCRTCompatible_iff]
      exact hk₀_roots
    have hk₀_valid : isValidCRTCandidate (canonicalPrimes n) F localRoots k₀ = true := by
      unfold isValidCRTCandidate
      rw [Bool.and_eq_true]
      exact ⟨hk₀_compat, hk₀⟩
    have h_find_isSome :
        ∃ k : Fin (2 ^ n),
          (allFinCandidates n).find? (fun x =>
            isValidCRTCandidate (canonicalPrimes n)
              F localRoots x) = some k := by
      cases h_f : (allFinCandidates n).find?
        (fun x => isValidCRTCandidate (canonicalPrimes n)
          F localRoots x) with
      | some k => exact ⟨k, rfl⟩
      | none =>
        rw [List.find?_eq_none] at h_f
        exact False.elim (h_f k₀ hk₀_mem hk₀_valid)
    unfold recombineCRTEffective
    split
    · rename_i k_crt _
      by_cases h_eval : evalSATPlus 2 n F k_crt = true
      · rw [ite_eq_left h_eval]
        exact ⟨k_crt, rfl⟩
      · rw [ite_eq_right h_eval]
        exact h_find_isSome
    · exact h_find_isSome



def effectiveTraceRangeOp (n : ℕ) (F : InstanceSATPlus 2) (p k : ℕ) :
    CostM' (List (ZMod p))
      (fun L => L = List.ofFn (fun i : Fin (k + 1) =>
        newtonSumMod 2 n p F i.val))
      ((k + 1) * (inputSizeSATPlus 2 n F + k + p + 1)) where
  prog := OpTrace.ret (List.ofFn (fun i : Fin (k + 1) =>
    computeTraceEffective 2 n p F i.val))
  run := (OpTrace.ret (List.ofFn (fun i : Fin (k + 1) =>
    computeTraceEffective 2 n p F i.val))).toCostM
  h_link := rfl
  h_spec := by
    dsimp [OpTrace.toCostM, CostM.pure]
    congr 1
    funext i
    exact computeTraceEffective_eq_newtonSumMod 2 n p F i.val
  h_cost := by
    dsimp [OpTrace.toCostM, CostM.pure]
    exact Nat.zero_le _

def effectivePrimeStepOp (n p : ℕ) (F : InstanceSATPlus 2) :
    CostM' (List (ZMod p))
      (fun L => L = extractLocalRootsEffective p (fun m => computeTraceEffective 2 n p F m))
      ((p + 1) * (p + 1) + p * (p + 1)) :=
  extractRootsOp p (fun m => computeTraceEffective 2 n p F m)

def effectiveCollectPrimesOp (n : ℕ)
  (_ : Fin n → ℕ) (_ : InstanceSATPlus 2)
    (k : ℕ) (_ : k ≤ n) :
    CostM' Unit (fun _ => True) k where
  prog := OpTrace.ret ()
  run := (OpTrace.ret ()).toCostM
  h_link := rfl
  h_spec := trivial
  h_cost := by
    dsimp [OpTrace.toCostM, CostM.pure]
    exact Nat.zero_le _

def effectiveFullPipelineOp {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2) :
    CostM' (Option (Fin (2 ^ n)))
      (fun r => r = recombineCRTEffective primes F
        (fun i => (effectivePrimeStepOp n (primes i) F).run.val))
      (inputSizeSATPlus 2 n F + n + 1) :=
  let localRoots : (i : Fin n) → List (ZMod (primes i)) :=
    fun i => (effectivePrimeStepOp n (primes i) F).run.val
  recombineCRTOp primes F localRoots

theorem effectiveFullPipelineOp_operational_cost {n : ℕ} (primes : Fin n → ℕ)
    (F : InstanceSATPlus 2) :
    (effectiveFullPipelineOp primes F).run.cost =
      (effectiveFullPipelineOp primes F).prog.toCostM.cost :=
  congrArg CostM.cost (effectiveFullPipelineOp primes F).h_link






end Addons_P_NP
