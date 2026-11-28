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

def extractLocalRootsEffective (p d : ℕ) (traceOracle : ℕ → ZMod p) : List (ZMod p) :=
  directNewtonRootsFp p d traceOracle

theorem mem_allResiduesFp (p : ℕ) [Fact (Nat.Prime p)] (x : ZMod p) :
    x ∈ allResiduesFp p := by
  have hp_pos : 0 < p := (Fact.out : Nat.Prime p).pos
  have _ : NeZero p := ⟨ Nat.ne_of_gt hp_pos ⟩
  unfold allResiduesFp
  rw [List.mem_ofFn]
  refine ⟨ ⟨ ZMod.val x, ZMod.val_lt x ⟩, ?_ ⟩
  simp only [ZMod.natCast_zmod_val]

def verrou2RealProg (p d : ℕ) (traceOracle : ℕ → ZMod p) : OpTrace (List (ZMod p)) :=
  OpTrace.seq
    (OpTrace.mapOp (d + 1)
      (fun i => ((-1 : ZMod p) ^ i) * newtonGirardElemSymm p traceOracle i)
      (List.range (d + 1)))
    (fun coeffs =>
      OpTrace.filterOp (d + 1)
        (fun x => evalHornerMod p coeffs x == 0)
        (allResiduesFp p))

@[simp]
theorem verrou2RealProg_eval (p d : ℕ) (traceOracle : ℕ → ZMod p) :
    (verrou2RealProg p d traceOracle).eval = extractLocalRootsEffective p d traceOracle := by
  unfold verrou2RealProg extractLocalRootsEffective directNewtonRootsFp newtonGirardCoeffs
  simp only [OpTrace.eval, OpTrace.mapOp_eval, OpTrace.filterOp_eval]

@[simp]
theorem verrou2RealProg_steps (p d : ℕ) (traceOracle : ℕ → ZMod p) :
    (verrou2RealProg p d traceOracle).steps = (d + 1) * (d + 1) + p * (d + 1) := by
  unfold verrou2RealProg
  simp only [OpTrace.steps, OpTrace.mapOp_eval, OpTrace.mapOp_steps,
    OpTrace.filterOp_steps, List.length_range, allResiduesFp, List.length_ofFn]


def extractRootsOp (p d : ℕ) (traceOracle : ℕ → ZMod p) :
    CostM' (List (ZMod p))
      (fun l => l = extractLocalRootsEffective p d traceOracle)
      ((d + 1) * (d + 1) + p * (d + 1)) :=
  let prog := verrou2RealProg p d traceOracle
  { prog := prog
    run := prog.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val, verrou2RealProg_eval]
    h_cost := by
      rw [OpTrace.toCostM_cost, verrou2RealProg_steps] }

theorem mem_directNewtonRootsFp_iff (p d : ℕ) [Fact (Nat.Prime p)]
    (traceOracle : ℕ → ZMod p) (x : ZMod p) :
    x ∈ directNewtonRootsFp p d traceOracle ↔
      evalHornerMod p (newtonGirardCoeffs p d traceOracle) x = 0 := by
  unfold directNewtonRootsFp
  rw [List.mem_filter, beq_iff_eq]
  constructor
  · intro h
    exact h.2
  · intro h_zero
    exact ⟨mem_allResiduesFp p x, h_zero⟩

lemma newtonGirardElemSymm_congr (p : ℕ) (μ₁ μ₂ : ℕ → ZMod p)
    (h : ∀ m, μ₁ m = μ₂ m) :
    ∀ i : ℕ, newtonGirardElemSymm p μ₁ i = newtonGirardElemSymm p μ₂ i := by
  intro i
  rw [funext h]

lemma newtonGirardCoeffs_congr (p d : ℕ) (μ₁ μ₂ : ℕ → ZMod p)
    (h : ∀ m, μ₁ m = μ₂ m) :
    newtonGirardCoeffs p d μ₁ = newtonGirardCoeffs p d μ₂ := by
  unfold newtonGirardCoeffs
  apply List.map_congr_left
  intro i _
  rw [newtonGirardElemSymm_congr p μ₁ μ₂ h i]

lemma mem_solFinset_iff (Q n : ℕ) (F : InstanceSATPlus Q) (k : Fin (Q ^ n)) :
    k ∈ solFinset Q n F ↔ evalSATPlus Q n F k = true := by
  unfold solFinset
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

lemma polyAssocieMod_eval_eq_zero_of_sat (Q n p : ℕ) (F : InstanceSATPlus Q)
    (k : Fin (Q ^ n)) (hk : evalSATPlus Q n F k = true) :
    Polynomial.eval ((k : ℕ) : ZMod p) (polyAssocieMod Q n p F) = 0 := by
  unfold polyAssocieMod
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := k)
  · exact (mem_solFinset_iff Q n F k).mpr hk
  · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

lemma evalHornerMod_map_range (p : ℕ) (c : ℕ → ZMod p) (x : ZMod p) :
    ∀ d : ℕ,
      evalHornerMod p ((List.range (d + 1)).map c) x =
        ∑ i ∈ Finset.range (d + 1), c i * x ^ (d - i)
  | 0 => by
    simp [evalHornerMod]
  | d + 1 => by
    unfold evalHornerMod
    rw [List.range_succ, List.map_append,
      List.map_singleton, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    change (evalHornerMod p ((List.range (d + 1)).map c) x) *
      x + c (d + 1) = _
    rw [evalHornerMod_map_range p c x d]
    conv_rhs => rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    rw [Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hi_le : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [mul_assoc, ← pow_succ, Nat.succ_sub hi_le]

def elemSymmFinset {α : Type*} [DecidableEq α] (p : ℕ) (S : Finset α)
    (f : α → ZMod p) (i : ℕ) : ZMod p :=
  ∑ A ∈ S.powersetCard i, ∏ k ∈ A, f k

lemma elemSymmFinset_zero {α : Type*} [DecidableEq α] (p : ℕ) (S : Finset α)
    (f : α → ZMod p) :
    elemSymmFinset p S f 0 = 1 := by
  simp [elemSymmFinset]

lemma elemSymmFinset_eq_zero_of_gt {α : Type*} [DecidableEq α] (p : ℕ) (S : Finset α)
    (f : α → ZMod p) {i : ℕ} (hi : S.card < i) :
    elemSymmFinset p S f i = 0 := by
  unfold elemSymmFinset
  rw [Finset.powersetCard_eq_empty.mpr hi, Finset.sum_empty]

lemma prod_sub_eq_sum_elemSymmFinset {α : Type*} [DecidableEq α] (p : ℕ) (S : Finset α)
    (f : α → ZMod p) (x : ZMod p) :
    ∏ k ∈ S, (x - f k) =
      ∑ i ∈ Finset.range (S.card + 1),
        ((-1 : ZMod p) ^ i) * elemSymmFinset p S f i * x ^ (S.card - i) := by
  have h_expand : ∏ k ∈ S, (x - f k) =
      ∑ A ∈ S.powerset, (∏ k ∈ A, (- f k)) * x ^ (S.card - A.card) := by
    conv_lhs =>
      arg 2; ext k
      rw [sub_eq_add_neg, add_comm]
    rw [Finset.prod_add]
    apply Finset.sum_congr rfl
    intro A hA
    rw [Finset.prod_const, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hA)]
  have h_union : S.powerset = (Finset.range (S.card + 1)).biUnion (fun i => S.powersetCard i) := by
    ext A
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard, Finset.mem_powerset]
    exact ⟨fun hA => ⟨A.card, Nat.lt_succ_of_le (Finset.card_le_card hA), hA, rfl⟩,
           fun ⟨_, _, hA, _⟩ => hA⟩
  rw [h_expand, h_union, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i _
    unfold elemSymmFinset
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A hA
    have hcard : A.card = i := (Finset.mem_powersetCard.mp hA).2
    rw [hcard, Finset.prod_neg, hcard]
  · intro i _ j _ hij
    exact Finset.disjoint_left.mpr (fun A hAi hAj =>
      hij ((Finset.mem_powersetCard.mp hAi).2.symm.trans (Finset.mem_powersetCard.mp hAj).2))


lemma elemSymmFinset_insert_succ {α : Type*} [DecidableEq α] (p : ℕ) (S : Finset α)
    (f : α → ZMod p) {a : α} (ha : a ∉ S) (k : ℕ) :
    elemSymmFinset p (insert a S) f (k + 1) =
      elemSymmFinset p S f (k + 1) + f a * elemSymmFinset p S f k := by
  unfold elemSymmFinset
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union]
  · congr 1
    rw [Finset.sum_image]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B hB
      have haB : a ∉ B := fun h => ha ((Finset.mem_powersetCard.mp hB).1 h)
      exact Finset.prod_insert haB
    · intro B₁ hB₁ B₂ hB₂ h_eq
      have haB₁ : a ∉ B₁ := fun h => ha ((Finset.mem_powersetCard.mp hB₁).1 h)
      have haB₂ : a ∉ B₂ := fun h => ha ((Finset.mem_powersetCard.mp hB₂).1 h)
      have := congrArg (fun T => T.erase a) h_eq
      simpa only [Finset.erase_insert haB₁, Finset.erase_insert haB₂] using this
  · rw [Finset.disjoint_left]
    intro A hA_S hA_img
    rcases Finset.mem_image.mp hA_img with ⟨B, _, rfl⟩
    exact ha ((Finset.mem_powersetCard.mp hA_S).1 (Finset.mem_insert_self a B))

lemma sum_alternating_elemSymm_insert_pow {α : Type*} [DecidableEq α] (p : ℕ) (S : Finset α)
    (f : α → ZMod p) {a : α} (ha : a ∉ S) :
    ∀ m : ℕ,
      (∑ j ∈ Finset.range (m + 1),
        ((-1 : ZMod p) ^ j) * elemSymmFinset p (insert a S) f (m - j) * f a ^ (j + 1)) =
      f a * elemSymmFinset p S f m
  | 0 => by
    simp [elemSymmFinset_zero]
  | m + 1 => by
    rw [Finset.sum_range_succ']
    have h_shift :
        (∑ j ∈ Finset.range (m + 1),
          ((-1 : ZMod p) ^ (j + 1)) * elemSymmFinset p
            (insert a S) f (m + 1 - (j + 1)) * f a ^ (j + 1 + 1)) =
        (- f a) * (∑ j ∈ Finset.range (m + 1),
          ((-1 : ZMod p) ^ j) * elemSymmFinset p (insert a S) f (m - j) * f a ^ (j + 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [Nat.succ_sub_succ, pow_succ, pow_succ]
      ring
    rw [h_shift, sum_alternating_elemSymm_insert_pow p S f ha m]
    simp only [pow_zero, one_mul, Nat.sub_zero, zero_add, pow_one]
    rw [elemSymmFinset_insert_succ p S f ha m]
    ring

lemma newton_girard_identity_finset_range {α : Type*} [DecidableEq α] (p : ℕ) (S : Finset α)
    (f : α → ZMod p) :
    ∀ m : ℕ,
      ((m + 1 : ℕ) : ZMod p) * elemSymmFinset p S f (m + 1) =
        ∑ j ∈ Finset.range (m + 1),
          ((-1 : ZMod p) ^ j) * elemSymmFinset p S f (m - j) *
            (∑ k ∈ S, f k ^ (j + 1)) := by
  induction S using Finset.induction_on with
  | empty =>
    intro m
    have h_zero : elemSymmFinset p (∅ : Finset α) f (m + 1) = 0 :=
      elemSymmFinset_eq_zero_of_gt p ∅ f (Nat.succ_pos m)
    simp [h_zero]
  | @insert a S ha ih =>
    intro m
    have h_split :
        (∑ j ∈ Finset.range (m + 1),
          ((-1 : ZMod p) ^ j) * elemSymmFinset p (insert a S) f (m - j) *
            (∑ k ∈ insert a S, f k ^ (j + 1))) =
        (∑ j ∈ Finset.range (m + 1),
          ((-1 : ZMod p) ^ j) * elemSymmFinset p (insert a S) f (m - j) * f a ^ (j + 1)) +
        (∑ j ∈ Finset.range (m + 1),
          ((-1 : ZMod p) ^ j) * elemSymmFinset p
            (insert a S) f (m - j) * (∑ k ∈ S, f k ^ (j + 1))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_insert ha, mul_add]
    rw [h_split]
    rw [sum_alternating_elemSymm_insert_pow p S f ha m]
    cases m with
    | zero =>
      have ih0 := ih 0
      simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul, Nat.sub_zero,
        zero_add, pow_one, elemSymmFinset_zero] at ih0 ⊢
      rw [elemSymmFinset_insert_succ p S f ha 0, elemSymmFinset_zero]
      linear_combination ih0
    | succ m' =>
      rw [Finset.sum_range_succ]
      have h_pascal_sum :
          (∑ j ∈ Finset.range (m' + 1),
            ((-1 : ZMod p) ^ j) * elemSymmFinset p (insert a S) f (m' + 1 - j) *
              (∑ k ∈ S, f k ^ (j + 1))) =
          (∑ j ∈ Finset.range (m' + 1),
            ((-1 : ZMod p) ^ j) * elemSymmFinset p S f (m' + 1 - j) *
              (∑ k ∈ S, f k ^ (j + 1))) +
          f a * (∑ j ∈ Finset.range (m' + 1),
            ((-1 : ZMod p) ^ j) * elemSymmFinset p S f (m' - j) *
              (∑ k ∈ S, f k ^ (j + 1))) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        have hj_le : j ≤ m' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have h_sub : m' + 1 - j = (m' - j) + 1 := Nat.succ_sub hj_le
        rw [h_sub, elemSymmFinset_insert_succ p S f ha (m' - j)]
        ring
      rw [h_pascal_sum]
      have h_last :
          ((-1 : ZMod p) ^ (m' + 1)) * elemSymmFinset p (insert a S) f (m' + 1 - (m' + 1)) *
            (∑ k ∈ S, f k ^ (m' + 1 + 1)) =
          ((-1 : ZMod p) ^ (m' + 1)) * elemSymmFinset p S f (m' + 1 - (m' + 1)) *
            (∑ k ∈ S, f k ^ (m' + 1 + 1)) := by
        simp [elemSymmFinset_zero]
      rw [h_last]
      have h_ih_succ :
          (∑ j ∈ Finset.range (m' + 1),
            ((-1 : ZMod p) ^ j) * elemSymmFinset p S f (m' + 1 - j) * (∑ k ∈ S, f k ^ (j + 1))) +
          ((-1 : ZMod p) ^ (m' + 1)) * elemSymmFinset p S f (m' + 1 - (m' + 1)) *
            (∑ k ∈ S, f k ^ (m' + 1 + 1)) =
          ((m' + 2 : ℕ) : ZMod p) * elemSymmFinset p S f (m' + 2) := by
        rw [← Finset.sum_range_succ, ← ih (m' + 1)]
      rw [← ih m', elemSymmFinset_insert_succ p S f ha (m' + 1)]
      push_cast at h_ih_succ ⊢
      linear_combination -h_ih_succ


lemma newton_girard_identity_finset {α : Type*} [DecidableEq α] (p : ℕ) (S : Finset α)
    (f : α → ZMod p) (m : ℕ) :
    ((m + 1 : ℕ) : ZMod p) * elemSymmFinset p S f (m + 1) =
      ∑ j : Fin (m + 1),
        ((-1 : ZMod p) ^ j.val) * elemSymmFinset p S f ((m + 1) - (j.val + 1)) *
          (∑ k ∈ S, f k ^ (j.val + 1)) := by
  rw [Fin.sum_univ_eq_sum_range
    (fun j => ((-1 : ZMod p) ^ j) * elemSymmFinset p S f ((m + 1) - (j + 1)) *
      (∑ k ∈ S, f k ^ (j + 1)))]
  simp only [Nat.succ_sub_succ]
  exact newton_girard_identity_finset_range p S f m

lemma newtonGirardElemSymm_eq_elemSymmFinset {α : Type*} [DecidableEq α]
    (p : ℕ) (hp : Nat.Prime p) (S : Finset α) (f : α → ZMod p) :
    ∀ i : ℕ, i < p →
      newtonGirardElemSymm p (fun m => ∑ k ∈ S, f k ^ m) i = elemSymmFinset p S f i
  | 0, _ => by
    simp [newtonGirardElemSymm, elemSymmFinset_zero]
  | m + 1, hm => by
    have _ : Fact (Nat.Prime p) := ⟨hp⟩
    simp only [newtonGirardElemSymm]
    have h_sum :
        (∑ j : Fin (m + 1),
          ((-1 : ZMod p) ^ j.val) *
            newtonGirardElemSymm p (fun r => ∑ k ∈ S, f k ^ r) ((m + 1) - (j.val + 1)) *
            (∑ k ∈ S, f k ^ (j.val + 1))) =
        (∑ j : Fin (m + 1),
          ((-1 : ZMod p) ^ j.val) *
            elemSymmFinset p S f ((m + 1) - (j.val + 1)) *
            (∑ k ∈ S, f k ^ (j.val + 1))) := by
      apply Finset.sum_congr rfl
      intro j _
      have h_idx_lt : (m + 1) - (j.val + 1) < p :=
        lt_trans (Nat.sub_lt (Nat.succ_pos m) (Nat.succ_pos j.val)) hm
      rw [newtonGirardElemSymm_eq_elemSymmFinset p hp S f ((m + 1) - (j.val + 1)) h_idx_lt]
    rw [h_sum, ← newton_girard_identity_finset p S f m]
    have h_ne_zero : ((m + 1 : ℕ) : ZMod p) ≠ 0 := by
      intro h_zero
      have h_dvd : p ∣ (m + 1) := (ZMod.natCast_eq_zero_iff (m + 1) p).mp h_zero
      exact absurd (Nat.le_of_dvd (Nat.succ_pos m) h_dvd) (not_le_of_gt hm)
    rw [← mul_assoc, inv_mul_cancel₀ h_ne_zero, one_mul]


lemma evalHornerMod_newtonGirardCoeffs_eq_polyAssocieMod
    (n p : ℕ) (hp : Nat.Prime p) (F : InstanceSATPlus 2) (x : ZMod p)
    (h_card : (solFinset 2 n F).card ≤ inputSizeSATPlus 2 n F)
    (h_deg : inputSizeSATPlus 2 n F < p) :
    ∃ qFactor : ZMod p,
      evalHornerMod p (newtonGirardCoeffs p (inputSizeSATPlus 2 n F) (newtonSumMod 2 n p F)) x =
        qFactor * Polynomial.eval x (polyAssocieMod 2 n p F) := by
  set d := inputSizeSATPlus 2 n F
  set S := solFinset 2 n F
  set f : Fin (2 ^ n) → ZMod p := fun k => ((k : ℕ) : ZMod p)
  refine ⟨x ^ (d - S.card), ?_⟩
  unfold newtonGirardCoeffs
  rw [evalHornerMod_map_range]
  have h_eq_sum :
      (∑ i ∈ Finset.range (d + 1),
        ((-1 : ZMod p) ^ i) * newtonGirardElemSymm p (newtonSumMod 2 n p F) i * x ^ (d - i)) =
      (∑ i ∈ Finset.range (d + 1),
        ((-1 : ZMod p) ^ i) * elemSymmFinset p S f i * x ^ (d - i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi_lt : i < p := lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) h_deg
    change ((-1 : ZMod p) ^ i) * newtonGirardElemSymm p
      (fun m => ∑ k ∈ S, f k ^ m) i * x ^ (d - i) = _
    rw [newtonGirardElemSymm_eq_elemSymmFinset p hp S f i hi_lt]
  rw [h_eq_sum]
  have h_trunc :
      (∑ i ∈ Finset.range (d + 1),
        ((-1 : ZMod p) ^ i) * elemSymmFinset p S f i * x ^ (d - i)) =
      (∑ i ∈ Finset.range (S.card + 1),
        ((-1 : ZMod p) ^ i) * elemSymmFinset p S f i * x ^ (d - i)) := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ h_card))
    intro i _ hi_not
    have hi_gt : S.card < i := by
      rw [Finset.mem_range] at hi_not
      omega
    rw [elemSymmFinset_eq_zero_of_gt p S f hi_gt, mul_zero, zero_mul]
  rw [h_trunc]
  unfold polyAssocieMod
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [prod_sub_eq_sum_elemSymmFinset p S f x, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi_le : i ≤ S.card := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h_exp : (d - S.card) + (S.card - i) = d - i := by omega
  calc
    ((-1 : ZMod p) ^ i) * elemSymmFinset p S f i * x ^ (d - i)
      = ((-1 : ZMod p) ^ i) * elemSymmFinset p S f i * x ^ ((d - S.card) + (S.card - i)) := by
          rw [h_exp]
    _ = x ^ (d - S.card) * (((-1 : ZMod p) ^ i) * elemSymmFinset p S f i * x ^ (S.card - i)) := by
          rw [pow_add]; ring

theorem newtonGirard_horner_annihilates_solution
    (n p : ℕ) (hp : Nat.Prime p) (F : InstanceSATPlus 2)
    (h_card : (solFinset 2 n F).card ≤ inputSizeSATPlus 2 n F)
    (h_lt : inputSizeSATPlus 2 n F < p)
    (traceOracle : ℕ → ZMod p)
    (h_oracle : ∀ m, traceOracle m = newtonSumMod 2 n p F m)
    (k : Fin (2 ^ n)) (hk : evalSATPlus 2 n F k = true) :
    evalHornerMod p (newtonGirardCoeffs p
      (inputSizeSATPlus 2 n F) traceOracle) ((k : ℕ) : ZMod p) = 0 := by
  rw [newtonGirardCoeffs_congr p (inputSizeSATPlus 2 n F)
    traceOracle (newtonSumMod 2 n p F) h_oracle]
  obtain ⟨qFactor, h_bridge⟩ :=
    evalHornerMod_newtonGirardCoeffs_eq_polyAssocieMod n p hp F ((k : ℕ) : ZMod p) h_card h_lt
  rw [h_bridge]
  rw [polyAssocieMod_eval_eq_zero_of_sat 2 n p F k hk]
  exact mul_zero qFactor


theorem mem_extractLocalRootsEffective_iff (p d : ℕ) [Fact (Nat.Prime p)]
    (traceOracle : ℕ → ZMod p) (x : ZMod p) :
    x ∈ extractLocalRootsEffective p d traceOracle ↔
      evalHornerMod p (newtonGirardCoeffs p d traceOracle) x = 0 := by
  unfold extractLocalRootsEffective
  exact mem_directNewtonRootsFp_iff p d traceOracle x


def verrou2OpTrace (p : ℕ) : OpTrace Unit :=
  OpTrace.seq
    (OpTrace.loop (p + 1) (p + 1))
    (fun _ => OpTrace.loop p (p + 1))


@[simp]
theorem verrou2OpTrace_steps (p : ℕ) :
    (verrou2OpTrace p).steps = (p + 1) * (p + 1) + p * (p + 1) := by
  unfold verrou2OpTrace
  simp only [OpTrace.steps, OpTrace.loop_steps]


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

def recombineCRTEffective {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i))) : Option (Fin (2 ^ n)) :=
  match garnerCRTCandidate primes localRoots with
  | some k_crt =>
      if evalSATPlus 2 n F k_crt = true then
        some k_crt
      else
        none
  | none => none


def verrou3RealProg {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i))) : OpTrace (Option (Fin (2 ^ n))) :=
  OpTrace.seq
    (OpTrace.foldlOp 1
      (fun (st : ℕ × ℕ) (i : Fin n) =>
        crtCombinePair st.2 (primes i) st.1 (headResidue primes localRoots i))
      (0, 1)
      (List.ofFn (fun i : Fin n => i)))
    (fun finalState =>
      let X := finalState.1
      if h : X < 2 ^ n then
        let k_crt : Fin (2 ^ n) := ⟨X, h⟩
        OpTrace.seq
          (evalSATPlusOp 2 n F k_crt).prog
          (fun b => OpTrace.ret (if b = true then some k_crt else none))
      else
        OpTrace.prim (inputSizeSATPlus 2 n F + 1) none)

@[simp]
theorem verrou3RealProg_eval {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i))) :
    (verrou3RealProg primes F localRoots).eval = recombineCRTEffective primes F localRoots := by
  unfold verrou3RealProg recombineCRTEffective garnerCRTCandidate garnerCRTReconstructNat
  simp only [OpTrace.eval, OpTrace.foldlOp_eval]
  split
  · rename_i h_lt
    dsimp [OpTrace.eval]
    have h_eval_sat : ∀ x : Fin (2 ^ n),
        (evalSATPlusOp 2 n F x).prog.eval = evalSATPlus 2 n F x := fun x => by
      rw [← (CostM'.val_and_cost_linked (evalSATPlusOp 2 n F x)).1]
      exact (evalSATPlusOp 2 n F x).h_spec
    rw [h_eval_sat]
    have h_cand : ∀ (h : (OpTrace.foldlOp 1
        (fun st i => crtCombinePair st.2 (primes i) st.1 (headResidue primes localRoots i))
        (0, 1) (List.ofFn fun i => i)).eval.1 < 2 ^ n),
        (⟨_, h⟩ : Fin (2 ^ n)) = ⟨_, h_lt⟩ := fun h => by
      ext
      simp only [OpTrace.foldlOp_eval]
    rw [h_cand]
  · rfl

@[simp]
theorem verrou3RealProg_steps {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i))) :
    (verrou3RealProg primes F localRoots).steps = inputSizeSATPlus 2 n F + n + 1 := by
  unfold verrou3RealProg
  simp only [OpTrace.steps, OpTrace.foldlOp_eval,
    OpTrace.foldlOp_steps, List.length_ofFn, Nat.mul_one]
  split
  · rename_i h_lt
    dsimp [OpTrace.steps, evalSATPlusOp]
    rw [OpTrace.loop_steps, Nat.mul_one]
    omega
  · dsimp [OpTrace.steps]
    omega

def recombineCRTOp {n : ℕ} (primes : Fin n → ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (primes i))) :
    CostM' (Option (Fin (2 ^ n)))
      (fun r => r = recombineCRTEffective primes F localRoots)
      (inputSizeSATPlus 2 n F + n + 1) :=
  let prog := verrou3RealProg primes F localRoots
  { prog := prog
    run := prog.toCostM
    h_link := rfl
    h_spec := by
      rw [OpTrace.toCostM_val, verrou3RealProg_eval]
    h_cost := by
      rw [OpTrace.toCostM_cost, verrou3RealProg_steps] }


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
      contradiction
  · contradiction

lemma garnerCRTCandidate_eq_some_of_reconstruct_eq {n : ℕ}
    (primes : Fin n → ℕ)
    (localRoots : (i : Fin n) → List (ZMod (primes i)))
    (k : Fin (2 ^ n))
    (h_rec : garnerCRTReconstructNat primes localRoots = k.val) :
    garnerCRTCandidate primes localRoots = some k := by
  unfold garnerCRTCandidate
  dsimp only
  have h_lt : garnerCRTReconstructNat primes localRoots < 2 ^ n := by
    rw [h_rec]
    exact k.isLt
  rw [dite_eq_left h_lt]
  congr 1
  ext
  exact h_rec

lemma canonicalPrimes_prime (n : ℕ) (i : Fin n) :
    Nat.Prime (canonicalPrimes n i) := by
  unfold canonicalPrimes
  exact Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime i.val

lemma canonicalPrimes_strictMono (n : ℕ) :
    StrictMono (canonicalPrimes n) := by
  intro i j hij
  unfold canonicalPrimes
  exact Nat.nth_strictMono Nat.infinite_setOfPred_prime hij

lemma canonicalPrimes_pairwise_coprime
  (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    Nat.Coprime (canonicalPrimes n i) (canonicalPrimes n j) := by
  rw [Nat.coprime_primes (canonicalPrimes_prime n i)
    (canonicalPrimes_prime n j)]
  exact (canonicalPrimes_strictMono n).injective.ne hij

lemma canonicalPrimes_coprime (n : ℕ) {i j : Fin n} (hij : i ≠ j) :
    Nat.Coprime (canonicalPrimes n i) (canonicalPrimes n j) := by
  refine (Nat.coprime_primes (canonicalPrimes_prime n i) (canonicalPrimes_prime n j)).mpr ?_
  intro h_eq
  apply hij
  exact Fin.ext (Nat.nth_injective Nat.infinite_setOfPred_prime h_eq)

lemma two_pow_le_prod_canonicalPrimes (n : ℕ) :
    2 ^ n ≤ ∏ i : Fin n, canonicalPrimes n i := by
  have h2 : (2 : ℕ) ^ n = ∏ _i : Fin n, 2 := by
    simp
  rw [h2]
  exact Finset.prod_le_prod
    (fun i _ => (canonicalPrimes_prime n i).two_le)

lemma crtStep_natCast (m₁ m₂ : ℕ) (h : Nat.Coprime m₁ m₂) (k : ℕ) :
    crtStep m₁ m₂ h (k : ZMod m₁) (k : ZMod m₂) = (k : ZMod (m₁ * m₂)) := by
  unfold crtStep
  have h_prod : ((k : ZMod m₁), (k : ZMod m₂)) = (k : ZMod m₁ × ZMod m₂) := by
    ext <;> simp
  rw [h_prod]
  exact map_natCast (ZMod.chineseRemainder h).symm k

lemma crtCombinePair_mod (M p k : ℕ) (hM : 0 < M) (hp : 0 < p) (hcop : Nat.Coprime M p) :
    crtCombinePair M p (k % M) (k : ZMod p) = (k % (M * p), M * p) := by
  unfold crtCombinePair
  rw [dite_eq_left hcop]
  have hmod : ((k % M : ℕ) : ZMod M) = (k : ZMod M) := ZMod.natCast_mod k M
  rw [hmod, crtStep_natCast M p hcop k]
  have _ : NeZero (M * p) := ⟨Nat.mul_ne_zero (Nat.ne_of_gt hM) (Nat.ne_of_gt hp)⟩
  dsimp only
  rw [ZMod.val_natCast]


lemma foldl_crtCombinePair_eq {n : ℕ}
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i)))
    (k : ℕ)
    (h_head : ∀ i : Fin n,
      headResidue (canonicalPrimes n) localRoots i = (k : ZMod (canonicalPrimes n i))) :
    ∀ (L : List (Fin n)) (M : ℕ),
      0 < M →
      L.Nodup →
      (∀ i ∈ L, Nat.Coprime M (canonicalPrimes n i)) →
      L.foldl
        (fun (st : ℕ × ℕ) (i : Fin n) =>
          crtCombinePair st.2 (canonicalPrimes n i) st.1
            (headResidue (canonicalPrimes n) localRoots i))
        (k % M, M) =
      (k % (M * (L.map (canonicalPrimes n)).prod), M * (L.map (canonicalPrimes n)).prod)
  | [], M, _, _, _ => by
    simp
  | i :: rest, M, hM, hnodup, hcop => by
    rw [List.nodup_cons] at hnodup
    obtain ⟨hi_not_mem, hnodup_rest⟩ := hnodup
    have hcop_i : Nat.Coprime M (canonicalPrimes n i) := hcop i (by simp)
    have hp_pos : 0 < canonicalPrimes n i := (canonicalPrimes_prime n i).pos
    simp only [List.foldl_cons, List.map_cons, List.prod_cons]
    rw [h_head i, crtCombinePair_mod M (canonicalPrimes n i) k hM hp_pos hcop_i]
    have hM' : 0 < M * canonicalPrimes n i := Nat.mul_pos hM hp_pos
    have hcop_rest : ∀ j ∈ rest, Nat.Coprime (M * canonicalPrimes n i) (canonicalPrimes n j) := by
      intro j hj
      have hcop_Mj : Nat.Coprime M (canonicalPrimes n j) := hcop j (by simp [hj])
      have hij : i ≠ j := fun h => hi_not_mem (h ▸ hj)
      exact Nat.Coprime.mul_left hcop_Mj (canonicalPrimes_coprime n hij)
    rw [foldl_crtCombinePair_eq localRoots k h_head rest
      (M * canonicalPrimes n i) hM' hnodup_rest hcop_rest]
    rw [mul_assoc]


lemma garnerCRTReconstructNat_eq_witness
    (n : ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i)))
    (k : Fin (2 ^ n))
    (_ : evalSATPlus 2 n F k = true)
    (h_head : ∀ i : Fin n,
      headResidue (canonicalPrimes n) localRoots i = ((k : ℕ) : ZMod (canonicalPrimes n i))) :
    garnerCRTReconstructNat (canonicalPrimes n) localRoots = k.val := by
  unfold garnerCRTReconstructNat
  dsimp only
  have hinit : (0, 1) = (k.val % 1, 1) := by
    rw [Nat.mod_one]
  rw [hinit]
  have hnodup : (List.ofFn (fun i : Fin n => i)).Nodup :=
    List.nodup_ofFn.mpr Function.injective_id
  have hcop1 : ∀ i ∈ List.ofFn (fun i : Fin n => i), Nat.Coprime 1 (canonicalPrimes n i) :=
    fun i _ => Nat.coprime_one_left _
  rw [foldl_crtCombinePair_eq localRoots k.val h_head
        (List.ofFn (fun i : Fin n => i)) 1 Nat.one_pos hnodup hcop1]
  simp only [one_mul]
  have hprod : ((List.ofFn (fun i : Fin n => i)).map (canonicalPrimes n)).prod =
      ∏ i : Fin n, canonicalPrimes n i := by
    rw [List.map_ofFn]
    exact List.prod_ofFn
  rw [hprod]
  have hlt : k.val < ∏ i : Fin n, canonicalPrimes n i :=
    lt_of_lt_of_le k.isLt (two_pow_le_prod_canonicalPrimes n)
  exact Nat.mod_eq_of_lt hlt


theorem garnerCRTCandidate_completeness (n : ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i)))
    (h_sat : ∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true ∧
      ∀ i : Fin n, ((k : ℕ) : ZMod (canonicalPrimes n i)) ∈ localRoots i) :
    ∃ k_crt : Fin (2 ^ n),
      garnerCRTCandidate (canonicalPrimes n) localRoots = some k_crt ∧
      evalSATPlus 2 n F k_crt = true := by
  rcases h_sat with ⟨k, hk_sat, hk_mem⟩
  refine ⟨k, ?_, hk_sat⟩
  apply garnerCRTCandidate_eq_some_of_reconstruct_eq
  sorry
  -- exact garnerCRTReconstructNat_eq_witness n F localRoots k hk_sat hk_mem
-- ya un soucis avec l'un des arguments sur la fin, à corriger après



theorem recombineCRTEffective_completeness (n : ℕ) (F : InstanceSATPlus 2)
    (localRoots : (i : Fin n) → List (ZMod (canonicalPrimes n i)))
    (h_sat : ∃ k : Fin (2 ^ n), evalSATPlus 2 n F k = true ∧
      ∀ i : Fin n, ((k : ℕ) : ZMod (canonicalPrimes n i)) ∈ localRoots i) :
    ∃ k_out : Fin (2 ^ n),
      recombineCRTEffective (canonicalPrimes n) F localRoots = some k_out := by
  rcases garnerCRTCandidate_completeness n F localRoots h_sat with ⟨k_crt, h_garner, h_eval⟩
  refine ⟨k_crt, ?_⟩
  unfold recombineCRTEffective
  simp [h_garner, h_eval]


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
    intro n F localRoots h_sat
    have hval := (recombineCRTOp (canonicalPrimes n) F localRoots).h_spec
    rw [hval]
    exact recombineCRTEffective_completeness n F localRoots h_sat


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





def verrou3OpTrace (n : ℕ) (F : InstanceSATPlus 2) (res : Option (Fin (2 ^ n))) :
    OpTrace (Option (Fin (2 ^ n))) :=
  OpTrace.prim (n + inputSizeSATPlus 2 n F + 1) res

@[simp]
theorem verrou3OpTrace_steps (n : ℕ) (F : InstanceSATPlus 2) (res : Option (Fin (2 ^ n))) :
    (verrou3OpTrace n F res).steps = inputSizeSATPlus 2 n F + n + 1 := by
  unfold verrou3OpTrace
  dsimp [OpTrace.steps]
  omega






def effectiveVerrou1 : Verrou1_PolyTimeTrace where
  computeTrace := fun n p m F => (computeTraceOp n F p m).toCostM
  prog := fun n p m F => (computeTraceOp n F p m).prog
  h_link := fun n p m F => (computeTraceOp n F p m).h_link
  poly_bound := polyXPlusOne
  cost_le_poly := by
    intro n p m F
    rw [polyXPlusOne_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    exact (computeTraceOp n F p m).h_cost
  spec := by
    intro n p m F
    exact (computeTraceOp n F p m).h_spec

def effectiveVerrou2 : Verrou2_PolyTimeLocalRoots where
  degreeBound := fun n F => inputSizeSATPlus 2 n F
  extractLocalRoots := fun n p F oracle =>
    (extractRootsOp p (inputSizeSATPlus 2 n F) (fun m => (oracle m).val)).run
  poly_bound := polyVerrou2
  cost_le_poly := by
    intro n p F oracle
    rw [polyVerrou2_eq]
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    have hcost := (extractRootsOp p (inputSizeSATPlus 2 n F) (fun m => (oracle m).val)).h_cost
    set S := inputSizeSATPlus 2 n F
    nlinarith
  spec := by
    intro n p hp F h_card h_lt oracle h_oracle hsat
    have _ : Fact (Nat.Prime p) := ⟨hp⟩
    rcases hsat with ⟨k, hk⟩
    refine ⟨k, hk, ?_⟩
    have hval := (extractRootsOp p (inputSizeSATPlus 2 n F) (fun m => (oracle m).val)).h_spec
    rw [hval]
    unfold extractLocalRootsEffective
    rw [mem_directNewtonRootsFp_iff]
    exact newtonGirard_horner_annihilates_solution n p hp F h_card h_lt
      (fun m => (oracle m).val) h_oracle k hk




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
      (fun L => L = extractLocalRootsEffective p p (fun m => computeTraceEffective 2 n p F m))
      ((p + 1) * (p + 1) + p * (p + 1)) :=
  extractRootsOp p p (fun m => computeTraceEffective 2 n p F m)

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
