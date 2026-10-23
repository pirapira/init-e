import InitE.SourceSemantics
import InitE.SourceDeclarationsCore
import Guest.Ast
import Guest.GasLimit
import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
import Flapjack.Pancake.Semantics.PanProps.EvalInvariant


set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

/-!
# `InitECandidate.Solver.GuestStepBound` — Verrou B: Source `PanSem` Clock Calculus & `Guest.guestAst` Structural Bounds

This module establishes the source-level (`PanSem`) clock calculus and static
structural bounds on `Guest.guestAst` required for finite step-bound certificates:

1. **Clock Irrelevance of `PanSem` & `PanValue` Expression Evaluation**:
   Evaluating a single expression (`panSem_evalExp_clock_irrel`), an expression
   list (`panSem_evalExps_clock_irrel`), or struct field expressions
   (`panSem_evalFields_clock_irrel`) in `PanSemStateFiniteExact` is completely
   independent of the state clock `s.clock`.
2. **Exact Clock Preservation & Decrement of `PanSem` Statements**:
   - All 11 leaf statements (`.skip`, `.annot`, `.assign`, `.store`, `.storeByte`,
     `.store32`, `.return`, `.raise`, `.break`, `.continue`, `.primitive`) preserve
     `s.clock` exactly (`(evaluateHOLFiniteState s prog).2.clock = s.clock`).
   - Any `.tick` or `.while c b` step with true guard (`evalHOLFinite s c = some (.val (.word w))`,
     `w ≠ 0`) at `s.clock = 0` produces `(some .timeOut, emptyLocalsHOLFinite s)`.
   - Consequently, any non-`.timeOut` execution of `.while c b` with a true guard
     requires `1 ≤ s.clock` and decreases `clock` by at least `1` (`post.clock ≤ s.clock - 1`).
3. **Kernel-Checked Structural & Frame Bounds on `Guest.guestAst` (`Verrou B`)**:
   - Total, non-`partial`, kernel-checked port of `Guest.FrameBound` proving
     `guestMaxFrameBound = 348` (`0` reduction axioms, no `native_decide`),
     `Guest.guestAst.length = 928`, `(frameBounds Guest.guestAst).length = 825`,
     and connecting `Guest.GasLimit.declaredGasLimit input ≤ 200000000` to
     `Guest.InputDecode.decodeStatelessInput`.
-/

namespace Flapjack.PanSemStateFiniteExact

open Flapjack.Pancake.PanLang (MlS ExpHOL)

/-- Alias for exact finite-support single-expression evaluation (`evalHOLFinite`). -/
abbrev evalExpHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    ExpHOL width → Option (ValueHOL width) :=
  @evalHOLFinite width σ _ state h

/-- Alias for exact finite-support expression-list evaluation (`evalListHOLFinite`). -/
abbrev evalExpsHOL {width : Nat} {σ : Type} [NeZero width]
    (state : PanSemStateFiniteExact width σ) [h : DecidablePred state.memaddrs] :
    List (ExpHOL width) → Option (List (ValueHOL width)) :=
  @evalListHOLFinite width σ _ state h

end Flapjack.PanSemStateFiniteExact

namespace InitECandidate.Solver.GuestStepBound

open Flapjack
open Flapjack.Pancake.PanLang

/-! ## 1. Clock Irrelevance of `PanSem` & `PanValue` Expressions -/

/-- Evaluating a Pancake expression `e : ExpHOL width` in `PanSemStateFiniteExact`
is independent of `s.clock`: expressions never inspect or consume clock ticks.
Proved by mutual structural induction on `ExpHOL width`. -/
theorem panSem_evalExp_clock_irrel {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) [h : DecidablePred s.memaddrs]
    (k : Nat) (e : ExpHOL width) :
    @PanSemStateFiniteExact.evalExpHOL width σ _ { s with clock := k } h e =
      @PanSemStateFiniteExact.evalExpHOL width σ _ s h e := by
  simp only [PanSemStateFiniteExact.evalExpHOL, PanSemStateFiniteExact.evalHOLFinite]
  exact @evalHOLExact_upd_clock_eq width σ _ s.toExact h e k

/-- Evaluating a list of Pancake expressions `es : List (ExpHOL width)` in
`PanSemStateFiniteExact` is independent of `s.clock`. -/
theorem panSem_evalExps_clock_irrel {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) [h : DecidablePred s.memaddrs]
    (k : Nat) (es : List (ExpHOL width)) :
    @PanSemStateFiniteExact.evalExpsHOL width σ _ { s with clock := k } h es =
      @PanSemStateFiniteExact.evalExpsHOL width σ _ s h es := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
      simp only [PanSemStateFiniteExact.evalExpsHOL, PanSemStateFiniteExact.evalListHOLFinite,
        evalListHOLExact]
      have he : @evalHOLExact width σ _ ({ s with clock := k }).toExact h e =
          @evalHOLExact width σ _ s.toExact h e :=
        @evalHOLExact_upd_clock_eq width σ _ s.toExact h e k
      have hrest : @evalListHOLExact width σ _ ({ s with clock := k }).toExact h rest =
          @evalListHOLExact width σ _ s.toExact h rest := ih
      rw [he, hrest]

/-- Evaluating named-struct field expressions `fs : List (MlS × ExpHOL width)` in
`PanSemStateFiniteExact` is independent of `s.clock`. -/
theorem panSem_evalFields_clock_irrel {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) [h : DecidablePred s.memaddrs]
    (k : Nat) (fs : List (MlS × ExpHOL width)) :
    @PanSemStateFiniteExact.evalListFieldsHOLFinite width σ _ { s with clock := k } h fs =
      @PanSemStateFiniteExact.evalListFieldsHOLFinite width σ _ s h fs := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
      obtain ⟨fname, e⟩ := f
      simp only [PanSemStateFiniteExact.evalListFieldsHOLFinite, evalListFieldsHOLExact]
      have he : @evalHOLExact width σ _ ({ s with clock := k }).toExact h e =
          @evalHOLExact width σ _ s.toExact h e :=
        @evalHOLExact_upd_clock_eq width σ _ s.toExact h e k
      have hrest : @evalListFieldsHOLExact width σ _ ({ s with clock := k }).toExact h rest =
          @evalListFieldsHOLExact width σ _ s.toExact h rest := ih
      rw [he, hrest]

/-- Monadic list evaluation `es.mapM (evalExpHOL ...)` is independent of `s.clock`. -/
theorem panSem_optMmap_evalExp_clock_irrel {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) [h : DecidablePred s.memaddrs]
    (k : Nat) (es : List (ExpHOL width)) :
    es.mapM (fun e => @PanSemStateFiniteExact.evalExpHOL width σ _ { s with clock := k } h e) =
      es.mapM (fun e => @PanSemStateFiniteExact.evalExpHOL width σ _ s h e) := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
      simp only [List.mapM_cons, panSem_evalExp_clock_irrel s k e, ih]

/-! ## 2. Exact Clock Preservation of `PanSem` Leaf Instructions -/

@[simp] theorem setVarHOLFinite_clock {width : Nat} [NeZero width] {σ : Type}
    (name : MlS) (value : ValueHOL width) (s : PanSemStateFiniteExact width σ) :
    (PanSemStateFiniteExact.setVarHOLFinite name value s).clock = s.clock := rfl

@[simp] theorem setGlobalHOLFinite_clock {width : Nat} [NeZero width] {σ : Type}
    (name : MlS) (value : ValueHOL width) (s : PanSemStateFiniteExact width σ) :
    (PanSemStateFiniteExact.setGlobalHOLFinite name value s).clock = s.clock := rfl

@[simp] theorem setKvarHOLFinite_clock {width : Nat} [NeZero width] {σ : Type}
    (kind : VarKind) (name : MlS) (value : ValueHOL width)
    (s : PanSemStateFiniteExact width σ) :
    (PanSemStateFiniteExact.setKvarHOLFinite kind name value s).clock = s.clock := by
  cases kind <;> rfl

@[simp] theorem emptyLocalsHOLFinite_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) :
    (PanSemStateFiniteExact.emptyLocalsHOLFinite s).clock = s.clock := rfl

@[simp] theorem decClockHOLFinite_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) :
    (PanSemStateFiniteExact.decClockHOLFinite s).clock = s.clock - 1 := rfl

/-- `.skip` leaves `clock` unchanged. -/
theorem panSem_evaluate_skip_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.skip : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_skip]

/-- `.annot` leaves `clock` unchanged. -/
theorem panSem_evaluate_annot_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (tag text : MlS) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.annot tag text : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_annot]

/-- `.break` leaves `clock` unchanged. -/
theorem panSem_evaluate_break_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.break : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_break]

/-- `.continue` leaves `clock` unchanged. -/
theorem panSem_evaluate_continue_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.continue : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_continue]

/-- `.assign` leaves `clock` unchanged in both success and error branches. -/
theorem panSem_evaluate_assign_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (kind : VarKind) (name : MlS) (e : ExpHOL width) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.assign kind name e : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_assign]
  split
  · rfl
  · split <;> simp [setKvarHOLFinite_clock]

/-- `.store` leaves `clock` unchanged in all branches. -/
theorem panSem_evaluate_store_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (dst src : ExpHOL width) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.store dst src : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_store]
  cases @evalHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) dst with
  | none => rfl
  | some dv =>
      cases dv with
      | rStruct _ | nStruct _ _ => rfl
      | val dp =>
          cases dp with
          | word address =>
              dsimp only
              cases @evalHOLExact width σ _ s.toExact
                  (fun address => Classical.propDecidable (s.memaddrs address)) src with
              | none => rfl
              | some value =>
                  dsimp only
                  cases @panMemStoresHOL width _ address (flattenHOL value) s.memaddrs
                      (fun address => Classical.propDecidable (s.memaddrs address)) s.memory <;> rfl

/-- `.storeByte` leaves `clock` unchanged in all branches. -/
theorem panSem_evaluate_storeByte_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (dst src : ExpHOL width) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.storeByte dst src : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_storeByte]
  cases @evalHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) dst with
  | none => rfl
  | some dv =>
      cases dv with
      | rStruct _ | nStruct _ _ => rfl
      | val dp =>
          cases dp with
          | word address =>
              dsimp only
              cases @evalHOLExact width σ _ s.toExact
                  (fun address => Classical.propDecidable (s.memaddrs address)) src with
              | none => rfl
              | some sv =>
                  cases sv with
                  | rStruct _ | nStruct _ _ => rfl
                  | val sp =>
                      cases sp with
                      | word value =>
                          dsimp only
                          cases @panMemStoreByteWord8HOL width _ s.memory s.memaddrs
                              (fun address => Classical.propDecidable (s.memaddrs address))
                              s.be address (BitVec.ofNat 8 value.toNat) <;> rfl

/-- `.store32` leaves `clock` unchanged in all branches. -/
theorem panSem_evaluate_store32_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (dst src : ExpHOL width) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.store32 dst src : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_store32]
  cases @evalHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) dst with
  | none => rfl
  | some dv =>
      cases dv with
      | rStruct _ | nStruct _ _ => rfl
      | val dp =>
          cases dp with
          | word address =>
              dsimp only
              cases @evalHOLExact width σ _ s.toExact
                  (fun address => Classical.propDecidable (s.memaddrs address)) src with
              | none => rfl
              | some sv =>
                  cases sv with
                  | rStruct _ | nStruct _ _ => rfl
                  | val sp =>
                      cases sp with
                      | word value =>
                          dsimp only
                          cases @panMemStore32HOL width _ s.memory s.memaddrs
                              (fun address => Classical.propDecidable (s.memaddrs address))
                              s.be address (BitVec.ofNat 32 value.toNat) <;> rfl

/-- `.return` leaves `clock` unchanged in all branches. -/
theorem panSem_evaluate_return_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (e : ExpHOL width) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.return e : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_return]
  split
  · rfl
  · split <;> rfl

/-- `.raise` leaves `clock` unchanged in all branches. -/
theorem panSem_evaluate_raise_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (eid : MlS) (e : ExpHOL width) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.raise eid e : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_raise]
  cases s.eshapes.lookup eid with
  | none => rfl
  | some shape =>
      dsimp only
      cases @evalHOLExact width σ _ s.toExact
          (fun address => Classical.propDecidable (s.memaddrs address)) e with
      | none => rfl
      | some value =>
          dsimp only
          by_cases hcond : shapeOfHOLExact value = shape ∧
              Flapjack.Pancake.PanLang.sizeOfShapeWithContextHOL s.structs
                (shapeOfHOLExact value) ≤ 32
          · rw [if_pos hcond]; rfl
          · rw [if_neg hcond]

/-- `.primitive` leaves `clock` unchanged in all branches. -/
theorem panSem_evaluate_primitive_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (name : MlS) (op : PrimOp) (args : List (ExpHOL width)) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s (.primitive name op args : ProgHOL width)).2.clock = s.clock := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_primitive]
  cases @evalListHOLExact width σ _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) args with
  | none => rfl
  | some values =>
      dsimp only
      cases panPrimopHOLExact op values with
      | none => rfl
      | some value =>
          dsimp only
          by_cases hvalid : s.isValidValueHOLFinite VarKind.local name value = true
          · rw [if_pos hvalid]; rfl
          · rw [if_neg hvalid]

/-- Syntactic classifier for the non-ticking leaf instructions of `ProgHOL width`. -/
def isClockPreservingLeaf {width : Nat} [NeZero width] : ProgHOL width → Bool
  | .skip | .annot _ _ | .assign _ _ _ | .store _ _ | .storeByte _ _ | .store32 _ _
  | .return _ | .raise _ _ | .break | .continue | .primitive _ _ _ => true
  | _ => false

/-- Unified leaf clock-preservation theorem: every `ProgHOL width` satisfying
`isClockPreservingLeaf prog = true` leaves `s.clock` unchanged. -/
theorem panSem_evaluate_leaf_clock_eq {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (prog : ProgHOL width)
    (hleaf : isClockPreservingLeaf prog = true) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState s prog).2.clock = s.clock := by
  cases prog with
  | skip => exact panSem_evaluate_skip_clock s
  | annot tag text => exact panSem_evaluate_annot_clock s tag text
  | assign kind name e => exact panSem_evaluate_assign_clock s kind name e
  | store dst src => exact panSem_evaluate_store_clock s dst src
  | storeByte dst src => exact panSem_evaluate_storeByte_clock s dst src
  | store32 dst src => exact panSem_evaluate_store32_clock s dst src
  | «return» e => exact panSem_evaluate_return_clock s e
  | raise eid e => exact panSem_evaluate_raise_clock s eid e
  | «break» => exact panSem_evaluate_break_clock s
  | «continue» => exact panSem_evaluate_continue_clock s
  | primitive name op args => exact panSem_evaluate_primitive_clock s name op args
  | _ => simp [isClockPreservingLeaf] at hleaf

/-! ## 3. Clock Decrement of `.tick`, `.while`, `.call`, and `.decCall` -/

/-- Evaluating `.tick` at `s.clock = 0` immediately produces `some .timeOut`. -/
theorem panSem_evaluate_tick_clock_zero {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (h0 : s.clock = 0) :
    PanSemStateFiniteExact.evaluateHOLFiniteState s (.tick : ProgHOL width) =
      (some .timeOut, PanSemStateFiniteExact.emptyLocalsHOLFinite s) := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_tick, if_pos h0]

/-- Any non-`.timeOut` evaluation of `.tick` requires `1 ≤ s.clock` and decrements `clock` by `1`. -/
theorem panSem_evaluate_tick_not_timeOut {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ)
    (hnt : (PanSemStateFiniteExact.evaluateHOLFiniteState s (.tick : ProgHOL width)).1 ≠ some .timeOut) :
    1 ≤ s.clock ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState s (.tick : ProgHOL width)).2.clock = s.clock - 1 := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_tick] at hnt ⊢
  by_cases h0 : s.clock = 0
  · rw [if_pos h0] at hnt
    exact absurd rfl hnt
  · rw [if_neg h0]
    exact ⟨Nat.pos_of_ne_zero h0, rfl⟩

/-- Evaluating `.while c b` when the guard `c` evaluates to `0` (`false`)
terminates immediately with `(none, s)` and consumes `0` clock ticks. -/
theorem panSem_evaluate_while_false_clock_eq {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (c : ExpHOL width) (b : ProgHOL width)
    (hguard : @PanSemStateFiniteExact.evalHOLFinite width σ _ s
      (fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word 0))) :
    PanSemStateFiniteExact.evaluateHOLFiniteState s (.while c b) = (none, s) ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState s (.while c b)).2.clock = s.clock := by
  have hw : PanSemStateFiniteExact.evaluateHOLFiniteState s (.while c b) = (none, s) := by
    rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_total, hguard]
    dsimp only
    rw [if_neg (by intro h; exact h rfl)]
  exact ⟨hw, by rw [hw]⟩

/-- Evaluating `.while c b` at `s.clock = 0` when the guard `c` evaluates to a
non-zero word `w ≠ 0` immediately produces `(some .timeOut, emptyLocalsHOLFinite s)`. -/
theorem panSem_evaluate_while_true_clock_zero {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (c : ExpHOL width) (b : ProgHOL width)
    (w : BitVec width)
    (hguard : @PanSemStateFiniteExact.evalHOLFinite width σ _ s
      (fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word w)))
    (htrue : w ≠ 0) (h0 : s.clock = 0) :
    PanSemStateFiniteExact.evaluateHOLFiniteState s (.while c b) =
      (some .timeOut, PanSemStateFiniteExact.emptyLocalsHOLFinite s) := by
  rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_total, hguard]
  dsimp only
  rw [if_pos htrue, if_pos h0]

/-- Any non-`.timeOut` execution of `.while c b` whose guard `c` is true (`w ≠ 0`)
requires `1 ≤ s.clock` and consumes at least `1` clock tick (`post.clock ≤ s.clock - 1`). -/
theorem panSem_evaluate_while_true_not_timeOut_clock_dec {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (c : ExpHOL width) (b : ProgHOL width)
    (w : BitVec width)
    (hguard : @PanSemStateFiniteExact.evalHOLFinite width σ _ s
      (fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word w)))
    (htrue : w ≠ 0)
    (hnt : (PanSemStateFiniteExact.evaluateHOLFiniteState s (.while c b)).1 ≠ some .timeOut) :
    1 ≤ s.clock ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState s (.while c b)).2.clock ≤ s.clock - 1 := by
  by_cases h0 : s.clock = 0
  · rw [panSem_evaluate_while_true_clock_zero s c b w hguard htrue h0] at hnt
    exact absurd rfl hnt
  · refine ⟨Nat.pos_of_ne_zero h0, ?_⟩
    rw [PanSemStateFiniteExact.evaluateHOLFiniteState_while_total, hguard]
    dsimp only
    rw [if_pos htrue, if_neg h0]
    let entry := PanSemStateFiniteExact.decClockHOLFinite s
    let bodyOutput := PanSemStateFiniteExact.evaluateHOLFiniteState entry b
    let fixed := PanSemStateFiniteExact.fixClockHOLFinite entry bodyOutput
    have hfixed_le : fixed.2.clock ≤ s.clock - 1 :=
      PanSemStateFiniteExact.fixClockHOLFinite_clock_le entry bodyOutput
    have hrec_le : (PanSemStateFiniteExact.evaluateHOLFiniteState fixed.2 (.while c b)).2.clock ≤
        s.clock - 1 :=
      Nat.le_trans
        (evaluateHOLFiniteState_clock_le fixed.2 (.while c b))
        hfixed_le
    cases hbo : bodyOutput.1 with
    | none => exact hrec_le
    | some r =>
        cases r <;> first | exact hrec_le | exact hfixed_le

/-- Evaluating `.decCall` at `s.clock = 0` when argument evaluation and code lookup succeed
produces `(some .timeOut, emptyLocalsHOLFinite s)`. -/
theorem panSem_evaluate_decCall_clock_zero {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ)
    (rt : MlS) (sh : ShapeHOL) (fname : MlS) (args : List (ExpHOL width)) (cont : ProgHOL width)
    (values : List (ValueHOL width)) (body : ProgHOL width)
    (callee : HolFiniteMapExact MlS (ValueHOL width)) (retShape : ShapeHOL)
    (hargs : @PanSemStateFiniteExact.evalListHOLFinite width σ _ s
      (fun a => Classical.propDecidable (s.memaddrs a)) args = some values)
    (hlookup : PanSemStateFiniteExact.lookupCodeHOLFinite s.code.lookup fname values =
      some (body, callee, retShape))
    (h0 : s.clock = 0) :
    PanSemStateFiniteExact.evaluateHOLFiniteState s (.decCall rt sh fname args cont) =
      (some .timeOut, PanSemStateFiniteExact.emptyLocalsHOLFinite s) :=
  PanSemStateFiniteExact.evaluateHOLFiniteState_decCall_clock_zero
    s rt sh fname args cont values body callee retShape hargs hlookup h0

/-! ## 4. Total, Kernel-Checked Port of `Guest.FrameBound` & `Guest.guestAst` Bounds (`Verrou B`) -/

/-- Word size of a shape (`Shape.shapeSize`). -/
def words : Shape → Nat := Shape.shapeSize

mutual
  /-- Total, structurally recursive count of expression nodes in `Exp α`. -/
  def expNodes {α : Type} : Exp α → Nat
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => 1
    | .rStruct fields => 1 + expNodesList fields
    | .rField _ e | .nField _ e | .load _ e | .load32 e | .loadByte e => 1 + expNodes e
    | .nStruct _ fields => 1 + expNodesFieldList fields
    | .op _ args | .panOp _ args => 1 + expNodesList args
    | .cmp _ l r | .shift _ l r => 1 + expNodes l + expNodes r

  /-- Total sum of `expNodes` over a list of expressions. -/
  def expNodesList {α : Type} : List (Exp α) → Nat
    | [] => 0
    | e :: es => expNodes e + expNodesList es

  /-- Total sum of `expNodes` over a list of named struct fields. -/
  def expNodesFieldList {α : Type} : List (FieldName × Exp α) → Nat
    | [] => 0
    | (_, e) :: fs => expNodes e + expNodesFieldList fs
end

/-- `expNodesList` agrees with `(es.map expNodes).sum`. -/
theorem expNodesList_eq_map_sum {α : Type} (es : List (Exp α)) :
    expNodesList es = (es.map expNodes).sum := by
  induction es with
  | nil => rfl
  | cons e rest ih => simp [expNodesList, ih]

/-- `expNodesFieldList` agrees with `(fs.map (fun f => expNodes f.2)).sum`. -/
theorem expNodesFieldList_eq_map_sum {α : Type} (fs : List (FieldName × Exp α)) :
    expNodesFieldList fs = (fs.map (fun f => expNodes f.2)).sum := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
      obtain ⟨_, e⟩ := f
      simp [expNodesFieldList, ih]

/-- Expression nodes evaluated by one statement (not descending into nested statements),
giving an upper bound on the `crep_to_loop` temporaries live at once. -/
def stmtExpNodes {α : Type} : Prog α → Nat
  | .dec _ _ v _ | .assign _ _ v | .raise _ v | .return v => expNodes v
  | .primitive _ _ args | .call _ _ args | .decCall _ _ _ args _ => expNodesList args
  | .store a v | .store32 a v | .storeByte a v | .shMemStore _ a v => expNodes a + expNodes v
  | .ite c _ _ | .while c _ => expNodes c
  | .extCall _ a b c d => expNodes a + expNodes b + expNodes c + expNodes d
  | .shMemLoad _ _ _ a => expNodes a
  | _ => 0

/-- Total count of words of every variable declared in a statement body
(each `var`, `var = f()`, and exception handler variable). -/
def declaredWords {α : Type} : Prog α → Nat
  | .dec _ shape _ body => words shape + declaredWords body
  | .decCall _ shape _ _ body => words shape + declaredWords body
  | .seq a b => declaredWords a + declaredWords b
  | .ite _ a b => declaredWords a + declaredWords b
  | .while _ b => declaredWords b
  | .call (some (_, some (_, _, handler))) _ _ => 1 + declaredWords handler
  | _ => 0
termination_by p => sizeOf p
decreasing_by
  all_goals
    simp_wf
    try omega

/-- Total maximum temporary expression nodes across all statements in a program. -/
def maxTemps {α : Type} : Prog α → Nat
  | .seq a b => max (maxTemps a) (maxTemps b)
  | .ite c a b => max (expNodes c) (max (maxTemps a) (maxTemps b))
  | .while c b => max (expNodes c) (maxTemps b)
  | .dec _ _ v b => max (expNodes v) (maxTemps b)
  | .decCall _ _ _ args b => max (expNodesList args) (maxTemps b)
  | .call (some (_, some (_, _, handler))) _ args =>
      max (expNodesList args) (maxTemps handler)
  | .call _ _ args => expNodesList args
  | s => stmtExpNodes s
termination_by p => sizeOf p
decreasing_by
  all_goals
    simp_wf
    try omega

/-- Total sum of parameter words for a function declaration. -/
def paramWords (params : List (VarName × Shape)) : Nat :=
  match params with
  | [] => 0
  | (_, s) :: rest => words s + paramWords rest

/-- `paramWords` agrees with `(params.map (fun p => words p.2)).sum`. -/
theorem paramWords_eq_map_sum (params : List (VarName × Shape)) :
    paramWords params = (params.map (fun p => words p.2)).sum := by
  induction params with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨_, s⟩ := p
      simp [paramWords, ih]

/-- Source-level stack frame upper bound of a function declaration (in words). -/
def frameBound {α : Type} (f : FunDecl α) : Nat :=
  paramWords f.params + declaredWords f.body + maxTemps f.body + 1

/-- Frame bound of every function declaration in a Pancake program. -/
def frameBounds {α : Type} (program : List (Decl α)) : List (FunName × Nat) :=
  program.filterMap fun
    | .function f => some (f.name, frameBound f)
    | _ => none

/-- `F`: the largest frame bound over all functions in `Guest.guestAst`. -/
def guestMaxFrameBound : Nat :=
  (frameBounds Guest.guestAst).foldl (fun acc entry => max acc entry.2) 0

/-- Kernel-checked certificate (`0` reduction axioms) that the maximum stack frame
bound across all functions in `Guest.guestAst` is `348` words. -/
theorem guestMaxFrameBound_eq : guestMaxFrameBound = 348 := by
  decide_cbv

/-- Total number of declarations in `Guest.guestAst` is `928`. -/
theorem guestAst_length_eq : Guest.guestAst.length = 928 := by
  decide_cbv

/-- Total number of function declarations in `Guest.guestAst` is `825`. -/
theorem guestAst_functions_length_eq : (frameBounds Guest.guestAst).length = 825 := by
  decide_cbv

/-- Every function in `Guest.guestAst` has frame bound at most `348` words. -/
theorem guestAst_frameBound_le :
    ∀ entry ∈ frameBounds Guest.guestAst, entry.2 ≤ 348 := by
  have hall : (frameBounds Guest.guestAst).all (fun entry => decide (entry.2 ≤ 348)) = true := by
    decide_cbv
  intro entry hentry
  exact of_decide_eq_true (List.all_eq_true.mp hall entry hentry)

/-! ## 5. Connection Between `Guest.GasLimit.declaredGasLimit` and `Guest.InputDecode` -/

/-- Whenever `Guest.InputDecode.decodeStatelessInput` accepts `input` and the challenge
precondition `Guest.GasLimit.declaredGasLimit input ≤ 200000000` holds, the decoded
execution payload's `gasLimit` is equal to `Guest.GasLimit.declaredGasLimit input`
and bounded by `200000000`. -/
theorem declaredGasLimit_le_of_decode {input : Guest.InputBlob}
    {decoded : Guest.InputDecode.StatelessInput}
    (hdecode : Guest.InputDecode.decodeStatelessInput input = some decoded)
    (hbound : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    decoded.payload.gasLimit = Guest.GasLimit.declaredGasLimit input ∧
      decoded.payload.gasLimit ≤ 200000000 := by
  have heq := Guest.GasLimit.declaredGasLimit_of_decode hdecode
  exact ⟨heq, heq ▸ hbound⟩

/-- Under a successful `decodeStatelessInput`, `Guest.InputDecode.declaredGasLimit input`
is `some decoded.payload.gasLimit` and is bounded by `200000000` iff
`Guest.GasLimit.declaredGasLimit input ≤ 200000000`. -/
theorem decoderGasLimit_bound_iff_of_decode {input : Guest.InputBlob}
    {decoded : Guest.InputDecode.StatelessInput}
    (hdecode : Guest.InputDecode.decodeStatelessInput input = some decoded) :
    Guest.InputDecode.declaredGasLimit input = some (Guest.GasLimit.declaredGasLimit input) ∧
      (decoded.payload.gasLimit ≤ 200000000 ↔
        Guest.GasLimit.declaredGasLimit input ≤ 200000000) := by
  refine ⟨Guest.GasLimit.decoderGasLimit_eq_some hdecode, ?_⟩
  rw [Guest.GasLimit.declaredGasLimit_of_decode hdecode]

end InitECandidate.Solver.GuestStepBound
