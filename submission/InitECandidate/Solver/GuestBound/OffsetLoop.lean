import Mathlib.Data.BitVec
import Mathlib.Tactic.Ring
import InitECandidate.Solver.GuestBound.CounterLoop
import InitECandidate.Solver.GuestBound.Calm

/-!
# Offset-guard loops

Loops of the shape `while i + k <=+ n { …; i = i + k }` (`memcpy`, `memzero`,
`memeq`). For `n ≥ 2^64 - k` the guard never becomes false, so there is no
unconditional bound; but if the body can only finish normally or with
`.error`, such a run never returns a result other than `.error`. Every other
run leaves the loop within `2^64` iterations.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The result is `.normal` or `.error`. -/
def _root_.Flapjack.PanValueFfiControlResult.plain {σ : Type} : Result σ → Bool
  | .normal _ _ _ _ | .error _ _ _ _ => true
  | _ => false

/-- Statements that can only finish normally or with `.error`; calls are
allowed to functions satisfying `callee` (meant: calm functions). -/
def straight (callee : FunName → Bool) : Prog Word → Bool
  | .skip | .tick | .annot _ _ | .assign _ _ _ | .store _ _ | .store32 _ _ | .storeByte _ _
  | .primitive _ _ _ => true
  | .seq first second => straight callee first && straight callee second
  | .ite _ thenBranch elseBranch => straight callee thenBranch && straight callee elseBranch
  | .dec _ _ _ body => straight callee body
  | .while _ body => straight callee body
  | .call (some (_, none)) f _ => callee f
  | .decCall _ _ f _ body => callee f && straight callee body
  | _ => false

/-- A call with a destination and no handler, to a calm function, ends normally or in `.error`. -/
theorem callSteps_dest_plain {f : FunName} (hf : FunCalm E f)
    (destination : Option (VarKind × VarName)) (fuel : Nat) (s : St σ)
    (arguments : List (Exp Word)) (r : Result σ) (n : Nat)
    (hrun : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
      E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi
      (some (destination, none)) f arguments (memoryAccess := E.memoryAccess)
      (contracts := E.contracts) (memoryHandler := E.memoryHandler) = some (r, n)) :
    r.plain = true := by
  cases fuel with
  | zero => simp [evalPanValueFfiCallSteps] at hrun
  | succ fuel =>
    rw [evalPanValueFfiCallSteps] at hrun
    cases hargs : panValueCallArguments E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory arguments E.memoryAccess with
    | none =>
      rw [hargs] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      rfl
    | some argumentPair =>
      obtain ⟨values, argumentSteps⟩ := argumentPair
      rw [hargs] at hrun
      simp only [Option.elim_some] at hrun
      cases htarget : panValueCallTarget E.structs E.contracts f E.functions values with
      | none =>
        rw [htarget] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
      | some callTarget =>
        obtain ⟨body, calleeLocals⟩ := callTarget
        rw [htarget] at hrun
        simp only [Option.elim_some] at hrun
        have hbodyCalm : ∀ fuel s r n, E.run fuel s body = some (r, n) → r.isCalm = true := by
          simp only [panValueCallTarget] at htarget
          split at htarget
          · simp at htarget
          · rename_i parameters body' hlookup
            split at htarget
            · split at htarget
              · simp only [Option.some.injEq, Prod.mk.injEq] at htarget
                obtain ⟨rfl, _⟩ := htarget
                exact hf parameters _ hlookup
              · simp at htarget
            · simp at htarget
        cases hbody : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel calleeLocals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [hbody] at hrun; simp at hrun
        | some bodyPair =>
          obtain ⟨rb, nb⟩ := bodyPair
          rw [hbody] at hrun
          have hcalm := hbodyCalm fuel ⟨calleeLocals, s.globals, s.memory, s.ffi⟩ rb nb hbody
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases rb with
          | raised l g m ffi exception value => cases hcalm
          | finalFfi l g m ffi event => cases hcalm
          | returned l g m ffi returned =>
            simp only at hrun
            split at hrun
            · cases hassign : assignPanValueCallResult s.locals g destination returned
                  (structs := E.structs) with
              | none => rw [hassign] at hrun; simp at hrun
              | some assigned =>
                rw [hassign] at hrun
                simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                  Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                rfl
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              rfl
          | _ =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            rfl

set_option hygiene false in
/-- Finish a leaf: every outcome of its helper is `.normal` or `.error`. -/
local macro "plain_leaf" helper:ident : tactic => `(tactic| (
  rw [evalPanValueFfiProgSteps] at hrun
  simp only [$helper:ident] at hrun
  repeat' split at hrun
  all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
  all_goals (obtain ⟨rfl, -⟩ := hrun)
  all_goals rfl))

theorem straight_sound (callee : FunName → Bool)
    (hcallee : ∀ f, callee f = true → FunCalm E f) :
    ∀ (fuel : Nat) (p : Prog Word) (s : St σ) (r : Result σ) (n : Nat),
      straight callee p = true → E.run fuel s p = some (r, n) → r.plain = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro p s r n _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro p s r n hs hrun
    simp only [Env.run] at hrun
    cases p with
    | skip =>
      simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      rfl
    | tick =>
      simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      rfl
    | annot key text =>
      simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      rfl
    | assign kind name value =>
      cases kind with
      | global => plain_leaf panValueAssignGlobalResult
      | «local» => plain_leaf panValueAssignLocalResult
    | store address value => plain_leaf panValueStoreResult
    | store32 address value => plain_leaf panValueStore32Result
    | storeByte address value => plain_leaf panValueStoreByteResult
    | primitive name operator arguments => plain_leaf panValuePrimitiveResult
    | seq first second =>
      simp only [straight, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases h₁ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi first (memoryAccess := E.memoryAccess) (contracts := E.contracts)
          (memoryHandler := E.memoryHandler) with
      | none => rw [h₁] at hrun; simp at hrun
      | some pair =>
        obtain ⟨r₁, n₁⟩ := pair
        rw [h₁] at hrun
        have p₁ := ih first s r₁ n₁ hs.1 h₁
        cases r₁ with
        | normal l g m f =>
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases h₂ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f second
              (memoryAccess := E.memoryAccess) (contracts := E.contracts)
              (memoryHandler := E.memoryHandler) with
          | none => rw [h₂] at hrun; simp at hrun
          | some pair₂ =>
            obtain ⟨r₂, n₂⟩ := pair₂
            rw [h₂] at hrun
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih second ⟨l, g, m, f⟩ r₂ n₂ hs.2 h₂
        | error l g m f =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          rfl
        | _ => exact absurd p₁ (by simp [PanValueFfiControlResult.plain])
    | ite condition thenBranch elseBranch =>
      simp only [straight, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
      | some pair =>
        obtain ⟨c, k⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hc : (c != 0) = true
        · rw [if_pos hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi thenBranch (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih thenBranch s rb nb hs.1 hb
        · rw [if_neg hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi elseBranch (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih elseBranch s rb nb hs.2 hb
    | dec name shape value body =>
      simp only [straight] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
      | some accepted =>
        rw [hacc] at hrun
        simp only [Option.elim_some] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel
            (updatePanValueMap s.locals name accepted.1) s.globals s.memory s.ffi body
            (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          have pb := ih body ⟨updatePanValueMap s.locals name accepted.1, s.globals, s.memory,
            s.ffi⟩ rb nb hs hb
          cases rb <;> first | rfl | exact absurd pb (by simp [PanValueFfiControlResult.plain])
    | «while» condition body =>
      have hsb : straight callee body = true := by simpa only [straight] using hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        rfl
      | some pair =>
        obtain ⟨c, k⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hc : (c == 0) = true
        · rw [if_pos hc] at hrun
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          rfl
        · rw [if_neg hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi body (memoryAccess := E.memoryAccess)
              (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            have pb := ih body s rb nb hsb hb
            cases rb with
            | normal l g m f =>
              simp only [Option.bind_eq_bind, Option.bind_some] at hrun
              cases hl : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                  E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
                  (.while condition body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
              | none => rw [hl] at hrun; simp at hrun
              | some pair =>
                obtain ⟨rl, nl⟩ := pair
                rw [hl] at hrun
                simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                  Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                exact ih (.while condition body) ⟨l, g, m, f⟩ rl nl hs hl
            | error l g m f =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              rfl
            | _ => exact absurd pb (by simp [PanValueFfiControlResult.plain])
    | call info f arguments =>
      cases info with
      | none => simp [straight] at hs
      | some pair =>
        obtain ⟨destination, handlerInfo⟩ := pair
        cases handlerInfo with
        | some triple => simp [straight] at hs
        | none =>
          have hf : FunCalm E f := hcallee f (by simpa only [straight] using hs)
          rw [evalPanValueFfiProgSteps] at hrun
          cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
              s.memory s.ffi (some (destination, none)) f arguments
              (memoryAccess := E.memoryAccess) (contracts := E.contracts)
              (memoryHandler := E.memoryHandler) with
          | none => rw [hcall] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rc, nc⟩ := pair
            rw [hcall] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact callSteps_dest_plain hf destination fuel s arguments rc nc hcall
    | decCall name shape f arguments body =>
      simp only [straight, Bool.and_eq_true] at hs
      have hf : FunCalm E f := hcallee f hs.1
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi none f arguments (memoryAccess := E.memoryAccess)
          (contracts := E.contracts) (memoryHandler := E.memoryHandler)
          (preserveReturnLocals := true) with
      | none => rw [hcall] at hrun; simp at hrun
      | some pair =>
        obtain ⟨rc, nc⟩ := pair
        rw [hcall] at hrun
        have hcalm := callSteps_calm hf fuel s arguments true rc nc hcall
        simp only [Option.bind_eq_bind, Option.bind_some] at hrun
        split at hrun
        · split at hrun
          · rename_i returnedLocals g m ffi value _
            cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                (updatePanValueMap s.locals name value) g m ffi body
                (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hb] at hrun; simp at hrun
            | some pair =>
              obtain ⟨rb, nb⟩ := pair
              rw [hb] at hrun
              simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              have pb := ih body ⟨updatePanValueMap s.locals name value, g, m, ffi⟩ rb nb hs.2 hb
              cases rb <;> first | rfl | exact absurd pb (by simp [PanValueFfiControlResult.plain])
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            rfl
        · cases hcalm
        · cases hcalm
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          rfl
        · simp at hrun
    | _ => simp [straight] at hs

end InitECandidate.Solver.GuestBound
