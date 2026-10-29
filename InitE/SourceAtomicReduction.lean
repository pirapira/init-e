import InitE.SourceReduction

namespace InitE.SourceAtomicReduction
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

/-- Lift an existing state equation, choosing the small operational context. -/
theorem context_output {σ : Type} (context : FiniteEvalContext 64 σ)
    (program : ProgHOL 64) (output : Option (PanSemResultExact 64) × FiniteEvalContext 64 σ)
    (checked : evaluateHOLFiniteState context.state program = (output.1, output.2.state)) :
    evalPanSemRecursiveCallFiniteContext program context = some output := by
  obtain ⟨post, run, same⟩ := evalPanSemRecursiveCallFiniteContext_of_evaluateHOLFiniteState
    context.state program context rfl (output.1, output.2.state) checked
  have equal : post = output.2 := FiniteEvalContext.ext same
  simpa only [equal] using run

def assignContext {σ : Type} (context : FiniteEvalContext 64 σ)
    (kind : VarKind) (name : MlS) (source : ExpHOL 64) :
    Option (PanSemResultExact 64) × FiniteEvalContext 64 σ :=
  letI : DecidablePred context.state.memaddrs := context.memaddrsDecidable
  match evalHOLFinite context.state source with
  | none => (some .error, context)
  | some value =>
    if isValidValueHOLFinite context.state kind name value then
      (none, context.withState (setKvarHOLFinite kind name value context.state)
        (by cases kind <;> rfl) (by cases kind <;> rfl))
    else (some .error, context)

@[scoped cbv_eval] theorem assign_context {σ : Type} (context : FiniteEvalContext 64 σ)
    (kind : VarKind) (name : MlS) (source : ExpHOL 64) :
    evalPanSemRecursiveCallFiniteContext (.assign kind name source) context =
      some (assignContext context kind name source) := by
  apply context_output
  rw [evaluateHOLFiniteState_assign]
  have domains : (fun address => Classical.propDecidable (context.state.memaddrs address)) =
      context.memaddrsDecidable := Subsingleton.elim _ _
  rw [domains]
  unfold assignContext evalHOLFinite
  cases @evalHOLExact 64 σ _ context.state.toExact context.memaddrsDecidable source with
  | none => rfl
  | some value => dsimp only; split <;> rfl

def storeContext {σ : Type} (context : FiniteEvalContext 64 σ)
    (destination source : ExpHOL 64) :
    Option (PanSemResultExact 64) × FiniteEvalContext 64 σ :=
  letI : DecidablePred context.state.memaddrs := context.memaddrsDecidable
  match evalHOLFinite context.state destination with
  | some (.val (.word address)) =>
    match evalHOLFinite context.state source with
    | some value =>
      match panMemStoresHOL address (flattenHOL value) context.state.memaddrs context.state.memory with
      | some memory => (none, context.withState {context.state with memory := memory} rfl rfl)
      | none => (some .error, context)
    | none => (some .error, context)
  | _ => (some .error, context)

@[scoped cbv_eval] theorem store_context {σ : Type} (context : FiniteEvalContext 64 σ)
    (destination source : ExpHOL 64) :
    evalPanSemRecursiveCallFiniteContext (.store destination source) context =
      some (storeContext context destination source) := by
  apply context_output
  rw [evaluateHOLFiniteState_store]
  have domains : (fun address => Classical.propDecidable (context.state.memaddrs address)) =
      context.memaddrsDecidable := Subsingleton.elim _ _
  rw [domains]
  unfold storeContext evalHOLFinite
  cases @evalHOLExact 64 σ _ context.state.toExact context.memaddrsDecidable destination with
  | none => rfl
  | some destinationValue =>
    cases destinationValue with
    | val payload =>
      cases payload with
      | word address =>
        dsimp only
        cases @evalHOLExact 64 σ _ context.state.toExact context.memaddrsDecidable source with
        | none => rfl
        | some value =>
          dsimp only
          cases @panMemStoresHOL 64 _ address (flattenHOL value) context.state.memaddrs
            context.memaddrsDecidable context.state.memory <;> rfl
    | rStruct _ => rfl
    | nStruct _ _ => rfl

def storeByteContext {σ : Type} (context : FiniteEvalContext 64 σ)
    (destination source : ExpHOL 64) :
    Option (PanSemResultExact 64) × FiniteEvalContext 64 σ :=
  letI : DecidablePred context.state.memaddrs := context.memaddrsDecidable
  match evalHOLFinite context.state destination with
  | some (.val (.word address)) =>
    match evalHOLFinite context.state source with
    | some (.val (.word value)) =>
      match panMemStoreByteWord8HOL context.state.memory context.state.memaddrs
          context.state.be address (BitVec.ofNat 8 value.toNat) with
      | some memory => (none, context.withState {context.state with memory := memory} rfl rfl)
      | none => (some .error, context)
    | _ => (some .error, context)
  | _ => (some .error, context)

@[scoped cbv_eval] theorem store_byte_context {σ : Type} (context : FiniteEvalContext 64 σ)
    (destination source : ExpHOL 64) :
    evalPanSemRecursiveCallFiniteContext (.storeByte destination source) context =
      some (storeByteContext context destination source) := by
  apply context_output
  rw [evaluateHOLFiniteState_storeByte]
  have domains : (fun address => Classical.propDecidable (context.state.memaddrs address)) =
      context.memaddrsDecidable := Subsingleton.elim _ _
  rw [domains]
  unfold storeByteContext evalHOLFinite
  cases @evalHOLExact 64 σ _ context.state.toExact context.memaddrsDecidable destination with
  | none => rfl
  | some destinationValue =>
    cases destinationValue with
    | val payload =>
      cases payload with
      | word address =>
        dsimp only
        cases @evalHOLExact 64 σ _ context.state.toExact context.memaddrsDecidable source with
        | none => rfl
        | some value =>
          cases value with
          | val payload =>
            cases payload with
            | word value =>
              dsimp only
              cases @panMemStoreByteWord8HOL 64 _ context.state.memory context.state.memaddrs
                context.memaddrsDecidable context.state.be address (BitVec.ofNat 8 value.toNat) <;> rfl
          | rStruct _ => rfl
          | nStruct _ _ => rfl
    | rStruct _ => rfl
    | nStruct _ _ => rfl

end InitE.SourceAtomicReduction
