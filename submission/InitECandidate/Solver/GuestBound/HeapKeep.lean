import InitECandidate.Solver.GuestBound.Heap
import InitECandidate.Solver.GuestBound.Keepers

/-!
# The heap pointer stays in the heap

`heap_ptr` is assigned by `mem_init`, `alloc` and `heap_release`. Every call
of `heap_release` passes a local that was declared by `heap_mark()`. `hk`
checks that shape, tracking the set of locals known to hold a word within the
heap, and `hk_sound` shows that checked programs keep `HeapOk`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The locals in `G` hold words not above the end of the heap. -/
def GoodL (G : List VarName) (l : VarName → Option (PanValue Word)) : Prop :=
  ∀ x, x ∈ G → ∃ w : Word, l x = some (.word w) ∧ w.toNat ≤ 2952790016

/-- The heap pointer is in the heap, and so are the good locals of results
that keep running. -/
def HPost (G : List VarName) : Result σ → Prop
  | .normal l g _ _ | .continued l g _ _ | .broke l g _ _ => HeapOk g ∧ GoodL G l
  | .error _ g _ _ | .returned _ g _ _ _ | .raised _ g _ _ _ _ | .finalFfi _ g _ _ _ => HeapOk g

theorem HPost.heapOk {G : List VarName} {r : Result σ} (h : HPost G r) : HeapOk r.st.globals := by
  cases r <;> first | exact h.1 | exact h

/-- Statements that change neither locals nor globals. -/
def plainLeaf : Prog Word → Bool
  | .skip | .tick | .annot _ _ | .break | .continue | .return _ | .raise _ _
  | .store _ _ | .store32 _ _ | .storeByte _ _ | .shMemStore _ _ _ => true
  | _ => false

/-- Results that keep running have the entry locals. -/
def LocalsSame (s : St σ) : Result σ → Prop
  | .normal l _ _ _ | .continued l _ _ _ | .broke l _ _ _ => l = s.locals
  | _ => True

set_option hygiene false in
local macro "plain_leaf" helper:ident : tactic => `(tactic| (
  rw [evalPanValueFfiProgSteps] at hrun
  simp only [$helper:ident] at hrun
  repeat' split at hrun
  all_goals (try (simp only [Option.some.injEq, Prod.mk.injEq] at hrun))
  all_goals (obtain ⟨rfl, -⟩ := hrun)
  all_goals (first | rfl | trivial)))

set_option hygiene false in
local macro "plain_same" : tactic => `(tactic| (
  simp only [evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
  obtain ⟨rfl, -⟩ := hrun
  first | rfl | trivial))

theorem plainLeaf_locals {fuel : Nat} {p : Prog Word} {s : St σ} {r : Result σ} {n : Nat}
    (hp : plainLeaf p = true) (hrun : E.run fuel s p = some (r, n)) : LocalsSame s r := by
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    cases p with
    | skip =>
      simp only [evalPanValueFfiProgSteps, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      rfl
    | tick => plain_same
    | annot key text => plain_same
    | «break» => plain_same
    | «continue» => plain_same
    | «return» value => plain_leaf panValueReturnResult
    | raise exception value => plain_leaf panValueRaiseResult
    | store address value => plain_leaf panValueStoreResult
    | store32 address value => plain_leaf panValueStore32Result
    | storeByte address value => plain_leaf panValueStoreByteResult
    | shMemStore size address value => plain_leaf panValueShMemStoreResult
    | _ => simp [plainLeaf] at hp

theorem plainLeaf_globals {fuel : Nat} {p : Prog Word} {s : St σ} {r : Result σ} {n : Nat}
    (hp : plainLeaf p = true) (hrun : E.run fuel s p = some (r, n)) :
    r.st.globals = s.globals := by
  refine (globalsKeeper E).leaf fuel p s r n ?_ hrun
  cases p <;> first | rfl | simp [plainLeaf] at hp

/-- A plain statement keeps the invariant. -/
theorem plainLeaf_post {G : List VarName} {fuel : Nat} {p : Prog Word} {s : St σ}
    {r : Result σ} {n : Nat} (hp : plainLeaf p = true) (hs : HeapOk s.globals)
    (hG : GoodL G s.locals) (hrun : E.run fuel s p = some (r, n)) : HPost G r := by
  have hg := plainLeaf_globals hp hrun
  have hl := plainLeaf_locals hp hrun
  cases r with
  | normal l g m f =>
    have hg' : g = s.globals := hg
    have hl' : l = s.locals := hl
    subst hg' hl'
    exact ⟨hs, hG⟩
  | continued l g m f =>
    have hg' : g = s.globals := hg
    have hl' : l = s.locals := hl
    subst hg' hl'
    exact ⟨hs, hG⟩
  | broke l g m f =>
    have hg' : g = s.globals := hg
    have hl' : l = s.locals := hl
    subst hg' hl'
    exact ⟨hs, hG⟩
  | error l g m f => have hg' : g = s.globals := hg; subst hg'; exact hs
  | returned l g m f v => have hg' : g = s.globals := hg; subst hg'; exact hs
  | raised l g m f e v => have hg' : g = s.globals := hg; subst hg'; exact hs
  | finalFfi l g m f e => have hg' : g = s.globals := hg; subst hg'; exact hs

/-- A call destination that is neither a good local nor `heap_ptr`. -/
def destOk (G : List VarName) : Option (VarKind × VarName) → Bool
  | none => true
  | some (.local, x) => !G.contains x
  | some (.global, x) => x != "heap_ptr"

/-- The argument list of `heap_release` is one good local. -/
def relArg (G : List VarName) : List (Exp Word) → Bool
  | [.var .local m] => G.contains m
  | _ => false

/-- `p` only moves `heap_ptr` through `alloc`, through `heap_release` of a good
local, or by assigning a good local or the base address; `G` is the set of good locals. -/
def hk : List VarName → Prog Word → Bool
  | G, .seq a b => hk G a && hk G b
  | G, .ite _ a b => hk G a && hk G b
  | G, .while _ b => hk G b
  | G, .dec x _ _ b => hk (G.erase x) b
  | G, .decCall x _ f _ b =>
      if f == "heap_mark" then hk (x :: G) b else f != "heap_release" && hk (G.erase x) b
  | G, .assign .local x _ => !G.contains x
  | G, .assign .global x e =>
      x != "heap_ptr" || (match e with
        | .var .local q => G.contains q
        | .baseAddr => true
        | _ => false)
  | G, .primitive x _ _ => !G.contains x
  | G, .shMemLoad _ .local x _ => !G.contains x
  | _, .shMemLoad _ .global _ _ => false
  | G, .extCall _ _ _ _ _ => G.isEmpty
  | _, .call none f _ => f != "heap_release"
  | G, .call (some (dest, none)) f args => destOk G dest && (f != "heap_release" || relArg G args)
  | G, .call (some (dest, some (_, hv, hp))) f _ =>
      destOk G dest && f != "heap_release" && !G.contains hv && hk G hp
  | _, p => plainLeaf p

theorem heapOk_update {g : VarName → Option (PanValue Word)} {x : VarName} (v : PanValue Word)
    (hx : (x != "heap_ptr") = true) (h : HeapOk g) : HeapOk (updatePanValueMap g x v) := by
  obtain ⟨p, hp, hle⟩ := h
  refine ⟨p, ?_, hle⟩
  have hne : ("heap_ptr" == x) = false := by
    rw [BEq.comm]
    simpa using hx
  simp only [updatePanValueMap, hne]
  exact hp

theorem goodL_update {G : List VarName} {l : VarName → Option (PanValue Word)} {x : VarName}
    (v : PanValue Word) (hx : (!G.contains x) = true) (h : GoodL G l) :
    GoodL G (updatePanValueMap l x v) := by
  intro y hy
  obtain ⟨w, hw, hle⟩ := h y hy
  refine ⟨w, ?_, hle⟩
  have hne : (y == x) = false := by
    simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not] at hx
    simp only [beq_eq_false_iff_ne, ne_eq]
    exact fun hh => hx (hh ▸ hy)
  simp only [updatePanValueMap, hne]
  exact hw

/-- Assigning a call result to an allowed destination keeps the invariant. -/
theorem assign_post {G : List VarName} {structs : StructContext}
    {l g l' g' : VarName → Option (PanValue Word)} {dest : Option (VarKind × VarName)}
    {values : List (PanValue Word)} (hd : destOk G dest = true) (hg : HeapOk g) (hl : GoodL G l)
    (h : assignPanValueCallResult l g dest values (structs := structs) = some (l', g')) :
    HeapOk g' ∧ GoodL G l' := by
  unfold assignPanValueCallResult at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hg, hl⟩
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hg, hl⟩
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hg, goodL_update _ hd hl⟩
    · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨heapOk_update _ hd hg, hl⟩
    · cases h
  · cases h

/-- What a call without destination returned comes from a run of the callee. -/
def RetFrom (E : Env σ) (fuel : Nat) (s : St σ) (f : FunName) (arguments : List (Exp Word))
    (rc : Result σ) : Prop :=
  ∀ lr g m ffi vs, rc = .returned lr g m ffi vs →
    ∃ values parameters body cl lb nb, E.evalArgs s arguments = some values ∧
      lookupPanFunction f E.functions = some (parameters, body) ∧
      bindPanValueParameters parameters values = some cl ∧
      E.run fuel ⟨cl, s.globals, s.memory, s.ffi⟩ body = some (.returned lb g m ffi vs, nb)

set_option maxHeartbeats 1000000 in
/-- A call keeps the invariant when the callee body and the handler do. -/
theorem callSteps_hk (G : List VarName) {f : FunName}
    {info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word))}
    (fuel : Nat) (s : St σ) (arguments : List (Exp Word)) (preserve : Bool) (rc : Result σ)
    (nc : Nat) (hs : HeapOk s.globals) (hG : GoodL G s.locals)
    (hdest : ∀ dest h, info = some (dest, h) → destOk G dest = true)
    (hcallee : ∀ values parameters body cl, E.evalArgs s arguments = some values →
      lookupPanFunction f E.functions = some (parameters, body) →
      bindPanValueParameters parameters values = some cl →
      ∀ rb nb, E.run (fuel - 1) ⟨cl, s.globals, s.memory, s.ffi⟩ body = some (rb, nb) →
        HeapOk rb.st.globals)
    (hh : ∀ dest exc hv hp, info = some (dest, some (exc, hv, hp)) →
      ∀ v g m ffi r n, HeapOk g →
        E.run (fuel - 1) ⟨updatePanValueMap s.locals hv v, g, m, ffi⟩ hp = some (r, n) →
        HPost G r)
    (hrun : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
      E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi info f
      arguments (memoryAccess := E.memoryAccess) (contracts := E.contracts)
      (memoryHandler := E.memoryHandler) (preserveReturnLocals := preserve) = some (rc, nc)) :
    HPost G rc ∧ (info = none → RetFrom E (fuel - 1) s f arguments rc) := by
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
      exact ⟨hs, fun _ _ _ _ _ _ h => by cases h⟩
    | some argumentPair =>
      obtain ⟨values, argumentSteps⟩ := argumentPair
      rw [hargs] at hrun
      have hvalues : E.evalArgs s arguments = some values := by
        simp only [panValueCallArguments, evalPanValueExpsCounted, Option.map_eq_some_iff,
          Prod.mk.injEq] at hargs
        obtain ⟨vs, hvs, rfl, -⟩ := hargs
        exact hvs
      simp only [Option.elim_some] at hrun
      cases htarget : panValueCallTarget E.structs E.contracts f E.functions values with
      | none =>
        rw [htarget] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact ⟨hs, fun _ _ _ _ _ _ h => by cases h⟩
      | some callTarget =>
        obtain ⟨body, calleeLocals⟩ := callTarget
        rw [htarget] at hrun
        simp only [Option.elim_some] at hrun
        have hlookup : ∃ parameters, lookupPanFunction f E.functions = some (parameters, body) ∧
            bindPanValueParameters parameters values = some calleeLocals := by
          simp only [panValueCallTarget] at htarget
          split at htarget
          · simp at htarget
          · rename_i parameters body' hlookup
            split at htarget
            · split at htarget
              · rename_i locals hbind
                simp only [Option.some.injEq, Prod.mk.injEq] at htarget
                obtain ⟨rfl, rfl⟩ := htarget
                exact ⟨parameters, hlookup, hbind⟩
              · simp at htarget
            · simp at htarget
        obtain ⟨parameters, hlookup, hbind⟩ := hlookup
        cases hbody : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel calleeLocals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess) (contracts := E.contracts)
            (memoryHandler := E.memoryHandler) with
        | none => rw [hbody] at hrun; simp at hrun
        | some bodyPair =>
          obtain ⟨rb, nb⟩ := bodyPair
          rw [hbody] at hrun
          have hrb : HeapOk rb.st.globals :=
            hcallee values parameters body calleeLocals hvalues hlookup hbind rb nb hbody
          simp only [Option.bind_eq_bind, Option.bind_some] at hrun
          cases rb with
          | returned l g m ffi returned =>
            simp only at hrun
            split at hrun
            · cases info with
              | none =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                refine ⟨hrb, fun _ lr g' m' ffi' vs h => ?_⟩
                simp only [PanValueFfiControlResult.returned.injEq] at h
                obtain ⟨-, rfl, rfl, rfl, rfl⟩ := h
                exact ⟨values, parameters, body, calleeLocals, l, nb, hvalues, hlookup, hbind,
                  hbody⟩
              | some pair =>
                obtain ⟨destination, handlerInfo⟩ := pair
                simp only at hrun
                cases hassign : assignPanValueCallResult s.locals g destination returned
                    (structs := E.structs) with
                | none => rw [hassign] at hrun; simp at hrun
                | some assigned =>
                  obtain ⟨locals', globals'⟩ := assigned
                  rw [hassign] at hrun
                  simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                    Prod.mk.injEq] at hrun
                  obtain ⟨rfl, -⟩ := hrun
                  exact ⟨assign_post (hdest _ _ rfl) hrb hG hassign, fun h => by cases h⟩
            · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact ⟨hrb, fun _ _ _ _ _ _ h => by cases h⟩
          | raised l g m ffi exception value =>
            simp only at hrun
            split at hrun
            · cases info with
              | none =>
                simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                exact ⟨hrb, fun _ _ _ _ _ _ h => by cases h⟩
              | some pair =>
                obtain ⟨destination, handlerInfo⟩ := pair
                cases handlerInfo with
                | none =>
                  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                  obtain ⟨rfl, -⟩ := hrun
                  exact ⟨hrb, fun h => by cases h⟩
                | some triple =>
                  obtain ⟨caught, handlerVar, handlerProgram⟩ := triple
                  simp only at hrun
                  split at hrun
                  · split at hrun
                    · cases hhandler : evalPanValueFfiProgSteps E.context E.primitive E.handler
                          E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                          (updatePanValueMap s.locals handlerVar value) g m ffi
                          handlerProgram (memoryAccess := E.memoryAccess)
                          (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
                      | none => rw [hhandler] at hrun; simp at hrun
                      | some handlerPair =>
                        obtain ⟨rh, nh⟩ := handlerPair
                        rw [hhandler] at hrun
                        simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                          Prod.mk.injEq] at hrun
                        obtain ⟨rfl, -⟩ := hrun
                        exact ⟨hh destination caught handlerVar handlerProgram rfl value g m ffi
                          _ nh hrb hhandler, fun h => by cases h⟩
                    · simp at hrun
                  · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
                    obtain ⟨rfl, -⟩ := hrun
                    exact ⟨hrb, fun h => by cases h⟩
            · simp at hrun
          | _ =>
            simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            first
              | exact ⟨hrb, fun _ _ _ _ _ _ h => by cases h⟩

end InitECandidate.Solver.GuestBound
