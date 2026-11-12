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
  ∀ x, x ∈ G → ∃ w : Word, l x = some (.word w) ∧ InHeap w

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
  | G, .dec x _ _ b => hk (G.filter (· != x)) b
  | G, .decCall x _ f _ b =>
      if f == "heap_mark" then hk (x :: G) b else f != "heap_release" && hk (G.filter (· != x)) b
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

/-- `trap_with` changes no global. -/
theorem trap_with_globals (hE : GuestEnv E) : FunKeeps (globalsKeeper E) "trap_with" :=
  keepFn_sound (globalsKeeper E) hE.functions 1 "trap_with"
    (show keepFn globalsLeaf Guest.Software.guestAst 1 "trap_with" = true by decide +kernel)

/-- The guard `if c { trap_with(…); }` changes no global. -/
theorem trapIte_globals (hE : GuestEnv E) {c : Exp Word} {arguments : List (Exp Word)}
    {s : St σ} {r : Result σ}
    (h : Runs E s (.ite c (.call (some (none, none)) "trap_with" arguments) .skip) r) :
    r.st.globals = s.globals := by
  obtain ⟨fuel, n, hrun⟩ := h
  exact keepWith_sound (globalsKeeper E) (fun f => f == "trap_with")
    (fun f hf => by
      have : f = "trap_with" := by simpa using hf
      subst this
      exact trap_with_globals hE)
    fuel _ s r n
    (show keepWith globalsLeaf (fun f => f == "trap_with")
      (.ite c (.call (some (none, none)) "trap_with" arguments) .skip) = true by
      simp [keepWith, destLocal, globalsLeaf]) hrun

theorem st_globals_restore (x : VarName) (old : Option (PanValue Word)) (r : Result σ) :
    (restorePanValueFfiLocal x old r).st.globals = r.st.globals := by
  cases r <;> rfl

set_option maxHeartbeats 2000000 in
/-- `alloc` keeps the heap pointer in the heap, whatever its argument and outcome. -/
theorem alloc_keeps (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "alloc" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (hs : HeapOk s.globals) (h : Runs E s body r) :
    HeapOk r.st.globals := by
  have hbody := (fun_of_index 7 hE.functions (by guest_decl_at 7) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  obtain ⟨pv, hpv, hple⟩ := id hs
  rw [runs_dec] at h
  simp only [eval_global, hpv, shape_word, shape_matches_self, if_true] at h
  obtain ⟨r1, h1, rfl⟩ := h
  rw [st_globals_restore]
  obtain ⟨ra, ha, hrest⟩ := runs_seq.mp h1
  have hga := trapIte_globals hE ha
  have hgd := trapIte_guard hE ha
  cases ra with
  | normal l g m f =>
    obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hgd
    simp only at hrest
    rw [runs_dec] at hrest
    split at hrest
    · rename_i vq hvq
      have hal : ∀ yv : Word, vq = .word yv → yv.toNat % 8 = 0 := by
        intro yv hyv
        subst hyv
        obtain ⟨va, vb, w, -, hvb, hw, hwe⟩ := eval_op2_inv hE.word hvq
        simp only [PanValue.word.injEq] at hwe
        subst hwe
        simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, wordsProj_cons, wordsProj_nil,
          wordOp] at hvb
        subst hvb
        simp [wordOp] at hw
        rw [← hw]
        have hm8 := and_m8 va
        have e1 : (0#64 - 8#64 : Word) = 18446744073709551608#64 := by decide
        have e2 : ~~~(0 : BitVec 64) = 18446744073709551615#64 := by decide
        rw [e1, e2] at hm8
        omega
      split at hrest
      · obtain ⟨r2, h2, rfl⟩ := hrest
        rw [st_globals_restore]
        obtain ⟨rb, hb, hrest2⟩ := runs_seq.mp h2
        have hgb := trapIte_globals hE hb
        have hgd2 := trapIte_guard hE hb
        cases rb with
        | normal l g m f =>
          obtain ⟨rfl, rfl, rfl, rfl, hc0⟩ := hgd2
          simp only at hrest2
          -- the guard was false: `q` is a word not above the end of the heap
          rw [evalF_cmp hE.word] at hc0
          simp only [eval_const] at hc0
          split at hc0
          · rename_i x y hx hy
            simp only [Option.some.injEq, PanValue.word.injEq] at hx hc0
            subst hx
            have hle : InHeap y := by
              have := lower_zero hc0
              rw [BitVec.lt_def] at this
              have hE' : (2952790016#64 : Word).toNat = 2952790016 := by decide
              refine ⟨by omega, hal y ?_⟩
              rw [evalF_local] at hy
              simpa [updatePanValueMap] using hy
            obtain ⟨r3, h3, hrest3⟩ := runs_seq.mp hrest2
            rw [runs_assign_global, hy] at h3
            simp only at h3
            split at h3
            · subst h3
              simp only at hrest3
              rw [runs_return] at hrest3
              subst hrest3
              have hok : HeapOk (updatePanValueMap s.globals "heap_ptr" (PanValue.word y)) :=
                ⟨y, by simp [updatePanValueMap], hle⟩
              split
              · split
                · exact hok
                · exact hok
              · exact hok
            · subst h3
              simp only [St.err] at hrest3
              subst hrest3
              exact hs
          · cases hc0
        | error l g m f => simp only at hrest2; subst hrest2; rw [hgb]; exact hs
        | raised l g m f e v => simp only at hrest2; subst hrest2; rw [hgb]; exact hs
        | finalFfi l g m f e => simp only at hrest2; subst hrest2; rw [hgb]; exact hs
        | _ => exact hgd2.elim
      · subst hrest
        exact hs
    · subst hrest
      exact hs
  | error l g m f => simp only at hrest; subst hrest; rw [hga]; exact hs
  | raised l g m f e v => simp only at hrest; subst hrest; rw [hga]; exact hs
  | finalFfi l g m f e => simp only at hrest; subst hrest; rw [hga]; exact hs
  | _ => exact hgd.elim

/-- `heap_release(m)` with `m` within the heap keeps the heap pointer in the heap. -/
theorem heap_release_keeps (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "heap_release" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (hs : HeapOk s.globals)
    (hm : ∃ w : Word, s.locals "m" = some (.word w) ∧ InHeap w)
    (h : Runs E s body r) : HeapOk r.st.globals := by
  obtain ⟨pv, hp, -⟩ := hs
  obtain ⟨w, hw, hle⟩ := hm
  have := heap_release_runs hE parameters body hlookup s r pv w hp hw h
  subst this
  exact ⟨w, by simp [PanValueFfiControlResult.st, updatePanValueMap], hle⟩

theorem HPost.of_globals {s : St σ} {r : Result σ} (hg : r.st.globals = s.globals)
    (hH : HeapOk s.globals) : HPost [] r := by
  cases r <;> simp only [PanValueFfiControlResult.st] at hg <;> subst hg
  all_goals first
    | exact ⟨hH, fun _ h => by cases h⟩
    | exact hH

theorem HPost.of_error {G : List VarName} {s : St σ} {r : Result σ} (herr : r.isError = true)
    (hg : r.st.globals = s.globals) (hH : HeapOk s.globals) : HPost G r := by
  cases r <;> first
    | (simp only [PanValueFfiControlResult.st] at hg; subst hg; exact hH)
    | cases herr

/-- Good locals after binding `x`. -/
theorem goodL_bind {G G' : List VarName} {l : VarName → Option (PanValue Word)} {x : VarName}
    {v : PanValue Word} (h : GoodL G l)
    (hx : x ∈ G' → ∃ w : Word, v = .word w ∧ InHeap w)
    (hsub : ∀ y, y ∈ G' → y ≠ x → y ∈ G) : GoodL G' (updatePanValueMap l x v) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    obtain ⟨w, rfl, hle⟩ := hx hy
    exact ⟨w, by simp [updatePanValueMap], hle⟩
  · obtain ⟨w, hw, hle⟩ := h y (hsub y hy hyx)
    have hne : (y == x) = false := by simpa using hyx
    exact ⟨w, by simp only [updatePanValueMap, hne]; exact hw, hle⟩

/-- The invariant after the scope of a declaration of `x` ends. -/
theorem hpost_restore {G G' : List VarName} {x : VarName} {old : Option (PanValue Word)}
    {rb : Result σ} (hsub : ∀ y, y ∈ G → y ≠ x → y ∈ G')
    (hold : x ∈ G → ∃ w : Word, old = some (.word w) ∧ InHeap w)
    (h : HPost G' rb) : HPost G (restorePanValueFfiLocal x old rb) := by
  have key : ∀ l : VarName → Option (PanValue Word), GoodL G' l →
      GoodL G (restorePanValueLocal l x old) := by
    intro l hl y hy
    by_cases hyx : y = x
    · subst hyx
      obtain ⟨w, rfl, hle⟩ := hold hy
      exact ⟨w, by simp [restorePanValueLocal], hle⟩
    · obtain ⟨w, hw, hle⟩ := hl y (hsub y hy hyx)
      have hne : (y == x) = false := by simpa using hyx
      exact ⟨w, by simp only [restorePanValueLocal, hne]; exact hw, hle⟩
  cases rb with
  | normal l g m f => exact ⟨h.1, key l h.2⟩
  | continued l g m f => exact ⟨h.1, key l h.2⟩
  | broke l g m f => exact ⟨h.1, key l h.2⟩
  | _ => exact h

theorem mem_filter_ne {G : List VarName} {x y : VarName} :
    y ∈ G.filter (· != x) ↔ y ∈ G ∧ y ≠ x := by
  simp [List.mem_filter]

theorem eval_baseAddr (s : St σ) : E.eval s .baseAddr = some (.word E.baseAddress) := by
  simp [Env.eval, evalPanValueExp]

set_option maxHeartbeats 4000000 in
/-- Checked programs keep the heap pointer in the heap, provided every function
body other than `alloc` and `heap_release` is checked. -/
theorem hk_sound (hE : GuestEnv E)
    (hfun : ∀ f parameters body, lookupPanFunction f E.functions = some (parameters, body) →
      f ≠ "alloc" → f ≠ "heap_release" → hk [] body = true) :
    ∀ (fuel : Nat) (p : Prog Word) (G : List VarName) (s : St σ) (r : Result σ) (n : Nat),
      hk G p = true → HeapOk s.globals → GoodL G s.locals → E.run fuel s p = some (r, n) →
      HPost G r := by
  intro fuel
  induction fuel using Nat.strongRecOn with
  | _ fuel sih =>
  cases fuel with
  | zero =>
    intro p G s r n _ _ _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    have ih := sih fuel (Nat.lt_succ_self fuel)
    intro p G s r n hs hH hG hrun0
    have hrun := hrun0
    simp only [Env.run] at hrun
    have hcal : ∀ (f : FunName) (arguments : List (Exp Word)), f ≠ "heap_release" →
        ∀ values parameters body cl, E.evalArgs s arguments = some values →
        lookupPanFunction f E.functions = some (parameters, body) →
        bindPanValueParameters parameters values = some cl →
        ∀ rb nb, E.run (fuel - 1) ⟨cl, s.globals, s.memory, s.ffi⟩ body = some (rb, nb) →
          HeapOk rb.st.globals := by
      intro f arguments hf values parameters body cl _ hlookup _ rb nb hrunb
      by_cases hfa : f = "alloc"
      · subst hfa
        exact alloc_keeps hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb hH
          (Runs.of_run hrunb)
      · exact (sih (fuel - 1) (by omega) body [] ⟨cl, s.globals, s.memory, s.ffi⟩ rb nb
          (hfun f parameters body hlookup hfa hf) hH (fun _ h => by cases h) hrunb).heapOk
    cases p with
    | seq first second =>
      simp only [hk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases h₁ : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                    E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi first
                    (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                    (memoryHandler := E.memoryHandler) with
      | none => rw [h₁] at hrun; simp at hrun
      | some pair =>
        obtain ⟨r₁, n₁⟩ := pair
        rw [h₁] at hrun
        have p₁ := ih first G s r₁ n₁ hs.1 hH hG h₁
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
            exact ih second G ⟨l, g, m, f⟩ r₂ n₂ hs.2 p₁.1 p₁.2 h₂
        | _ =>
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact p₁
    | ite condition thenBranch elseBranch =>
      simp only [hk, Bool.and_eq_true] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact hH
      | some pair =>
        obtain ⟨c, k⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hc : (c != 0) = true
        · rw [if_pos hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                    E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi thenBranch
                    (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                    (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih thenBranch G s rb nb hs.1 hH hG hb
        · rw [if_neg hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                    E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi elseBranch
                    (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                    (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact ih elseBranch G s rb nb hs.2 hH hG hb
    | dec name shape value body =>
      simp only [hk] at hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory value E.memoryAccess shape with
      | none =>
        rw [hacc] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact hH
      | some accepted =>
        rw [hacc] at hrun
        simp only [Option.elim_some] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                    E.functions E.baseAddress E.topAddress E.bytesInWord fuel (updatePanValueMap s.locals name accepted.1) s.globals s.memory s.ffi body
                    (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                    (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at hrun
          simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          have pb := ih body (G.filter (· != name))
            ⟨updatePanValueMap s.locals name accepted.1, s.globals, s.memory, s.ffi⟩ rb nb hs hH
            (goodL_bind hG (fun h => absurd rfl (mem_filter_ne.mp h).2)
              (fun y hy _ => (mem_filter_ne.mp hy).1)) hb
          exact hpost_restore (fun y hy hne => mem_filter_ne.mpr ⟨hy, hne⟩) (fun h => hG name h) pb
    | «while» condition body =>
      have hsb : hk G body = true := by simpa only [hk] using hs
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
          s.locals s.globals s.memory condition E.memoryAccess with
      | none =>
        rw [hcond] at hrun
        simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        exact hH
      | some pair =>
        obtain ⟨c, k⟩ := pair
        rw [hcond] at hrun
        simp only [Option.elim_some] at hrun
        by_cases hc : (c == 0) = true
        · rw [if_pos hc] at hrun
          simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact ⟨hH, hG⟩
        · rw [if_neg hc] at hrun
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                    E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi body
                    (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                    (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some pair =>
            obtain ⟨rb, nb⟩ := pair
            rw [hb] at hrun
            have pb := ih body G s rb nb hsb hH hG hb
            have again : ∀ l g m f, HeapOk g → GoodL G l → (do
                  let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                    E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord
                    fuel l g m f (.while condition body) (memoryAccess := E.memoryAccess)
                    (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                  pure (loopResult, k + nb + loopSteps + 1)) = some (r, n) →
                HPost G r := by
              intro l g m f hg hl hrun
              cases hl' : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                  E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g m f
                  (.while condition body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
              | none => rw [hl'] at hrun; simp at hrun
              | some pair =>
                obtain ⟨rl, nl⟩ := pair
                rw [hl'] at hrun
                simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                  Option.some.injEq, Prod.mk.injEq] at hrun
                obtain ⟨rfl, -⟩ := hrun
                exact ih (.while condition body) G ⟨l, g, m, f⟩ _ nl hs hg hl hl'
            cases rb with
            | normal l g m f => exact again l g m f pb.1 pb.2 hrun
            | continued l g m f => exact again l g m f pb.1 pb.2 hrun
            | broke l g m f =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact pb
            | _ =>
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              exact pb
    | call info f arguments =>
      rw [evalPanValueFfiProgSteps] at hrun
      cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory
          s.ffi info f arguments (memoryAccess := E.memoryAccess)
          (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
      | none => rw [hcall] at hrun; simp at hrun
      | some pair =>
        obtain ⟨rc, nc⟩ := pair
        rw [hcall] at hrun
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        cases info with
        | none =>
          have hf : f ≠ "heap_release" := by simpa [hk] using hs
          exact (callSteps_hk G fuel s arguments false _ nc hH hG (fun _ _ h => by cases h)
            (hcal f arguments hf) (fun _ _ _ _ h => by cases h) hcall).1
        | some pair =>
          obtain ⟨dest, handler⟩ := pair
          cases handler with
          | none =>
            simp only [hk, Bool.and_eq_true, Bool.or_eq_true] at hs
            obtain ⟨hd, hfr⟩ := hs
            refine (callSteps_hk G fuel s arguments false _ nc hH hG
              (fun d h heq => by cases heq; exact hd) ?_ (fun _ _ _ _ h => by cases h) hcall).1
            by_cases hf : f = "heap_release"
            · subst hf
              have hra : relArg G arguments = true := by
                rcases hfr with h | h
                · simp at h
                · exact h
              intro values parameters body cl hvalues hlookup hbind rb nb hrunb
              unfold relArg at hra
              split at hra
              · rename_i m
                obtain ⟨w, hw, hle⟩ := hG m (by simpa using hra)
                have hparams := (fun_of_index 9 hE.functions (by guest_decl_at 9)
                  (by decide +kernel) hlookup).2
                simp only [evalArgs_cons, evalArgs_nil, evalF_local, hw, Option.map_some,
                  Option.some.injEq] at hvalues
                subst hvalues
                rw [hparams] at hbind
                simp [bindPanValueParameters] at hbind
                exact heap_release_keeps hE parameters body hlookup
                  ⟨cl, s.globals, s.memory, s.ffi⟩ rb hH
                  ⟨w, by rw [← hbind]; simp [updatePanValueMap], hle⟩ (Runs.of_run hrunb)
              · cases hra
            · exact hcal f arguments hf
          | some triple =>
            obtain ⟨exc, hv, hp⟩ := triple
            simp only [hk, Bool.and_eq_true] at hs
            obtain ⟨⟨⟨hd, hf⟩, hhv⟩, hhp⟩ := hs
            refine (callSteps_hk G fuel s arguments false _ nc hH hG
              (fun d h heq => by cases heq; exact hd) (hcal f arguments (by simpa using hf)) ?_
              hcall).1
            intro d e v' p' heq v g m ffi r n hg hrunh
            cases heq
            exact sih (fuel - 1) (by omega) _ G _ r n hhp hg (goodL_update v hhv hG) hrunh
    | decCall name shape f arguments body =>
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
        have hfr : f ≠ "heap_release" := by
          by_cases hm : f = "heap_mark"
          · rw [hm]; decide
          · have hm' : (f == "heap_mark") = false := by simpa using hm
            simp only [hk, hm', Bool.false_eq_true, if_false, Bool.and_eq_true] at hs
            simpa using hs.1
        obtain ⟨hrc, hret⟩ := callSteps_hk G fuel s arguments true rc nc hH hG
          (fun _ _ h => by cases h) (hcal f arguments hfr) (fun _ _ _ _ h => by cases h) hcall
        simp only [Option.bind_eq_bind, Option.bind_some] at hrun
        split at hrun
        · split at hrun
          · rename_i returnedLocals g m ffi value _
            cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                    E.functions E.baseAddress E.topAddress E.bytesInWord fuel (updatePanValueMap s.locals name value) g m ffi body
                    (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                    (memoryHandler := E.memoryHandler) with
            | none => rw [hb] at hrun; simp at hrun
            | some pair =>
              obtain ⟨rb, nb⟩ := pair
              rw [hb] at hrun
              simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq] at hrun
              obtain ⟨rfl, -⟩ := hrun
              have hg : HeapOk g := hrc
              by_cases hm : f = "heap_mark"
              · subst hm
                have hsb : hk (name :: G) body = true := by simpa [hk] using hs
                obtain ⟨values, parameters, cbody, cl, lb, nb', -, hlookup, -, hrunc⟩ :=
                  hret rfl _ _ _ _ _ rfl
                obtain ⟨pv, hpv, hple⟩ := id hH
                have hmark := heap_mark_runs hE parameters cbody hlookup
                  ⟨cl, s.globals, s.memory, s.ffi⟩ _ pv hpv (Runs.of_run hrunc)
                simp only [PanValueFfiControlResult.returned.injEq, List.cons.injEq,
                  and_true] at hmark
                obtain ⟨-, -, -, -, rfl⟩ := hmark
                have pb := ih body (name :: G)
                  ⟨updatePanValueMap s.locals name (.word pv), g, m, ffi⟩ rb nb hsb hg
                  (goodL_bind hG (fun _ => ⟨pv, rfl, hple⟩)
                    (fun y hy hne => (List.mem_cons.mp hy).resolve_left hne)) hb
                exact hpost_restore (fun y hy _ => List.mem_cons_of_mem _ hy)
                  (fun h => hG name h) pb
              · have hm' : (f == "heap_mark") = false := by simpa using hm
                simp only [hk, hm', Bool.false_eq_true, if_false, Bool.and_eq_true] at hs
                have pb := ih body (G.filter (· != name))
                  ⟨updatePanValueMap s.locals name value, g, m, ffi⟩ rb nb hs.2 hg
                  (goodL_bind hG (fun h => absurd rfl (mem_filter_ne.mp h).2)
                    (fun y hy _ => (mem_filter_ne.mp hy).1)) hb
                exact hpost_restore (fun y hy hne => mem_filter_ne.mpr ⟨hy, hne⟩)
                  (fun h => hG name h) pb
          · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, -⟩ := hrun
            exact hrc
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact hrc
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact hrc
        · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          exact hrc
        · simp at hrun
    | skip => exact plainLeaf_post rfl hH hG hrun0
    | tick => exact plainLeaf_post rfl hH hG hrun0
    | annot key text => exact plainLeaf_post rfl hH hG hrun0
    | «break» => exact plainLeaf_post rfl hH hG hrun0
    | «continue» => exact plainLeaf_post rfl hH hG hrun0
    | «return» value => exact plainLeaf_post rfl hH hG hrun0
    | raise exception value => exact plainLeaf_post rfl hH hG hrun0
    | store address value => exact plainLeaf_post rfl hH hG hrun0
    | store32 address value => exact plainLeaf_post rfl hH hG hrun0
    | storeByte address value => exact plainLeaf_post rfl hH hG hrun0
    | shMemStore size address value => exact plainLeaf_post rfl hH hG hrun0
    | assign kind name value =>
      cases kind with
      | «local» =>
        have hx : (!G.contains name) = true := by simpa only [hk] using hs
        have hgl : r.st.globals = s.globals := (globalsKeeper E).leaf _ _ s r n rfl hrun0
        rcases assign_local_inv hrun0 with herr | ⟨v, -, rfl⟩
        · exact HPost.of_error herr hgl hH
        · exact ⟨hH, goodL_update v hx hG⟩
      | global =>
        have hr := runs_assign_global.mp (Runs.of_run hrun0)
        subst hr
        split
        · rename_i v hv
          split
          · show HeapOk (updatePanValueMap s.globals name v) ∧ GoodL G s.locals
            refine ⟨?_, hG⟩
            simp only [hk, Bool.or_eq_true] at hs
            rcases hs with hne | hval
            · exact heapOk_update v hne hH
            · split at hval
              · rename_i q
                obtain ⟨w, hw, hle⟩ := hG q (by simpa using hval)
                rw [evalF_local, hw] at hv
                simp only [Option.some.injEq] at hv
                subst hv
                by_cases hn : (name != "heap_ptr") = true
                · exact heapOk_update _ hn hH
                · have : name = "heap_ptr" := by simpa using hn
                  subst this
                  exact ⟨w, by simp [updatePanValueMap], hle⟩
              · rw [eval_baseAddr, hE.base] at hv
                simp only [Option.some.injEq] at hv
                subst hv
                by_cases hn : (name != "heap_ptr") = true
                · exact heapOk_update _ hn hH
                · have : name = "heap_ptr" := by simpa using hn
                  subst this
                  exact ⟨2701131776#64, by simp [updatePanValueMap], by decide, by decide⟩
              · cases hval
          · exact hH
        · exact hH
    | primitive name operator arguments =>
      have hx : (!G.contains name) = true := by simpa only [hk] using hs
      have hr := runs_primitive.mp (Runs.of_run hrun0)
      subst hr
      repeat' split
      all_goals first
        | exact ⟨hH, goodL_update _ hx hG⟩
        | exact hH
    | shMemLoad size kind name address =>
      cases kind with
      | «local» =>
        have hx : (!G.contains name) = true := by simpa only [hk] using hs
        have hgl : r.st.globals = s.globals := (globalsKeeper E).leaf _ _ s r n rfl hrun0
        rcases shMemLoad_local_inv hrun0 with herr | ⟨g, m, ffi, ev, rfl⟩ | ⟨w, ffi, rfl⟩
        · exact HPost.of_error herr hgl hH
        · have : g = s.globals := hgl
          subst this
          exact hH
        · exact ⟨hH, goodL_update _ hx hG⟩
      | global => simp [hk] at hs
    | extCall function configuration configurationLength array arrayLength =>
      have hGe : G = [] := by simpa [hk] using hs
      subst hGe
      exact HPost.of_globals ((globalsKeeper E).leaf _ _ s r n rfl hrun0) hH

/-- Every function declaration other than `alloc` and `heap_release` passes `hk`. -/
def hkAll (decls : List (Decl Word)) : Bool :=
  decls.all fun decl =>
    match decl with
    | .function d => d.name == "alloc" || d.name == "heap_release" || hk [] d.body
    | _ => true

theorem hkAll_guest : hkAll Guest.Software.guestAst = true := by decide +kernel

/-- Every guest function body other than `alloc` and `heap_release` is checked. -/
theorem guest_hk (hE : GuestEnv E) (f : FunName) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction f E.functions = some (parameters, body)) (hfa : f ≠ "alloc")
    (hfr : f ≠ "heap_release") : hk [] body = true := by
  obtain ⟨d, hmem, hname, hbody, -⟩ :=
    hE.functions f parameters body (lookupPanFunction_mem hlookup)
  have hall := hkAll_guest
  unfold hkAll at hall
  have hd := List.all_eq_true.mp hall _ hmem
  simp only [Bool.or_eq_true, beq_iff_eq] at hd
  rcases hd with (h | h) | h
  · exact absurd (hname ▸ h) hfa
  · exact absurd (hname ▸ h) hfr
  · rw [← hbody]
    exact h

/-- In the guest, a checked program keeps the heap pointer in the heap. -/
theorem heap_keep (hE : GuestEnv E) (fuel : Nat) (p : Prog Word) (G : List VarName) (s : St σ)
    (r : Result σ) (n : Nat) (hp : hk G p = true) (hs : HeapOk s.globals)
    (hG : GoodL G s.locals) (hrun : E.run fuel s p = some (r, n)) : HPost G r :=
  hk_sound hE (guest_hk hE) fuel p G s r n hp hs hG hrun

/-- Every guest function other than `heap_release` keeps the heap pointer in
the heap, whatever its arguments and outcome. -/
theorem fun_heap_keep (hE : GuestEnv E) {f : FunName} (hf : f ≠ "heap_release")
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction f E.functions = some (parameters, body)) (fuel : Nat)
    (s : St σ) (r : Result σ) (n : Nat) (hs : HeapOk s.globals)
    (hrun : E.run fuel s body = some (r, n)) : HeapOk r.st.globals := by
  by_cases hfa : f = "alloc"
  · subst hfa
    exact alloc_keeps hE parameters body hlookup s r hs (Runs.of_run hrun)
  · exact (heap_keep hE fuel body [] s r n (guest_hk hE f parameters body hlookup hfa hf) hs
      (fun _ h => by cases h) hrun).heapOk

end InitECandidate.Solver.GuestBound
