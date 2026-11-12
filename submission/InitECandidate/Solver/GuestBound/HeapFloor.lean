import InitECandidate.Solver.GuestBound.HeapKeep

/-!
# The heap pointer stays above a floor

Start-up allocates tables that later code relies on (`bn_gamma`, read by
`fq12_frob`). They stay allocated because, once `mem_init` has run,
`heap_ptr` only moves through `alloc`, which raises it, and through
`heap_release` of a local declared by `heap_mark()`. `hkf` checks that shape
as `hk` does, without the assignment of the base address and without calls of
`mem_init` and `main`; `hkf_sound` shows that checked programs keep
`heap_ptr` in the heap and not below any floor `F` it was above.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {F : Word}

/-- An aligned address in the heap, not below the floor `F`. -/
def InF (F w : Word) : Prop := InHeap w ∧ F.toNat ≤ w.toNat

/-- The heap pointer is an aligned word in the heap, not below `F`. -/
def FloorOk (F : Word) (g : VarName → Option (PanValue Word)) : Prop :=
  ∃ p : Word, g "heap_ptr" = some (.word p) ∧ InF F p

theorem FloorOk.heapOk {g : VarName → Option (PanValue Word)} (h : FloorOk F g) : HeapOk g := by
  obtain ⟨p, hp, hin, -⟩ := h
  exact ⟨p, hp, hin⟩

/-- Functions that may set `heap_ptr` back to the base: only start-up runs them. -/
def banned (f : FunName) : Bool := f == "mem_init" || f == "main"

set_option maxHeartbeats 2000000 in
/-- `alloc` leaves the globals alone unless it returns, and it returns only
for a word argument. -/
theorem alloc_globals_or (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "alloc" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (hs : HeapOk s.globals) (h : Runs E s body r) :
    r.st.globals = s.globals ∨
      ((∃ nv : Word, s.locals "n" = some (.word nv)) ∧ ∃ l g m f vs, r = .returned l g m f vs) := by
  have hbody := (fun_of_index 7 hE.functions (by guest_decl_at 7) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  obtain ⟨pv, hpv, hple⟩ := id hs
  rw [runs_dec] at h
  simp only [eval_global, hpv, shape_word, shape_matches_self, if_true] at h
  obtain ⟨r1, h1, rfl⟩ := h
  obtain ⟨ra, ha, hrest⟩ := runs_seq.mp h1
  have hga := trapIte_globals hE ha
  have hgd := trapIte_guard hE ha
  cases ra with
  | normal l g m f =>
    obtain ⟨rfl, rfl, rfl, rfl, hc1⟩ := hgd
    have hn : ∃ nv : Word, s.locals "n" = some (.word nv) := by
      rw [evalF_cmp hE.word] at hc1
      split at hc1
      · rename_i x y hx hy
        rw [evalF_local] at hy
        exact ⟨y, by simpa [updatePanValueMap] using hy⟩
      · cases hc1
    simp only at hrest
    rw [runs_dec] at hrest
    split at hrest
    · split at hrest
      · obtain ⟨r2, h2, rfl⟩ := hrest
        obtain ⟨rb, hb, hrest2⟩ := runs_seq.mp h2
        have hgb := trapIte_globals hE hb
        have hgd2 := trapIte_guard hE hb
        cases rb with
        | normal l g m f =>
          obtain ⟨rfl, rfl, rfl, rfl, hc0⟩ := hgd2
          simp only at hrest2
          obtain ⟨r3, h3, hrest3⟩ := runs_seq.mp hrest2
          rw [runs_assign_global] at h3
          split at h3
          · split at h3
            · subst h3
              simp only at hrest3
              rw [runs_return] at hrest3
              simp (config := { decide := true }) only [evalF_local, update_lookup, if_true,
                if_false, payload_word] at hrest3
              subst hrest3
              exact Or.inr ⟨hn, _, _, _, _, _, rfl⟩
            · subst h3
              simp only [St.err] at hrest3
              subst hrest3
              left; rfl
          · subst h3
            simp only [St.err] at hrest3
            subst hrest3
            left; rfl
        | error l g m f => simp only at hrest2; subst hrest2; left; exact hgb
        | raised l g m f e v => simp only at hrest2; subst hrest2; left; exact hgb
        | finalFfi l g m f e => simp only at hrest2; subst hrest2; left; exact hgb
        | _ => exact hgd2.elim
      · subst hrest
        left; rfl
    · subst hrest
      left; rfl
  | error l g m f => simp only at hrest; subst hrest; left; exact hga
  | raised l g m f e v => simp only at hrest; subst hrest; left; exact hga
  | finalFfi l g m f e => simp only at hrest; subst hrest; left; exact hga
  | _ => exact hgd.elim

/-- `alloc` keeps the heap pointer in the heap and does not lower it. -/
theorem alloc_keepsF (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "alloc" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (hs : FloorOk F s.globals) (h : Runs E s body r) :
    FloorOk F r.st.globals := by
  rcases alloc_globals_or hE parameters body hlookup s r hs.heapOk h with hg | ⟨⟨nv, hn⟩, hr⟩
  · rw [hg]
    exact hs
  · obtain ⟨l, g, m, f, vs, rfl⟩ := hr
    obtain ⟨pv, hpv, ⟨hple, hp8⟩, hF⟩ := hs
    obtain ⟨-, -, -, qv, rfl, hq, hqe, hq8⟩ :=
      alloc_runs hE parameters body hlookup s _ pv nv hn hpv hple h
    exact ⟨qv, by simp [PanValueFfiControlResult.st, updatePanValueMap], ⟨hqe, hq8⟩, by omega⟩


/-- The locals in `G` hold words not above the end of the heap. -/
def GoodF (F : Word) (G : List VarName) (l : VarName → Option (PanValue Word)) : Prop :=
  ∀ x, x ∈ G → ∃ w : Word, l x = some (.word w) ∧ InF F w

/-- The heap pointer is in the heap, and so are the good locals of results
that keep running. -/
def FPost (F : Word) (G : List VarName) : Result σ → Prop
  | .normal l g _ _ | .continued l g _ _ | .broke l g _ _ => FloorOk F g ∧ GoodF F G l
  | .error _ g _ _ | .returned _ g _ _ _ | .raised _ g _ _ _ _ | .finalFfi _ g _ _ _ => FloorOk F g

theorem FPost.floorOk {G : List VarName} {r : Result σ} (h : FPost F G r) : FloorOk F r.st.globals := by
  cases r <;> first | exact h.1 | exact h


/-- A plain statement keeps the invariant. -/
theorem plainLeaf_postF {G : List VarName} {fuel : Nat} {p : Prog Word} {s : St σ}
    {r : Result σ} {n : Nat} (hp : plainLeaf p = true) (hs : FloorOk F s.globals)
    (hG : GoodF F G s.locals) (hrun : E.run fuel s p = some (r, n)) : FPost F G r := by
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


/-- `p` only moves `heap_ptr` through `alloc`, through `heap_release` of a good
local, or by assigning a good local or the base address; `G` is the set of good locals. -/
def hkf : List VarName → Prog Word → Bool
  | G, .seq a b => hkf G a && hkf G b
  | G, .ite _ a b => hkf G a && hkf G b
  | G, .while _ b => hkf G b
  | G, .dec x _ _ b => hkf (G.filter (· != x)) b
  | G, .decCall x _ f _ b =>
      if f == "heap_mark" then hkf (x :: G) b
      else f != "heap_release" && !banned f && hkf (G.filter (· != x)) b
  | G, .assign .local x _ => !G.contains x
  | G, .assign .global x e =>
      x != "heap_ptr" || (match e with
        | .var .local q => G.contains q
        | _ => false)
  | G, .primitive x _ _ => !G.contains x
  | G, .shMemLoad _ .local x _ => !G.contains x
  | _, .shMemLoad _ .global _ _ => false
  | G, .extCall _ _ _ _ _ => G.isEmpty
  | _, .call none f _ => f != "heap_release" && !banned f
  | G, .call (some (dest, none)) f args => destOk G dest && (f != "heap_release" || relArg G args) && !banned f
  | G, .call (some (dest, some (_, hv, hp))) f _ =>
      destOk G dest && f != "heap_release" && !G.contains hv && hkf G hp && !banned f
  | _, p => plainLeaf p

theorem floorOk_update {g : VarName → Option (PanValue Word)} {x : VarName} (v : PanValue Word)
    (hx : (x != "heap_ptr") = true) (h : FloorOk F g) : FloorOk F (updatePanValueMap g x v) := by
  obtain ⟨p, hp, hle⟩ := h
  refine ⟨p, ?_, hle⟩
  have hne : ("heap_ptr" == x) = false := by
    rw [BEq.comm]
    simpa using hx
  simp only [updatePanValueMap, hne]
  exact hp

theorem goodF_update {G : List VarName} {l : VarName → Option (PanValue Word)} {x : VarName}
    (v : PanValue Word) (hx : (!G.contains x) = true) (h : GoodF F G l) :
    GoodF F G (updatePanValueMap l x v) := by
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
theorem assign_postF {G : List VarName} {structs : StructContext}
    {l g l' g' : VarName → Option (PanValue Word)} {dest : Option (VarKind × VarName)}
    {values : List (PanValue Word)} (hd : destOk G dest = true) (hg : FloorOk F g) (hl : GoodF F G l)
    (h : assignPanValueCallResult l g dest values (structs := structs) = some (l', g')) :
    FloorOk F g' ∧ GoodF F G l' := by
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
      exact ⟨hg, goodF_update _ hd hl⟩
    · cases h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨floorOk_update _ hd hg, hl⟩
    · cases h
  · cases h


set_option maxHeartbeats 1000000 in
/-- A call keeps the invariant when the callee body and the handler do. -/
theorem callSteps_hkf (G : List VarName) {f : FunName}
    {info : Option (Option (VarKind × VarName) × Option (ExceptionId × VarName × Prog Word))}
    (fuel : Nat) (s : St σ) (arguments : List (Exp Word)) (preserve : Bool) (rc : Result σ)
    (nc : Nat) (hs : FloorOk F s.globals) (hG : GoodF F G s.locals)
    (hdest : ∀ dest h, info = some (dest, h) → destOk G dest = true)
    (hcallee : ∀ values parameters body cl, E.evalArgs s arguments = some values →
      lookupPanFunction f E.functions = some (parameters, body) →
      bindPanValueParameters parameters values = some cl →
      ∀ rb nb, E.run (fuel - 1) ⟨cl, s.globals, s.memory, s.ffi⟩ body = some (rb, nb) →
        FloorOk F rb.st.globals)
    (hh : ∀ dest exc hv hp, info = some (dest, some (exc, hv, hp)) →
      ∀ v g m ffi r n, FloorOk F g →
        E.run (fuel - 1) ⟨updatePanValueMap s.locals hv v, g, m, ffi⟩ hp = some (r, n) →
        FPost F G r)
    (hrun : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
      E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi info f
      arguments (memoryAccess := E.memoryAccess) (contracts := E.contracts)
      (memoryHandler := E.memoryHandler) (preserveReturnLocals := preserve) = some (rc, nc)) :
    FPost F G rc ∧ (info = none → RetFrom E (fuel - 1) s f arguments rc) := by
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
          have hrb : FloorOk F rb.st.globals :=
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
                  exact ⟨assign_postF (hdest _ _ rfl) hrb hG hassign, fun h => by cases h⟩
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


/-- `heap_release(m)` with `m` within the heap keeps the heap pointer in the heap. -/
theorem heap_release_keepsF (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "heap_release" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (hs : FloorOk F s.globals)
    (hm : ∃ w : Word, s.locals "m" = some (.word w) ∧ InF F w)
    (h : Runs E s body r) : FloorOk F r.st.globals := by
  obtain ⟨pv, hp, -⟩ := hs
  obtain ⟨w, hw, hle⟩ := hm
  have := heap_release_runs hE parameters body hlookup s r pv w hp hw h
  subst this
  exact ⟨w, by simp [PanValueFfiControlResult.st, updatePanValueMap], hle⟩

theorem FPost.of_globals {s : St σ} {r : Result σ} (hg : r.st.globals = s.globals)
    (hH : FloorOk F s.globals) : FPost F [] r := by
  cases r <;> simp only [PanValueFfiControlResult.st] at hg <;> subst hg
  all_goals first
    | exact ⟨hH, fun _ h => by cases h⟩
    | exact hH

theorem FPost.of_error {G : List VarName} {s : St σ} {r : Result σ} (herr : r.isError = true)
    (hg : r.st.globals = s.globals) (hH : FloorOk F s.globals) : FPost F G r := by
  cases r <;> first
    | (simp only [PanValueFfiControlResult.st] at hg; subst hg; exact hH)
    | cases herr

/-- Good locals after binding `x`. -/
theorem goodF_bind {G G' : List VarName} {l : VarName → Option (PanValue Word)} {x : VarName}
    {v : PanValue Word} (h : GoodF F G l)
    (hx : x ∈ G' → ∃ w : Word, v = .word w ∧ InF F w)
    (hsub : ∀ y, y ∈ G' → y ≠ x → y ∈ G) : GoodF F G' (updatePanValueMap l x v) := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx
    obtain ⟨w, rfl, hle⟩ := hx hy
    exact ⟨w, by simp [updatePanValueMap], hle⟩
  · obtain ⟨w, hw, hle⟩ := h y (hsub y hy hyx)
    have hne : (y == x) = false := by simpa using hyx
    exact ⟨w, by simp only [updatePanValueMap, hne]; exact hw, hle⟩

/-- The invariant after the scope of a declaration of `x` ends. -/
theorem fpost_restore {G G' : List VarName} {x : VarName} {old : Option (PanValue Word)}
    {rb : Result σ} (hsub : ∀ y, y ∈ G → y ≠ x → y ∈ G')
    (hold : x ∈ G → ∃ w : Word, old = some (.word w) ∧ InF F w)
    (h : FPost F G' rb) : FPost F G (restorePanValueFfiLocal x old rb) := by
  have key : ∀ l : VarName → Option (PanValue Word), GoodF F G' l →
      GoodF F G (restorePanValueLocal l x old) := by
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

set_option maxHeartbeats 4000000 in
/-- Checked programs keep the heap pointer in the heap, provided every function
body other than `alloc` and `heap_release` is checked. -/
theorem hkf_sound (hE : GuestEnv E)
    (hfun : ∀ f parameters body, lookupPanFunction f E.functions = some (parameters, body) →
      f ≠ "alloc" → f ≠ "heap_release" → banned f = false → hkf [] body = true) :
    ∀ (fuel : Nat) (p : Prog Word) (G : List VarName) (s : St σ) (r : Result σ) (n : Nat),
      hkf G p = true → FloorOk F s.globals → GoodF F G s.locals → E.run fuel s p = some (r, n) →
      FPost F G r := by
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
        banned f = false →
        ∀ values parameters body cl, E.evalArgs s arguments = some values →
        lookupPanFunction f E.functions = some (parameters, body) →
        bindPanValueParameters parameters values = some cl →
        ∀ rb nb, E.run (fuel - 1) ⟨cl, s.globals, s.memory, s.ffi⟩ body = some (rb, nb) →
          FloorOk F rb.st.globals := by
      intro f arguments hf hbf values parameters body cl _ hlookup _ rb nb hrunb
      by_cases hfa : f = "alloc"
      · subst hfa
        exact alloc_keepsF hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb hH
          (Runs.of_run hrunb)
      · exact (sih (fuel - 1) (by omega) body [] ⟨cl, s.globals, s.memory, s.ffi⟩ rb nb
          (hfun f parameters body hlookup hfa hf hbf) hH (fun _ h => by cases h) hrunb).floorOk
    cases p with
    | seq first second =>
      simp only [hkf, Bool.and_eq_true] at hs
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
      simp only [hkf, Bool.and_eq_true] at hs
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
      simp only [hkf] at hs
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
            (goodF_bind hG (fun h => absurd rfl (mem_filter_ne.mp h).2)
              (fun y hy _ => (mem_filter_ne.mp hy).1)) hb
          exact fpost_restore (fun y hy hne => mem_filter_ne.mpr ⟨hy, hne⟩) (fun h => hG name h) pb
    | «while» condition body =>
      have hsb : hkf G body = true := by simpa only [hkf] using hs
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
            have again : ∀ l g m f, FloorOk F g → GoodF F G l → (do
                  let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                    E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord
                    fuel l g m f (.while condition body) (memoryAccess := E.memoryAccess)
                    (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                  pure (loopResult, k + nb + loopSteps + 1)) = some (r, n) →
                FPost F G r := by
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
          simp only [hkf, Bool.and_eq_true] at hs
          have hf : f ≠ "heap_release" := by simpa using hs.1
          have hbf : banned f = false := by simpa using hs.2
          exact (callSteps_hkf G fuel s arguments false _ nc hH hG (fun _ _ h => by cases h)
            (hcal f arguments hf hbf) (fun _ _ _ _ h => by cases h) hcall).1
        | some pair =>
          obtain ⟨dest, handler⟩ := pair
          cases handler with
          | none =>
            simp only [hkf, Bool.and_eq_true, Bool.or_eq_true] at hs
            obtain ⟨⟨hd, hfr⟩, hbf⟩ := hs
            have hbf : banned f = false := by simpa using hbf
            refine (callSteps_hkf G fuel s arguments false _ nc hH hG
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
                exact heap_release_keepsF hE parameters body hlookup
                  ⟨cl, s.globals, s.memory, s.ffi⟩ rb hH
                  ⟨w, by rw [← hbind]; simp [updatePanValueMap], hle⟩ (Runs.of_run hrunb)
              · cases hra
            · exact hcal f arguments hf hbf
          | some triple =>
            obtain ⟨exc, hv, hp⟩ := triple
            simp only [hkf, Bool.and_eq_true] at hs
            obtain ⟨⟨⟨⟨hd, hf⟩, hhv⟩, hhp⟩, hbf⟩ := hs
            refine (callSteps_hkf G fuel s arguments false _ nc hH hG
              (fun d h heq => by cases heq; exact hd)
              (hcal f arguments (by simpa using hf) (by simpa using hbf)) ?_
              hcall).1
            intro d e v' p' heq v g m ffi r n hg hrunh
            cases heq
            exact sih (fuel - 1) (by omega) _ G _ r n hhp hg (goodF_update v hhv hG) hrunh
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
            simp only [hkf, hm', Bool.false_eq_true, if_false, Bool.and_eq_true] at hs
            simpa using hs.1.1
        have hbf : banned f = false := by
          by_cases hm : f = "heap_mark"
          · rw [hm]; decide
          · have hm' : (f == "heap_mark") = false := by simpa using hm
            simp only [hkf, hm', Bool.false_eq_true, if_false, Bool.and_eq_true] at hs
            simpa using hs.1.2
        obtain ⟨hrc, hret⟩ := callSteps_hkf G fuel s arguments true rc nc hH hG
          (fun _ _ h => by cases h) (hcal f arguments hfr hbf) (fun _ _ _ _ h => by cases h) hcall
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
              have hg : FloorOk F g := hrc
              by_cases hm : f = "heap_mark"
              · subst hm
                have hsb : hkf (name :: G) body = true := by simpa [hkf] using hs
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
                  (goodF_bind hG (fun _ => ⟨pv, rfl, hple⟩)
                    (fun y hy hne => (List.mem_cons.mp hy).resolve_left hne)) hb
                exact fpost_restore (fun y hy _ => List.mem_cons_of_mem _ hy)
                  (fun h => hG name h) pb
              · have hm' : (f == "heap_mark") = false := by simpa using hm
                simp only [hkf, hm', Bool.false_eq_true, if_false, Bool.and_eq_true] at hs
                have pb := ih body (G.filter (· != name))
                  ⟨updatePanValueMap s.locals name value, g, m, ffi⟩ rb nb hs.2 hg
                  (goodF_bind hG (fun h => absurd rfl (mem_filter_ne.mp h).2)
                    (fun y hy _ => (mem_filter_ne.mp hy).1)) hb
                exact fpost_restore (fun y hy hne => mem_filter_ne.mpr ⟨hy, hne⟩)
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
    | skip => exact plainLeaf_postF rfl hH hG hrun0
    | tick => exact plainLeaf_postF rfl hH hG hrun0
    | annot key text => exact plainLeaf_postF rfl hH hG hrun0
    | «break» => exact plainLeaf_postF rfl hH hG hrun0
    | «continue» => exact plainLeaf_postF rfl hH hG hrun0
    | «return» value => exact plainLeaf_postF rfl hH hG hrun0
    | raise exception value => exact plainLeaf_postF rfl hH hG hrun0
    | store address value => exact plainLeaf_postF rfl hH hG hrun0
    | store32 address value => exact plainLeaf_postF rfl hH hG hrun0
    | storeByte address value => exact plainLeaf_postF rfl hH hG hrun0
    | shMemStore size address value => exact plainLeaf_postF rfl hH hG hrun0
    | assign kind name value =>
      cases kind with
      | «local» =>
        have hx : (!G.contains name) = true := by simpa only [hkf] using hs
        have hgl : r.st.globals = s.globals := (globalsKeeper E).leaf _ _ s r n rfl hrun0
        rcases assign_local_inv hrun0 with herr | ⟨v, -, rfl⟩
        · exact FPost.of_error herr hgl hH
        · exact ⟨hH, goodF_update v hx hG⟩
      | global =>
        have hr := runs_assign_global.mp (Runs.of_run hrun0)
        subst hr
        split
        · rename_i v hv
          split
          · show FloorOk F (updatePanValueMap s.globals name v) ∧ GoodF F G s.locals
            refine ⟨?_, hG⟩
            simp only [hkf, Bool.or_eq_true] at hs
            rcases hs with hne | hval
            · exact floorOk_update v hne hH
            · split at hval
              · rename_i q
                obtain ⟨w, hw, hle⟩ := hG q (by simpa using hval)
                rw [evalF_local, hw] at hv
                simp only [Option.some.injEq] at hv
                subst hv
                by_cases hn : (name != "heap_ptr") = true
                · exact floorOk_update _ hn hH
                · have : name = "heap_ptr" := by simpa using hn
                  subst this
                  exact ⟨w, by simp [updatePanValueMap], hle⟩
              · cases hval
          · exact hH
        · exact hH
    | primitive name operator arguments =>
      have hx : (!G.contains name) = true := by simpa only [hkf] using hs
      have hr := runs_primitive.mp (Runs.of_run hrun0)
      subst hr
      repeat' split
      all_goals first
        | exact ⟨hH, goodF_update _ hx hG⟩
        | exact hH
    | shMemLoad size kind name address =>
      cases kind with
      | «local» =>
        have hx : (!G.contains name) = true := by simpa only [hkf] using hs
        have hgl : r.st.globals = s.globals := (globalsKeeper E).leaf _ _ s r n rfl hrun0
        rcases shMemLoad_local_inv hrun0 with herr | ⟨g, m, ffi, ev, rfl⟩ | ⟨w, ffi, rfl⟩
        · exact FPost.of_error herr hgl hH
        · have : g = s.globals := hgl
          subst this
          exact hH
        · exact ⟨hH, goodF_update _ hx hG⟩
      | global => simp [hkf] at hs
    | extCall function configuration configurationLength array arrayLength =>
      have hGe : G = [] := by simpa [hkf] using hs
      subst hGe
      exact FPost.of_globals ((globalsKeeper E).leaf _ _ s r n rfl hrun0) hH

/-- Every function declaration other than `alloc` and `heap_release` passes `hkf`. -/
def hkfAll (decls : List (Decl Word)) : Bool :=
  decls.all fun decl =>
    match decl with
    | .function d => d.name == "alloc" || d.name == "heap_release" || banned d.name || hkf [] d.body
    | _ => true

theorem hkfAll_guest : hkfAll Guest.Software.guestAst = true := by decide +kernel

/-- Every guest function body other than `alloc` and `heap_release` is checked. -/
theorem guest_hkf (hE : GuestEnv E) (f : FunName) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction f E.functions = some (parameters, body)) (hfa : f ≠ "alloc")
    (hfr : f ≠ "heap_release") (hbf : banned f = false) : hkf [] body = true := by
  obtain ⟨d, hmem, hname, hbody, -⟩ :=
    hE.functions f parameters body (lookupPanFunction_mem hlookup)
  have hall := hkfAll_guest
  unfold hkfAll at hall
  have hd := List.all_eq_true.mp hall _ hmem
  simp only [Bool.or_eq_true, beq_iff_eq] at hd
  rcases hd with ((h | h) | h) | h
  · exact absurd (hname ▸ h) hfa
  · exact absurd (hname ▸ h) hfr
  · rw [hname, hbf] at h
    cases h
  · rw [← hbody]
    exact h

/-- In the guest, a checked program keeps the heap pointer in the heap. -/
theorem floor_keep (hE : GuestEnv E) (fuel : Nat) (p : Prog Word) (G : List VarName) (s : St σ)
    (r : Result σ) (n : Nat) (hp : hkf G p = true) (hs : FloorOk F s.globals)
    (hG : GoodF F G s.locals) (hrun : E.run fuel s p = some (r, n)) : FPost F G r :=
  hkf_sound hE (guest_hkf hE) fuel p G s r n hp hs hG hrun

/-- Every guest function other than `heap_release` keeps the heap pointer in
the heap, whatever its arguments and outcome. -/
theorem fun_floor_keep (hE : GuestEnv E) {f : FunName} (hf : f ≠ "heap_release")
    (hbf : banned f = false)
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction f E.functions = some (parameters, body)) (fuel : Nat)
    (s : St σ) (r : Result σ) (n : Nat) (hs : FloorOk F s.globals)
    (hrun : E.run fuel s body = some (r, n)) : FloorOk F r.st.globals := by
  by_cases hfa : f = "alloc"
  · subst hfa
    exact alloc_keepsF hE parameters body hlookup s r hs (Runs.of_run hrun)
  · exact (floor_keep hE fuel body [] s r n (guest_hkf hE f parameters body hlookup hfa hf hbf) hs
      (fun _ h => by cases h) hrun).floorOk

end InitECandidate.Solver.GuestBound