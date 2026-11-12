import InitECandidate.Solver.GuestBound.Manual.Taylor

/-!
# Function specifications and the bump allocator

`FunSpec E f P B Q`: every body registered for `f`, run from a state
satisfying `P`, takes at most `B` steps and ends in a result related to the
entry state by `Q`. `FunCost` is the case without conditions. The first
specification with real content is `alloc`: it returns the old `heap_ptr`
and advances it, aligned, by at least the requested size, within the heap.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A step bound with a precondition on the callee's entry state and a
postcondition relating entry state and result. -/
def FunSpec (E : Env σ) (f : FunName) (P : St σ → Prop) (B : Nat)
    (Q : St σ → Result σ → Prop) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ fuel s r n, P s → E.run fuel s body = some (r, n) → r.isError = false → n ≤ B ∧ Q s r

theorem FunSpec.of_cost {f : FunName} {B : Nat} (h : FunCost E f B) :
    FunSpec E f (fun _ => True) B (fun _ _ => True) :=
  fun parameters body hlookup fuel s r n _ hrun hne =>
    ⟨(h parameters body hlookup fuel s r n trivial hrun hne).1, trivial⟩

/-- A cost bound and a run-level fact give a specification. -/
theorem FunSpec.of_runs {f : FunName} {B : Nat} {P : St σ → Prop} {Q : St σ → Result σ → Prop}
    (h : FunCost E f B)
    (hq : ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
      ∀ s r, P s → Runs E s body r → Q s r) : FunSpec E f P B Q :=
  fun parameters body hlookup fuel s r n hP hrun hne =>
    ⟨(h parameters body hlookup fuel s r n trivial hrun hne).1,
      hq parameters body hlookup s r hP (Runs.of_run hrun)⟩

theorem runs_assign_global {s : St σ} {x : VarName} {e : Exp Word} {r : Result σ} :
    Runs E s (.assign .global x e) r ↔
      r = match E.eval s e with
        | some v =>
            if panValueAssignmentValid E.structs s.locals s.globals .global x v then
              .normal s.locals (updatePanValueMap s.globals x v) s.memory s.ffi
            else s.err
        | none => s.err := by
  have hrun : ∀ fuel, (E.run (fuel + 1) s (.assign .global x e)).map Prod.fst = some
      (match E.eval s e with
        | some v =>
            if panValueAssignmentValid E.structs s.locals s.globals .global x v then
              .normal s.locals (updatePanValueMap s.globals x v) s.memory s.ffi
            else s.err
        | none => s.err) := by
    intro fuel
    simp only [Env.run]
    rw [evalPanValueFfiProgSteps]
    simp only [panValueAssignGlobalResult, evalPanValueExpCounted, Env.eval, St.err]
    cases evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
        E.bytesInWord e E.memoryAccess with
    | none => simp
    | some v =>
      simp only [Option.map_some]
      split <;> simp
  constructor
  · rintro ⟨fuel, n, h⟩
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
    | succ fuel =>
      have := hrun fuel
      rw [h] at this
      simp only [Option.map_some, Option.some.injEq] at this
      exact this
  · rintro rfl
    exact runs_of_map (hrun 0)

/-- `if c { trap_with(…); }` ends normally only with `c` false and the state unchanged. -/
theorem trapIte_guard (hE : GuestEnv E) {c : Exp Word} {arguments : List (Exp Word)} {s : St σ}
    {r : Result σ} :
    Runs E s (.ite c (.call (some (none, none)) "trap_with" arguments) .skip) r →
    match r with
    | .normal l g m f => l = s.locals ∧ g = s.globals ∧ m = s.memory ∧ f = s.ffi ∧
        E.eval s c = some (.word 0)
    | .continued _ _ _ _ | .broke _ _ _ _ | .returned _ _ _ _ _ => False
    | _ => True := by
  intro h
  rw [runs_ite] at h
  split at h
  · rename_i v heq
    split at h
    · rename_i hv
      rw [runs_skip] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl, by rw [heq, hv]⟩
    · obtain ⟨fuel, n, hrun⟩ := h
      have hnr := call_noReturn (trap_with_noReturn hE) (some none) hrun
      cases r with
      | normal l g m f => cases hnr.2
      | continued l g m f => cases hnr.1
      | broke l g m f => cases hnr.1
      | returned l g m f vs => cases hnr.1
      | _ => trivial
  · subst h
    simp [St.err]

theorem lower_zero {a b : Word} (h : evalPanCmp .lower a b = 0) : ¬ a < b := by
  intro hab
  simp [evalPanCmp, hab] at h

/-- Clearing the low three bits, in the form the evaluator produces for `x & (0 - 8)`. -/
theorem and_m8 (x : BitVec 64) :
    (AndOp.and x (AndOp.and (0#64 - 8#64) (~~~(0 : BitVec 64)))).toNat = x.toNat / 8 * 8 := by
  have h : (x &&& ((0#64 - 8#64) &&& ~~~(0 : BitVec 64))) = (x >>> (3 : Nat)) <<< (3 : Nat) := by
    bv_decide
  show (x &&& ((0#64 - 8#64) &&& ~~~(0 : BitVec 64))).toNat = _
  rw [h, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- What a returning `alloc` did: the old `heap_ptr` is returned and the new
one is aligned, past the block, and inside the heap; nothing else changed. -/
def AllocPost (pv nv : Word) (s : St σ) : Result σ → Prop
  | .returned _ g m f vs =>
      vs = [.word pv] ∧ m = s.memory ∧ f = s.ffi ∧
        ∃ qv : Word, g = updatePanValueMap s.globals "heap_ptr" (.word qv) ∧
          pv.toNat + nv.toNat ≤ qv.toNat ∧ qv.toNat ≤ 2952790016 ∧ qv.toNat % 8 = 0
  | .normal _ _ _ _ | .continued _ _ _ _ | .broke _ _ _ _ => False
  | _ => True

set_option maxHeartbeats 2000000 in
theorem alloc_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "alloc" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv nv : Word) (hn : s.locals "n" = some (.word nv))
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : pv.toNat ≤ 2952790016)
    (h : Runs E s body r) : AllocPost pv nv s r := by
  have hbody := (fun_of_index 7 hE.functions (by guest_decl_at 7) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  rw [runs_dec] at h
  simp only [eval_global, hp, shape_word, shape_matches_self, if_true] at h
  obtain ⟨rb, hb, rfl⟩ := h
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp hb
  have ft := trapIte_guard hE h₁
  cases r₁ with
  | normal l1 g1 m1 f1 =>
    obtain ⟨rfl, rfl, rfl, rfl, hg1⟩ := ft
    simp only at hrest
    simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_op hE.word,
      evalArgs_cons, evalArgs_nil, evalF_local, eval_const, update_lookup, if_true, if_false, hn,
      wordsProj_cons, wordsProj_nil, wordOp, Option.map_some, Option.some.injEq,
      PanValue.word.injEq] at hg1
    rw [runs_dec] at hrest
    simp (config := { decide := true }) only [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
      evalF_local, eval_const, update_lookup, if_true, if_false, hn, wordsProj_cons,
      wordsProj_nil, wordOp, List.foldr, Option.map_some, shape_word, shape_matches_self]
      at hrest
    obtain ⟨rb2, hb2, rfl⟩ := hrest
    obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hb2
    have ft2 := trapIte_guard hE h₂
    cases r₂ with
    | normal l2 g2 m2 f2 =>
      obtain ⟨rfl, rfl, rfl, rfl, hg2⟩ := ft2
      simp only at hrest₂
      simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, eval_const,
        update_lookup, if_true, Option.some.injEq, PanValue.word.injEq] at hg2
      obtain ⟨r₃, h₃, hrest₃⟩ := runs_seq.mp hrest₂
      rw [runs_assign_global] at h₃
      simp (config := { decide := true }) only [evalF_local, update_lookup, if_true,
        panValueAssignmentValid, hp, shape_word, shape_matches_self] at h₃
      subst h₃
      simp only at hrest₃
      rw [runs_return] at hrest₃
      simp (config := { decide := true }) only [evalF_local, update_lookup, if_true, if_false,
        payload_word] at hrest₃
      subst hrest₃
      simp only [restorePanValueFfiLocal, AllocPost]
      refine ⟨trivial, trivial, trivial, _, rfl, ?_⟩
      have hq := and_m8 (pv + (nv + (7#64 + 0)))
      have h1 := lower_zero hg1
      have h2 := lower_zero hg2
      have hpl := pv.isLt
      have hnl := nv.isLt
      have hH : (2952790016#64).toNat = 2952790016 := by decide
      have h7 : (7#64).toNat = 7 := by decide
      have hsub : (2952790016#64 - pv).toNat = 2952790016 - pv.toNat := by
        rw [BitVec.toNat_sub, hH]
        omega
      rw [BitVec.lt_def, hsub] at h1
      have hsum : (pv + (nv + (7#64 + 0))).toNat = pv.toNat + nv.toNat + 7 := by
        have h70 : (7#64 + (0 : Word)) = 7#64 := by decide
        rw [h70, BitVec.toNat_add, BitVec.toNat_add, h7]
        omega
      rw [BitVec.lt_def, hq, hH, hsum] at h2
      rw [hq, hsum]
      omega
    | continued l2 g2 m2 f2 => exact ft2.elim
    | broke l2 g2 m2 f2 => exact ft2.elim
    | returned l2 g2 m2 f2 vs => exact ft2.elim
    | _ =>
      simp only at hrest₂
      subst hrest₂
      simp only [restorePanValueFfiLocal, AllocPost]
  | continued l1 g1 m1 f1 => exact ft.elim
  | broke l1 g1 m1 f1 => exact ft.elim
  | returned l1 g1 m1 f1 vs => exact ft.elim
  | _ =>
    simp only at hrest
    subst hrest
    simp only [restorePanValueFfiLocal, AllocPost]

/-- An aligned address not above the end of the heap. -/
def InHeap (w : Word) : Prop := w.toNat ≤ 2952790016 ∧ w.toNat % 8 = 0

/-- The heap pointer is an aligned word inside the heap. -/
def HeapOk (g : VarName → Option (PanValue Word)) : Prop :=
  ∃ p : Word, g "heap_ptr" = some (.word p) ∧ InHeap p

/-- A returning `alloc` keeps the heap pointer inside the heap. -/
theorem AllocPost.heapOk {pv nv : Word} {s : St σ} {l g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {f : FfiState σ} {vs : List (PanValue Word)}
    (h : AllocPost pv nv s (.returned l g m f vs)) : HeapOk g := by
  obtain ⟨-, -, -, qv, rfl, -, hq, hq8⟩ := h
  exact ⟨qv, by simp [updatePanValueMap], hq, hq8⟩

/-- `heap_mark` returns the heap pointer and changes nothing. -/
theorem heap_mark_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "heap_mark" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv : Word) (hp : s.globals "heap_ptr" = some (.word pv))
    (h : Runs E s body r) :
    r = .returned (fun _ => none) s.globals s.memory s.ffi [.word pv] := by
  have hbody := (fun_of_index 8 hE.functions (by guest_decl_at 8) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp only [runs_return, eval_global, hp, payload_word, if_true] at h
  exact h

/-- `heap_release(m)` sets the heap pointer to `m` and changes nothing else. -/
theorem heap_release_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "heap_release" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv mv : Word) (hp : s.globals "heap_ptr" = some (.word pv))
    (hm : s.locals "m" = some (.word mv)) (h : Runs E s body r) :
    r = .returned (fun _ => none) (updatePanValueMap s.globals "heap_ptr" (.word mv)) s.memory
      s.ffi [.word 0] := by
  have hbody := (fun_of_index 9 hE.functions (by guest_decl_at 9) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  simp only [runs_seq, runs_assign_global, runs_return, evalF_local, eval_const, hm,
    panValueAssignmentValid, hp, shape_word, shape_matches_self, payload_word, if_true,
    exists_eq_left] at h
  exact h

/-- The run ended without a value for the enclosing block: `.error`, an
exception, or a final FFI event. -/
def Stopped : Result σ → Prop
  | .error _ _ _ _ | .raised _ _ _ _ _ _ | .finalFfi _ _ _ _ _ => True
  | _ => False

theorem Stopped.of_error {r : Result σ} (h : r.isError = true) : Stopped r := by
  cases r <;> first | trivial | cases h

/-- `var x = alloc(e); body`: the run stopped, or `body` ran with `x` bound to
the old heap pointer and the heap pointer advanced past the block. -/
theorem decCall_alloc (hE : GuestEnv E) {x : VarName} {e : Exp Word} {body : Prog Word}
    {s : St σ} {r : Result σ} {pv nv : Word} (he : E.eval s e = some (.word nv))
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : pv.toNat ≤ 2952790016)
    (h : Runs E s (.decCall x .one "alloc" [e] body) r) :
    Stopped r ∨ ∃ (qv : Word) (r' : Result σ),
      pv.toNat + nv.toNat ≤ qv.toNat ∧ qv.toNat ≤ 2952790016 ∧ qv.toNat % 8 = 0 ∧
      Runs E ⟨updatePanValueMap s.locals x (.word pv),
        updatePanValueMap s.globals "heap_ptr" (.word qv), s.memory, s.ffi⟩ body r' ∧
      r = restorePanValueFfiLocal x (s.locals x) r' := by
  rcases runs_decCall_inv h with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 7 hE.functions (by guest_decl_at 7) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, he, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := alloc_runs hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb pv nv
    (by rw [← hbind]; simp [updatePanValueMap]) hp hpH hcallee
  cases rb with
  | returned lr g m f vs =>
    obtain ⟨rfl, rfl, rfl, qv, rfl, h1, h2, h3⟩ := hpost
    obtain ⟨r', -, hrun', rfl⟩ := hout
    exact Or.inr ⟨qv, r', h1, h2, h3, hrun', rfl⟩
  | raised lr g m f ex v =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m f ev =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | _ => exact hout.elim

/-- A store of a word at a word address: `.error`, or exactly that cell is rewritten. -/
theorem runs_store_word (hE : GuestEnv E) {a v : Exp Word} {s : St σ} {r : Result σ}
    {addr w : Word} (ha : E.eval s a = some (.word addr)) (hv : E.eval s v = some (.word w))
    (h : Runs E s (.store a v) r) :
    r.isError = true ∨ r = .normal s.locals s.globals (setCell s.memory addr w) s.ffi := by
  obtain ⟨fuel, n, hrun⟩ := h
  rcases store_word_inv hE.mem hrun with herr | ⟨addr', val, m, ha', hv', rfl, hm⟩
  · exact Or.inl herr
  rw [ha] at ha'
  rw [hv] at hv'
  simp only [Option.some.injEq, PanValue.word.injEq] at ha' hv'
  subst ha' hv'
  rw [hm w rfl]
  exact Or.inr rfl

end InitECandidate.Solver.GuestBound
