import InitECandidate.Solver.GuestBound.HtabFind

/-!
# `memeq` on one pointer

When `a` and `b` hold the same value, every comparison in `memeq` reads the
same cell twice, so no `return 0` is taken: the function returns 1 if it
returns at all, and changes nothing.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Locals `a` and `b` agree; globals, memory and FFI state are the given ones. -/
def SameAB (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (s : St σ) : Prop :=
  s.locals "a" = s.locals "b" ∧ s.globals = g ∧ s.memory = m ∧ s.ffi = f

/-- Outcome of a piece of `memeq`: still comparing, failed, or returned 1. -/
def SelfPost (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) : Result σ → Prop
  | .normal l g' m' f' | .continued l g' m' f' | .broke l g' m' f' => SameAB g m f ⟨l, g', m', f'⟩
  | .returned _ g' m' f' vs => g' = g ∧ m' = m ∧ f' = f ∧ vs = [.word 1#64]
  | _ => True

/-- Every run of `p` from a state with `a = b` ends in `SelfPost`. -/
def SelfOne (E : Env σ) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (f : FfiState σ) (p : Prog Word) : Prop :=
  ∀ s r, SameAB g m f s → Runs E s p r → SelfPost g m f r

variable {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
  {f : FfiState σ}

theorem eval_load_congr {s : St σ} {sh : Shape} {e1 e2 : Exp Word}
    (h : E.eval s e1 = E.eval s e2) : E.eval s (.load sh e1) = E.eval s (.load sh e2) := by
  simp only [Env.eval] at h ⊢
  rw [evalPanValueExp, evalPanValueExp, h]

theorem eval_loadByte_congr {s : St σ} {e1 e2 : Exp Word}
    (h : E.eval s e1 = E.eval s e2) : E.eval s (.loadByte e1) = E.eval s (.loadByte e2) := by
  simp only [Env.eval] at h ⊢
  rw [evalPanValueExp, evalPanValueExp, h]

theorem eval_add_ab (hE : GuestEnv E) {s : St σ} (h : s.locals "a" = s.locals "b")
    (rest : List (Exp Word)) :
    E.eval s (.op .add (.var .local "a" :: rest)) =
      E.eval s (.op .add (.var .local "b" :: rest)) := by
  simp only [evalF_op hE.word, evalArgs_cons, evalF_local, h]

theorem eval_var_ab {s : St σ} (h : s.locals "a" = s.locals "b") :
    E.eval s (.var .local "a") = E.eval s (.var .local "b") := by
  simp only [evalF_local, h]

theorem SelfOne.skip : SelfOne E g m f .skip := by
  intro s r hs h
  rw [runs_skip] at h
  subst h
  exact hs

theorem SelfOne.seq {p q : Prog Word} (hp : SelfOne E g m f p) (hq : SelfOne E g m f q) :
    SelfOne E g m f (.seq p q) := by
  intro s r hs h
  obtain ⟨r1, h1, hrest⟩ := runs_seq.mp h
  have hp1 := hp s r1 hs h1
  cases r1 with
  | normal l g' m' f' => exact hq _ r hp1 hrest
  | _ => simp only at hrest; subst hrest; exact hp1

theorem SelfOne.ite {c : Exp Word} {p q : Prog Word} (hp : SelfOne E g m f p)
    (hq : SelfOne E g m f q) : SelfOne E g m f (.ite c p q) := by
  intro s r hs h
  rw [runs_ite] at h
  split at h
  · split at h
    · exact hq s r hs h
    · exact hp s r hs h
  · subst h
    trivial

/-- `if e1 != e2 { return 0; }` where both sides read the same thing. -/
theorem SelfOne.guard (hE : GuestEnv E) {e1 e2 : Exp Word}
    (heq : ∀ s : St σ, s.locals "a" = s.locals "b" → E.eval s e1 = E.eval s e2) :
    SelfOne E g m f (.ite (.cmp .notEqual e1 e2) (.return (.const 0#64)) .skip) := by
  intro s r hs h
  rw [runs_ite, evalF_cmp hE.word, heq s hs.1] at h
  cases he : E.eval s e2 with
  | none => rw [he] at h; simp only at h; subst h; trivial
  | some x =>
    rw [he] at h
    cases x with
    | word w =>
      simp [evalPanCmp] at h
      rw [runs_skip] at h
      subst h
      exact hs
    | _ => simp only at h; subst h; trivial

theorem SelfOne.ret_one : SelfOne E g m f (.return (.const 1#64)) := by
  intro s r hs h
  rw [runs_return] at h
  simp only [eval_const, payload_word, if_true] at h
  subst h
  exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2, rfl⟩

theorem SelfOne.assign {x : VarName} {e : Exp Word} (hxa : (x == "a") = false)
    (hxb : (x == "b") = false) : SelfOne E g m f (.assign .local x e) := by
  intro s r hs h
  rw [runs_assign_local] at h
  subst h
  split
  · split
    · have ha : ("a" == x) = false := by rw [BEq.comm]; exact hxa
      have hb : ("b" == x) = false := by rw [BEq.comm]; exact hxb
      refine ⟨?_, hs.2⟩
      show updatePanValueMap s.locals x _ "a" = updatePanValueMap s.locals x _ "b"
      simp only [update_lookup, ha, hb]
      exact hs.1
    · trivial
  · trivial

theorem SelfOne.dec {x : VarName} {sh : Shape} {e : Exp Word} {p : Prog Word}
    (hxa : (x == "a") = false) (hxb : (x == "b") = false) (hp : SelfOne E g m f p) :
    SelfOne E g m f (.dec x sh e p) := by
  intro s r hs h
  rw [runs_dec] at h
  have ha : ("a" == x) = false := by rw [BEq.comm]; exact hxa
  have hb : ("b" == x) = false := by rw [BEq.comm]; exact hxb
  cases he : E.eval s e with
  | none => rw [he] at h; simp only at h; subst h; trivial
  | some v =>
    rw [he] at h
    simp only at h
    split at h
    · obtain ⟨rb, hrb, rfl⟩ := h
      have hin : SameAB g m f ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ := by
        refine ⟨?_, hs.2⟩
        show updatePanValueMap s.locals x _ "a" = updatePanValueMap s.locals x _ "b"
        simp only [update_lookup, ha, hb]
        exact hs.1
      have hpost := hp _ rb hin hrb
      cases rb with
      | normal l g' m' f' =>
        refine ⟨?_, hpost.2⟩
        show restorePanValueLocal l x _ "a" = restorePanValueLocal l x _ "b"
        simp only [restorePanValueLocal, ha, hb]
        exact hpost.1
      | continued l g' m' f' =>
        refine ⟨?_, hpost.2⟩
        show restorePanValueLocal l x _ "a" = restorePanValueLocal l x _ "b"
        simp only [restorePanValueLocal, ha, hb]
        exact hpost.1
      | broke l g' m' f' =>
        refine ⟨?_, hpost.2⟩
        show restorePanValueLocal l x _ "a" = restorePanValueLocal l x _ "b"
        simp only [restorePanValueLocal, ha, hb]
        exact hpost.1
      | returned l g' m' f' vs => exact hpost
      | _ => trivial
    · subst h; trivial

theorem SelfOne.while {c : Exp Word} {p : Prog Word} (hp : SelfOne E g m f p) :
    SelfOne E g m f (.while c p) := by
  intro s r hs h
  obtain ⟨fuel, n, hrun⟩ := h
  refine while_inv (I := SameAB g m f) (Q := SelfPost g m f) ?_ ?_ ?_ fuel s r n hs hrun
  · intro r hr
    cases r <;> first | trivial | cases hr
  · intro s' _ hs' _
    exact hs'
  · intro fuel' s' r' n' hs' _ hrun'
    have := hp s' r' hs' (Runs.of_run hrun')
    cases r' <;> exact this

-- Build a `SelfOne` derivation for a piece of `memeq`.
set_option hygiene false in
macro "self_one" : tactic => `(tactic|
  repeat' first
    | exact SelfOne.skip
    | exact SelfOne.ret_one
    | exact SelfOne.guard hE (fun s h => eval_load_congr (eval_var_ab h))
    | exact SelfOne.guard hE (fun s h => eval_load_congr (eval_add_ab hE h _))
    | exact SelfOne.guard hE (fun s h => eval_loadByte_congr (eval_var_ab h))
    | exact SelfOne.guard hE (fun s h => eval_loadByte_congr (eval_add_ab hE h _))
    | exact SelfOne.assign rfl rfl
    | apply SelfOne.seq
    | apply SelfOne.ite
    | apply SelfOne.while
    | apply SelfOne.dec rfl rfl)

set_option maxHeartbeats 2000000 in
/-- `memeq(p, p, n)`: if it returns, it returns 1 and has changed nothing. -/
theorem memeq_self (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "memeq" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (hab : s.locals "a" = s.locals "b") (h : Runs E s body r) :
    SelfPost s.globals s.memory s.ffi r := by
  have hbody := (fun_of_index 18 hE.functions (by guest_decl_at 18) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : SelfOne E s.globals s.memory s.ffi _) s r ⟨hab, rfl, rfl, rfl⟩ h
  self_one

end InitECandidate.Solver.GuestBound
