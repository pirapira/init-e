import InitECandidate.Solver.GuestBound.CompactNibbles

/-!
# `rlp_item` and `rlp_decode_fully`: frame

On return both have changed only free scratch memory (through
`rlp_list_count` on list items), all globals are as before, and the result is
a struct of four words.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem isw_const (w : Word) : ∀ y, E.eval s (.const w) = some y → ∃ w' : Word, y = .word w' := by
  intro y hy
  rw [eval_const] at hy
  exact ⟨w, (Option.some.inj hy).symm⟩

theorem isw_local {x : VarName} {w : Word} (h : s.locals x = some (.word w)) :
    ∀ y, E.eval s (.var .local x) = some y → ∃ w' : Word, y = .word w' := by
  intro y hy
  rw [evalF_local, h] at hy
  exact ⟨w, (Option.some.inj hy).symm⟩

/-- An operator application evaluates to a word, if at all. -/
theorem isw_op (hE : GuestEnv E) {o : BinOp} {es : List (Exp Word)} :
    ∀ y, E.eval s (.op o es) = some y → ∃ w' : Word, y = .word w' := by
  intro y hy
  rw [evalF_op hE.word] at hy
  split at hy
  · split at hy
    · simp only [Option.map_eq_some_iff] at hy
      obtain ⟨w, -, rfl⟩ := hy
      exact ⟨w, rfl⟩
    · cases hy
  · cases hy

/-- `if c { f(…); }` followed by `q`, when `f` changes nothing if it returns. -/
theorem WPs.guard_quiet {c : Exp Word} {f : FunName} {args : List (Exp Word)} {q : Prog Word}
    (hq : FunKeeps (quietKeeper E) f) (h : WPs E s q Q) :
    WPs E s (.seq (.ite c (.call (some (none, none)) f args) .skip) q) Q := by
  refine WPs.seq (fun a => a = s) (WPs.ite_both (fun w _ => ?_)) (fun a ha => ha ▸ h)
  split
  · exact WPs.skip ⟨_, _, _, _, rfl, rfl⟩
  · refine WPs.call_ret (fun vs g m ffi hret => ?_)
    obtain ⟨hg, hm, hf⟩ := CalleeRet.quiet hq hret
    subst g m ffi
    exact ⟨_, _, _, _, rfl, rfl⟩

/-- `if c₁ { if c₂ { f(…); } }` followed by `q`. -/
theorem WPs.guard2_quiet {c₁ c₂ : Exp Word} {f : FunName} {args : List (Exp Word)}
    {q : Prog Word} (hq : FunKeeps (quietKeeper E) f) (h : WPs E s q Q) :
    WPs E s (.seq (.ite c₁ (.ite c₂ (.call (some (none, none)) f args) .skip) .skip) q) Q := by
  refine WPs.seq (fun a => a = s) (WPs.ite_both (fun w _ => ?_)) (fun a ha => ha ▸ h)
  split
  · exact WPs.skip ⟨_, _, _, _, rfl, rfl⟩
  · refine WPs.ite_both (fun w2 _ => ?_)
    split
    · exact WPs.skip ⟨_, _, _, _, rfl, rfl⟩
    · refine WPs.call_ret (fun vs g m ffi hret => ?_)
      obtain ⟨hg, hm, hf⟩ := CalleeRet.quiet hq hret
      subst g m ffi
      exact ⟨_, _, _, _, rfl, rfl⟩

/-- Returning a struct of four word-valued expressions. -/
theorem WPs.ret_struct4 {e1 e2 e3 e4 : Exp Word}
    (h1 : ∀ y, E.eval s e1 = some y → ∃ w : Word, y = .word w)
    (h2 : ∀ y, E.eval s e2 = some y → ∃ w : Word, y = .word w)
    (h3 : ∀ y, E.eval s e3 = some y → ∃ w : Word, y = .word w)
    (h4 : ∀ y, E.eval s e4 = some y → ∃ w : Word, y = .word w)
    (h : ∀ a b c d : Word, Q (.returned (fun _ => none) s.globals s.memory s.ffi
      [.rStruct [.word a, .word b, .word c, .word d]])) :
    WPs E s (.return (.rStruct [e1, e2, e3, e4])) Q := by
  refine WPs.ret_ev (fun v hv => ?_)
  rw [evalF_rStruct] at hv
  simp only [evalArgs_cons, evalArgs_nil] at hv
  cases k1 : E.eval s e1 with
  | none => rw [k1] at hv; simp at hv
  | some y1 =>
    cases k2 : E.eval s e2 with
    | none => rw [k1, k2] at hv; simp at hv
    | some y2 =>
      cases k3 : E.eval s e3 with
      | none => rw [k1, k2, k3] at hv; simp at hv
      | some y3 =>
        cases k4 : E.eval s e4 with
        | none => rw [k1, k2, k3, k4] at hv; simp at hv
        | some y4 =>
          obtain ⟨a, rfl⟩ := h1 _ k1
          obtain ⟨b, rfl⟩ := h2 _ k2
          obtain ⟨c, rfl⟩ := h3 _ k3
          obtain ⟨d, rfl⟩ := h4 _ k4
          rw [k1, k2, k3, k4] at hv
          simp at hv
          subst hv
          exact h a b c d

theorem rlp_fail_quiet (hE : GuestEnv E) : FunKeeps (quietKeeper E) "rlp_fail" :=
  keepFn_sound (quietKeeper E) hE.functions 1 "rlp_fail"
    (show keepFn quietLeaf Guest.Software.guestAst 1 "rlp_fail" = true by decide +kernel)

theorem rlp_read_length_quiet (hE : GuestEnv E) : FunKeeps (quietKeeper E) "rlp_read_length" :=
  keepFn_sound (quietKeeper E) hE.functions 2 "rlp_read_length"
    (show keepFn quietLeaf Guest.Software.guestAst 2 "rlp_read_length" = true by decide +kernel)

/-- A returned struct of four words, with only free scratch memory changed. -/
def Item4 (pv fv : Word) (s : St σ) (r : Result σ) : Prop :=
  ∃ l m a b c d, r = .returned l s.globals m s.ffi
    [.rStruct [.word a, .word b, .word c, .word d]] ∧ ScrMem pv fv s.memory m

theorem Item4.restore {pv fv : Word} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : Item4 pv fv s r) : Item4 pv fv s (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, m, a, b, c, d, rfl, hk⟩ := h
  exact ⟨_, m, a, b, c, d, rfl, hk⟩

set_option maxHeartbeats 16000000 in
/-- On return, `rlp_item` has changed only free scratch memory and returns four words. -/
theorem rlp_item_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_item" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw : Word) (hpw : s.locals "p" = some (.word pw))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (h : Runs E s body r) : Stopped r ∨ Item4 pv fv s r := by
  have hbody := (fun_of_index 107 hE.functions (by guest_decl_at 107) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (Item4 pv fv s)) r h
  have hfq := rlp_fail_quiet hE
  have hrq := rlp_read_length_quiet hE
  have ret0 : ∀ (l : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word)),
      ScrMem pv fv s.memory m → ∀ a b c d : Word, Item4 pv fv s
        (.returned l s.globals m s.ffi [.rStruct [.word a, .word b, .word c, .word d]]) :=
    fun l m hk a b c d => ⟨_, m, a, b, c, d, rfl, hk⟩
  refine WPs.guard_quiet hfq ?_
  refine WPs.dec_ev (fun vb _ => WPs.conseq (Q' := Item4 pv fv s) ?_ (fun r h => h.restore))
  try dsimp only
  -- a single byte below 128
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "b" vb, s.globals, s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · exact WPs.ret_struct4 (isw_const _) (isw_local (w := pw) (by lk [hpw])) (isw_const _) (isw_const _)
        (ret0 _ _ (ScrMem.refl _ _ _))
  intro a ha
  rw [ha]
  clear ha a
  -- short string
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "b" vb, s.globals, s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.dec_ev (fun vn hvn => WPs.conseq (Q' := Item4 pv fv s) ?_ (fun r h => by
        obtain ⟨l, m, a, b, c, d, rfl, hk⟩ := h
        exact ⟨_, m, a, b, c, d, rfl, hk⟩))
      obtain ⟨nn, rfl⟩ := isw_op hE _ hvn
      refine WPs.guard_quiet hfq ?_
      refine WPs.guard2_quiet hfq ?_
      exact WPs.ret_struct4 (isw_const _) (isw_op hE) (isw_local (w := nn) (by lk [])) (isw_op hE)
        (ret0 _ _ (ScrMem.refl _ _ _))
  intro a ha
  rw [ha]
  clear ha a
  -- long string
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "b" vb, s.globals, s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.dec_ev (fun vl hvl => WPs.conseq (Q' := Item4 pv fv s) ?_ (fun r h => by
        obtain ⟨l, m, a, b, c, d, rfl, hk⟩ := h
        exact ⟨_, m, a, b, c, d, rfl, hk⟩))
      obtain ⟨llw, rfl⟩ := isw_op hE _ hvl
      refine WPs.guard_quiet hfq ?_
      refine WPs.decCall_word (fun nn g m ffi hret =>
        WPs.conseq (Q' := Item4 pv fv s) ?_ (fun r h => h.restore))
      obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet hrq hret
      subst g m ffi
      refine WPs.guard_quiet hfq ?_
      refine WPs.guard_quiet hfq ?_
      exact WPs.ret_struct4 (isw_const _) (isw_op hE) (isw_local (w := nn) (by lk [])) (isw_op hE)
        (ret0 _ _ (ScrMem.refl _ _ _))
  intro a ha
  rw [ha]
  clear ha a
  -- short list
  refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "b" vb, s.globals, s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.dec_ev (fun vn hvn => WPs.conseq (Q' := Item4 pv fv s) ?_ (fun r h => by
        obtain ⟨l, m, a, b, c, d, rfl, hk⟩ := h
        exact ⟨_, m, a, b, c, d, rfl, hk⟩))
      obtain ⟨nn, rfl⟩ := isw_op hE _ hvn
      refine WPs.guard_quiet hfq ?_
      refine WPs.seq_call_ret (fun vs g m ffi hret => ?_)
      obtain ⟨hg, hf', hk, -⟩ := rlplistcount_ret hE hret (pw0 := pw + 1#64) (lenv := nn)
        (by ev [hpw]) (by lk []) hp hf hfp
      subst g ffi
      exact WPs.ret_struct4 (isw_const _) (isw_op hE) (isw_local (w := nn) (by lk [])) (isw_op hE)
        (ret0 _ _ hk)
  intro a ha
  rw [ha]
  clear ha a
  -- long list
  refine WPs.dec_ev (fun vl hvl => WPs.conseq (Q' := Item4 pv fv s) ?_ (fun r h => h.restore))
  obtain ⟨llw, rfl⟩ := isw_op hE _ hvl
  refine WPs.guard_quiet hfq ?_
  refine WPs.decCall_word (fun nn g m ffi hret =>
    WPs.conseq (Q' := Item4 pv fv s) ?_ (fun r h => h.restore))
  obtain ⟨hg, hm, hf'⟩ := CalleeRet.quiet hrq hret
  subst g m ffi
  refine WPs.guard_quiet hfq ?_
  refine WPs.guard_quiet hfq ?_
  refine WPs.seq_call_ret (fun vs g m ffi hret => ?_)
  obtain ⟨hg, hf', hk, -⟩ := rlplistcount_ret hE hret (pw0 := pw + (1#64 + llw)) (lenv := nn)
    (by ev [hpw]) (by lk []) hp hf hfp
  subst g ffi
  exact WPs.ret_struct4 (isw_const _) (isw_op hE) (isw_local (w := nn) (by lk [])) (isw_op hE)
    (ret0 _ _ hk)

end InitECandidate.Solver.GuestBound
