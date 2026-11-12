import InitECandidate.Solver.GuestBound.Fq12Inv
import InitECandidate.Solver.GuestBound.U256Zero
import InitECandidate.Solver.GuestBound.FqAdd

/-!
# Scalar field helpers keep values below `p`

`fq_neg` and `fq_mul_small` return canonical values on canonical arguments.
They are read-only, so nothing else changes. First steps of the canonicity
chain needed by `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- A tail call: the callee's result is the result. -/
theorem WPs.tail_ret {f : FunName} {args : List (Exp Word)}
    (h : ∀ vs g m ffi, CalleeRet E s f args vs g m ffi → ∀ l, Q (.returned l g m ffi vs)) :
    WPs E s (.call none f args) Q := by
  intro r hr
  rcases runs_call_inv none hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    · exact Or.inr (h vs g m ffi ⟨parameters, body, values, cl, lr, hlookup, hvalues, hbind,
        hcallee⟩ l)
  | raised lr g m f ex v =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m f ev =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inl trivial
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl (Stopped.of_error hout)

/-- A declaring call of a word. -/
theorem WPs.decCall_word {x : VarName} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word}
    (h : ∀ w g m ffi, CalleeRet E s f args [.word w] g m ffi →
      WPs E ⟨updatePanValueMap s.locals x (.word w), g, m, ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one f args body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  cases rb with
  | returned lr g m ffi vs =>
    cases vs with
    | nil => exact hout.elim
    | cons v rest =>
      cases rest with
      | cons v' rest' => exact hout.elim
      | nil =>
        obtain ⟨r', hshape, hrun', rfl⟩ := hout
        obtain ⟨w, rfl⟩ := word_of_shape_one hshape
        rcases h w g m ffi ⟨parameters, cbody, values, cl, lr, hlookup, hvalues, hbind,
          hcallee⟩ r' hrun' with hs | hq
        · exact Or.inl hs.restore
        · exact Or.inr hq
  | raised lr g m ffi ex v =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m ffi ev =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | _ => exact hout.elim

/-- Return of a four-word value. -/
theorem WPs.ret4 {e : Exp Word} {w0 w1 w2 w3 : Word}
    (he : E.eval s e = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (h : Q (.returned (fun _ => none) s.globals s.memory s.ffi
      [.rStruct [.word w0, .word w1, .word w2, .word w3]])) : WPs E s (.return e) Q := by
  intro r hr
  rw [runs_return, he] at hr
  simp only [payload_words4, if_true] at hr
  subst hr
  exact Or.inr h

theorem limbs4_zero {a0 a1 a2 a3 : Word} (h : limbsVal [a0, a1, a2, a3] = 0) :
    a0 = 0 ∧ a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by
  simp only [limbsVal] at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply BitVec.eq_of_toNat_eq <;>
    simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod] <;> omega

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem iszero_ret (hE : GuestEnv E) {e : Exp Word} {a0 a1 a2 a3 : Word}
    (h : CalleeRet E s "u256_is_zero" [e] vs g m ffi)
    (h1 : E.eval s e = some (.rStruct [.word a0, .word a1, .word a2, .word a3])) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧
      ((limbsVal [a0, a1, a2, a3] = 0 ∧ vs = [.word 1]) ∨
        (limbsVal [a0, a1, a2, a3] ≠ 0 ∧ vs = [.word 0#64])) := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 42 hE.functions (by guest_decl_at 42) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  by_cases hz : limbsVal [a0, a1, a2, a3] = 0
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := limbs4_zero hz
    have := u256_is_zero_zero hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hrun
    cases this
    exact ⟨rfl, rfl, rfl, Or.inl ⟨hz, rfl⟩⟩
  · have := u256_is_zero_nz hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
      a0 a1 a2 a3 (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      hz hrun
    cases this
    exact ⟨rfl, rfl, rfl, Or.inr ⟨hz, rfl⟩⟩

theorem u256sub_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : CalleeRet E s "u256_sub" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (h2 : E.eval s e2 = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hle : limbsVal [b0, b1, b2, b3] ≤ limbsVal [a0, a1, a2, a3]) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ d0 d1 d2 d3 : Word,
      vs = [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] = limbsVal [a0, a1, a2, a3] - limbsVal [b0, b1, b2, b3] := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 57 hE.functions (by guest_decl_at 57) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  obtain ⟨l', d0, d1, d2, d3, heq, hd⟩ := u256_sub_spec hE parameters body hlookup
    ⟨cl, s.globals, s.memory, s.ffi⟩ _ a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hle hrun
  cases heq
  exact ⟨rfl, rfl, rfl, d0, d1, d2, d3, rfl, hd⟩

theorem fqadd_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : CalleeRet E s "fq_add" [e1, e2] vs g m ffi)
    (h1 : E.eval s e1 = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (h2 : E.eval s e2 = some (.rStruct [.word b0, .word b1, .word b2, .word b3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (hB : limbsVal [b0, b1, b2, b3] < bnP) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ d0 d1 d2 d3 : Word,
      vs = [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] =
        (limbsVal [a0, a1, a2, a3] + limbsVal [b0, b1, b2, b3]) % bnP := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 649 hE.functions (by guest_decl_at 649) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq_add_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hA hB hrun with
    hst | ⟨l', d0, d1, d2, d3, heq, hd⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, d0, d1, d2, d3, rfl, hd⟩

end rets

/-- What a read-only field function returns: a value below `p`, nothing changed. -/
def CanonRet (s : St σ) (r : Result σ) : Prop :=
  ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
    [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧ limbsVal [d0, d1, d2, d3] < bnP

set_option maxHeartbeats 4000000 in
theorem fq_neg_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq_neg" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (h : Runs E s body r) :
    Stopped r ∨ CanonRet s r := by
  have hbody := (fun_of_index 651 hE.functions (by guest_decl_at 651) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (CanonRet s)) r h
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, hz⟩ := iszero_ret hE hret (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3)
    (by lk [ha])
  subst g m ffi
  rcases hz with ⟨hz, hv⟩ | ⟨hz, hv⟩
  · simp only [List.cons.injEq, and_true] at hv
    subst v
    refine WPs.seqG (fun _ => False) (WPs.ite (w := evalPanCmp .equal (1 : Word) 1#64)
      (eval_cmp_inv hE (of_eval (w := (1 : Word)) (by lk [])) (of_eval (eval_const _ _))) ?_)
      (fun _ hf => hf.elim)
    rw [if_neg (by decide)]
    refine WPs.ret4 (w0 := 0#64) (w1 := 0#64) (w2 := 0#64) (w3 := 0#64)
      (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, 0#64, 0#64, 0#64, 0#64, rfl, by decide⟩
  · simp only [List.cons.injEq, and_true] at hv
    subst v
    refine WPs.seqG (fun st => st = ⟨updatePanValueMap s.locals "z" (.word 0#64), s.globals,
        s.memory, s.ffi⟩) (WPs.ite (w := evalPanCmp .equal (0#64 : Word) 1#64)
      (eval_cmp_inv hE (of_eval (w := 0#64) (by lk [])) (of_eval (eval_const _ _))) ?_) ?_
    · rw [if_pos (by decide)]
      exact WPs.skip rfl
    · rintro _ rfl
      refine WPs.tail_ret (fun vs g m ffi hret l => ?_)
      obtain ⟨hg, hm, hf, d0, d1, d2, d3, hv, hd⟩ := u256sub_ret hE hret
        (a0 := 4332616871279656263#64) (a1 := 10917124144477883021#64)
        (a2 := 13281191951274694749#64) (a3 := 3486998266802970665#64)
        (b0 := a0) (b1 := a1) (b2 := a2) (b3 := a3)
        (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) (by lk [ha])
        (by rw [bnP_limbs]; omega)
      subst g m ffi vs
      simp only [restorePanValueFfiLocal]
      have hpl := bnP_limbs
      exact ⟨_, d0, d1, d2, d3, rfl, by rw [hd, hpl]; omega⟩

theorem bit_length64_quiet :
    keepFn quietLeaf Guest.Software.guestAst 1 "bit_length64" = true := by
  decide +kernel

/-- A declaration with a known value. -/
theorem WPs.dec_val {x : VarName} {sh : Shape} {e : Exp Word} {body : Prog Word}
    {v : PanValue Word} (he : E.eval s e = some v)
    (h : WPs E ⟨updatePanValueMap s.locals x v, s.globals, s.memory, s.ffi⟩ body
      (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.dec x sh e body) Q := by
  intro r hr
  rw [runs_dec, he] at hr
  simp only at hr
  split at hr
  · obtain ⟨rb, hrb, rfl⟩ := hr
    rcases h rb hrb with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq
  · subst hr
    exact Or.inl (Stopped.err s)

/-- Invariant of the doubling loop of `fq_mul_small`. -/
def SmallI (s : St σ) (a0 a1 a2 a3 : Word) (st : St σ) : Prop :=
  st.globals = s.globals ∧ st.memory = s.memory ∧ st.ffi = s.ffi ∧
    st.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]) ∧
    (∃ iw : Word, st.locals "i" = some (.word iw)) ∧
    ∃ r0 r1 r2 r3 : Word, st.locals "r" = some (.rStruct [.word r0, .word r1, .word r2, .word r3]) ∧
      limbsVal [r0, r1, r2, r3] < bnP

set_option maxHeartbeats 4000000 in
theorem fq_mul_small_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq_mul_small" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hA : limbsVal [a0, a1, a2, a3] < bnP) (h : Runs E s body r) :
    Stopped r ∨ CanonRet s r := by
  have hbody := (fun_of_index 656 hE.functions (by guest_decl_at 656) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpp : 0 < bnP := by decide
  refine (?_ : WPs E s _ (CanonRet s)) r h
  refine WPs.dec_val (v := .rStruct [.word 0#64, .word 0#64, .word 0#64, .word 0#64])
    (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) ?_
  refine WPs.decCall_word (fun iw g m ffi hret => ?_)
  obtain ⟨hg, hm, hf⟩ := hret.quiet
    (keepFn_sound (quietKeeper E) hE.functions 1 "bit_length64" bit_length64_quiet)
  subst g m ffi
  refine WPs.seqG (SmallI s a0 a1 a2 a3) (WPs.loopG (I := SmallI s a0 a1 a2 a3)
    ⟨rfl, rfl, rfl, by lk [ha], ⟨iw, by lk []⟩, 0#64, 0#64, 0#64, 0#64, by lk [], by decide⟩
    ?_ (fun a k hI _ => hI)) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, hla, ⟨i0, hi⟩, r0, r1, r2, r3, hr, hrl⟩ -
    simp only at hg hm hf hla hi hr
    subst hg hm hf
    refine WPs.seq_assign (old := i0) (w := i0 - 1#64) hi (of_eval (by ev [hi])) ?_
    refine WPs.seq (fun st => st.globals = s.globals ∧ st.memory = s.memory ∧ st.ffi = s.ffi ∧
        (∀ x, x ≠ "r" → st.locals x = updatePanValueMap la "i" (.word (i0 - 1#64)) x) ∧
        ∃ d0 d1 d2 d3 : Word, st.locals "r" = some (.rStruct [.word d0, .word d1, .word d2,
          .word d3]) ∧ limbsVal [d0, d1, d2, d3] < bnP)
      (WPs.callA_ret (fun v g m ffi hret => ?_)) ?_
    · obtain ⟨hg, hm, hf, d0, d1, d2, d3, hv, hd⟩ := fqadd_ret hE hret (a0 := r0) (a1 := r1)
        (a2 := r2) (a3 := r3) (b0 := r0) (b1 := r1) (b2 := r2) (b3 := r3) (by lk [hr])
        (by lk [hr]) hrl hrl
      simp only [List.cons.injEq, and_true] at hv
      subst g m ffi v
      refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, fun x hx => by
        simp only [update_lookup]
        rw [if_neg (by simpa using hx)], d0, d1, d2, d3, by lk [], ?_⟩
      rw [hd]
      exact Nat.mod_lt _ hpp
    · rintro ⟨l2, g2, m2, f2⟩ ⟨hg, hm, hf, hl2, d0, d1, d2, d3, hr2, hd⟩
      simp only at hg hm hf hl2 hr2
      subst hg hm hf
      have hla2 : l2 "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]) := by
        rw [hl2 _ (by decide)]
        lk [hla]
      have hi2 : l2 "i" = some (.word (i0 - 1#64)) := by
        rw [hl2 _ (by decide)]
        lk []
      refine WPs.ite_both (fun w _ => ?_)
      split
      · exact WPs.skip ⟨rfl, rfl, rfl, hla2, ⟨_, hi2⟩, d0, d1, d2, d3, hr2, hd⟩
      · refine WPs.callA_ret (fun v g m ffi hret => ?_)
        obtain ⟨hg, hm, hf, e0, e1, e2, e3, hv, he⟩ := fqadd_ret hE hret (a0 := d0) (a1 := d1)
          (a2 := d2) (a3 := d3) (b0 := a0) (b1 := a1) (b2 := a2) (b3 := a3) (by lk [hr2])
          (by lk [hla2]) hd hA
        simp only [List.cons.injEq, and_true] at hv
        subst g m ffi v
        exact ⟨rfl, rfl, rfl, by lk [hla2], ⟨i0 - 1#64, by lk [hi2]⟩, e0, e1, e2, e3, by lk [],
          by rw [he]; exact Nat.mod_lt _ hpp⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, hla, -, r0, r1, r2, r3, hr, hrl⟩
    simp only at hg hm hf hr
    subst hg hm hf
    refine WPs.ret4 (w0 := r0) (w1 := r1) (w2 := r2) (w3 := r3) (by lk [hr]) ?_
    simp only [restorePanValueFfiLocal]
    exact ⟨_, r0, r1, r2, r3, rfl, hrl⟩

end InitECandidate.Solver.GuestBound
