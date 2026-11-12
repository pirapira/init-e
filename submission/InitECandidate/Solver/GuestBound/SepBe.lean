import InitECandidate.Solver.GuestBound.RfInstanceM
import InitECandidate.Solver.GuestBound.KeyNibbles

/-!
# Big-endian writers into an owned range

`st_be32(p, v)` writes four bytes at `p`. A byte store changes the word cell
that contains the byte, so writing inside an owned range keeps the range (its
contents are unknown anyway).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `stb a, v; rest` when the word cell of the byte lies in an owned range. -/
theorem WPr.seq_storeByte_range (hE : GuestEnv E) {a v : Exp Word} {q : Prog Word}
    {addr lo hi : Word} {F : Assn} (hpre : (Assn.Range lo hi ⋆ F).holds s)
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hlo : lo.toNat ≤ addr.toNat / 8 * 8) (hhi : addr.toNat / 8 * 8 < hi.toNat)
    (hq : ∀ m, (Assn.Range lo hi ⋆ F).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.storeByte a v) q) Q := by
  refine WPr.seq (fun s' => ∃ m, s' = ⟨s.locals, s.globals, m, s.ffi⟩ ∧
    (Assn.Range lo hi ⋆ F).holds s') ?_ (by rintro _ ⟨m, rfl, hm⟩; exact hq m hm)
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  rcases storeByte_inv' hE.mem hrun with herr | ⟨addr', val, cell, ha', -, -, rfl, -⟩
  · exact Or.inl herr
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  rw [hE.bytes]
  have hal : (al8 addr').toNat = addr'.toNat / 8 * 8 := align8_toNat addr'
  refine Or.inr ⟨_, rfl, Assn.holds_range_change hpre rfl (fun x hx => ?_)⟩
  exact setCell_ne _ (by
    intro hh
    have := congrArg BitVec.toNat hh
    rw [hal] at this
    omega)

/-- `x = f(args); rest` for a word-valued local `x` and a callee that changes
nothing and never raises. -/
theorem WPr.seq_callA_quiet {f : FunName} {args : List (Exp Word)} {x : VarName} {q : Prog Word}
    {o : Word} (hx : s.locals x = some (.word o)) (hq : FunKeeps (quietKeeper E) f)
    (hr : FunRaises E (fun _ => false) f) (htrap : ∀ r, Trap r → Q r)
    (hk : ∀ w : Word, WPr E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩
      q Q) :
    WPr E s (.seq (.call (some (some (.local, x), none)) f args) q) Q := by
  refine WPr.seq (fun s' => ∃ w : Word, s' = ⟨updatePanValueMap s.locals x (.word w), s.globals,
    s.memory, s.ffi⟩) ?_ (by rintro _ ⟨w, rfl⟩; exact hk w)
  intro r hr'
  rcases runs_call_inv (some (some (.local, x))) hr' with herr | ⟨parameters, body, values, cl,
    rb, hlookup, hvalues, hbind, hcallee, hout⟩
  · exact Or.inl herr
  have hra := hr parameters body hlookup _ rb hcallee
  obtain ⟨fuel, n, hrun⟩ := hcallee
  have hkeep := hq parameters body hlookup fuel ⟨cl, s.globals, s.memory, s.ffi⟩ rb n hrun
  cases rb with
  | returned lr g m ffi vs =>
    simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl herr
    · obtain ⟨hg, hm, hf⟩ := hkeep
      dsimp only [PanValueFfiControlResult.st] at hg hm hf
      subst hg hm hf
      cases vs with
      | nil => simp [assignPanValueCallResult] at hassign
      | cons v tl =>
        cases tl with
        | cons _ _ => simp [assignPanValueCallResult] at hassign
        | nil =>
          simp only [assignPanValueCallResult] at hassign
          split at hassign
          · rename_i hval
            simp only [Option.some.injEq, Prod.mk.injEq] at hassign
            obtain ⟨rfl, rfl⟩ := hassign
            simp only [panValueAssignmentValid, hx, shape_word] at hval
            obtain ⟨w, rfl⟩ := word_of_shape_one hval
            exact Or.inr ⟨w, rfl⟩
          · cases hassign
  | raised lr g m ffi ex v =>
    rcases hra with he | hx'
    · cases he
    · cases hx'
  | finalFfi lr g m ffi ev =>
    simp only [CallOutcome] at hout
    subst hout
    exact Or.inr (htrap _ trivial)
  | _ =>
    simp only [CallOutcome] at hout
    exact Or.inl hout

/-- `st_be32(p, v)` inside an owned range. -/
theorem st_be32_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "st_be32" E.functions = some (parameters, body))
    (s : St σ) (p lo hi : Word) (hp : s.locals "p" = some (.word p))
    (hl8 : lo.toNat % 8 = 0) (hlo : lo.toNat ≤ p.toNat) (hhi : p.toNat + 4 ≤ hi.toNat)
    (hb : hi.toNat ≤ 2 ^ 62) :
    WPFt E s body (Assn.Range lo hi)
      (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ Assn.Range lo hi) := by
  have hbody := (fun_of_index 27 hE.functions (by guest_decl_at 27) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  dsimp only
  have h1 : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
  have h2 : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
  have h3 : (p + 3#64).toNat = p.toNat + 3 := by bv_omega
  refine WPr.seq_storeByte_range hE hR (addr := p) (of_eval (by lk [hp])) (by omega) (by omega)
    (fun m1 hm1 => ?_)
  refine WPr.seq_storeByte_range hE hm1 (addr := p + 1#64) (of_eval (by ev [hp])) (by omega)
    (by omega) (fun m2 hm2 => ?_)
  refine WPr.seq_storeByte_range hE hm2 (addr := p + 2#64) (of_eval (by ev [hp])) (by omega)
    (by omega) (fun m3 hm3 => ?_)
  refine WPr.seq_storeByte_range hE hm3 (addr := p + 3#64) (of_eval (by ev [hp])) (by omega)
    (by omega) (fun m4 hm4 => ?_)
  exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
    (Or.inr (Assn.holds_pure_intro ⟨_, _, _, rfl⟩ (Assn.holds_congr rfl rfl hm4)))

/-- `st_be32(e1, e2)` at a call site where the first argument evaluates to `p`. -/
theorem st_be32_hc (hE : GuestEnv E) {args : List (Exp Word)} {p : Word} {v : PanValue Word}
    (hargs : E.evalArgs s args = some [.word p, v]) (lo hi : Word)
    (hl8 : lo.toNat % 8 = 0) (hlo : lo.toNat ≤ p.toNat) (hhi : p.toNat + 4 ≤ hi.toNat)
    (hb : hi.toNat ≤ 2 ^ 62) :
    ∀ parameters cbody values cl,
      lookupPanFunction "st_be32" E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (Assn.Range lo hi)
        (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ Assn.Range lo hi) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 27 hE.functions (by guest_decl_at 27) (by decide +kernel)
    hlk).2
  rw [hargs] at hvalues
  cases hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact st_be32_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ p lo hi
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hl8 hlo hhi hb

theorem bswap64_quiet (hE : GuestEnv E) : FunKeeps (quietKeeper E) "bswap64" :=
  keepFn_sound (quietKeeper E) hE.functions 2 "bswap64"
    (show keepFn quietLeaf Guest.Software.guestAst 2 "bswap64" = true by decide +kernel)

theorem bswap64_raises (hE : GuestEnv E) : FunRaises E (fun _ => false) "bswap64" :=
  raiseFn_sound _ hE.functions 2 "bswap64"
    (show raiseFn (fun _ => false) Guest.Software.guestAst 2 "bswap64" = true by decide +kernel)

set_option maxHeartbeats 1000000 in
/-- `st_be64(p, v)` inside an owned range. -/
theorem st_be64_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "st_be64" E.functions = some (parameters, body))
    (s : St σ) (p v lo hi : Word) (hp : s.locals "p" = some (.word p))
    (hv : s.locals "v" = some (.word v))
    (hl8 : lo.toNat % 8 = 0) (hlo : lo.toNat ≤ p.toNat) (hhi : p.toNat + 8 ≤ hi.toNat)
    (hb : hi.toNat ≤ 2 ^ 62) :
    WPFt E s body (Assn.Range lo hi)
      (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ Assn.Range lo hi) := by
  have hbody := (fun_of_index 28 hE.functions (by guest_decl_at 28) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  dsimp only
  refine WPr.seq_ite_skip ?_ ?_
  · -- aligned: one word store
    refine WPr.decCall_quiet (bswap64_quiet hE) (bswap64_raises hE)
      (fun r hr => by cases r <;> first | exact hr.elim | exact Or.inl hr) (fun vw hsh => ?_)
    obtain ⟨w, rfl⟩ := word_of_shape_one hsh
    have hR' := Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "w" (.word w), s.globals,
      s.memory, s.ffi⟩ : St σ)) rfl rfl hR
    refine WPr.seq_store_at hE hR' (addr := p) (w := w) (of_eval (by lk [hp]))
      (of_eval (by lk [])) (Step.range hlo (by omega)) (fun m hm => ?_)
    refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact Or.inr (Assn.holds_pure_intro ⟨_, _, _, rfl⟩ (Assn.holds_congr rfl rfl hm))
  · -- two halves
    have h4 : (p + 4#64).toNat = p.toNat + 4 := by bv_omega
    refine WPr.seq_call_framedT hR (st_be32_hc hE (p := p) (v := .word (v >>> 32))
      (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        evalF_shift hE.word, eval_const, RiscV.panRiscVShift, hp, hv]) lo hi hl8 hlo (by omega) hb)
      (fun r ht => Or.inl ht) ?_ ?_
    rotate_left
    · intro l g m ffi exc v' _ h
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    intro l g m ffi vs h
    obtain ⟨⟨_, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    refine WPr.seq_call_framedT hk (st_be32_hc hE (p := p + 4#64) (v := .word v)
      (by ev [hp, hv]) lo hi hl8 (by omega) (by omega) hb) (fun r ht => Or.inl ht) ?_ ?_
    rotate_left
    · intro l2 g2 m2 ffi2 exc v' _ h
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    intro l2 g2 m2 ffi2 vs2 h
    obtain ⟨⟨_, _, _, hC⟩, hk2⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
      (Or.inr (Assn.holds_pure_intro ⟨_, _, _, rfl⟩ (Assn.holds_congr rfl rfl hk2)))

/-- `st_be64(e1, e2)` at a call site. -/
theorem st_be64_hc (hE : GuestEnv E) {args : List (Exp Word)} {p v : Word}
    (hargs : E.evalArgs s args = some [.word p, .word v]) (lo hi : Word)
    (hl8 : lo.toNat % 8 = 0) (hlo : lo.toNat ≤ p.toNat) (hhi : p.toNat + 8 ≤ hi.toNat)
    (hb : hi.toNat ≤ 2 ^ 62) :
    ∀ parameters cbody values cl,
      lookupPanFunction "st_be64" E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (Assn.Range lo hi)
        (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ Assn.Range lo hi) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 28 hE.functions (by guest_decl_at 28) (by decide +kernel)
    hlk).2
  rw [hargs] at hvalues
  cases hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact st_be64_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ p v lo hi
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hl8 hlo hhi hb

set_option maxHeartbeats 2000000 in
/-- `u256_to_be32(a, out)`: 32 bytes written inside an owned range. -/
theorem u256_to_be32_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "u256_to_be32" E.functions = some (parameters, body))
    (s : St σ) (out w0 w1 w2 w3 lo hi : Word) (hout : s.locals "out" = some (.word out))
    (ha : s.locals "a" = some (.rStruct [.word w0, .word w1, .word w2, .word w3]))
    (hl8 : lo.toNat % 8 = 0) (hlo : lo.toNat ≤ out.toNat) (hhi : out.toNat + 32 ≤ hi.toNat)
    (hb : hi.toNat ≤ 2 ^ 62) :
    WPFt E s body (Assn.Range lo hi)
      (fun r => ⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ Assn.Range lo hi) := by
  have hbody := (fun_of_index 87 hE.functions (by guest_decl_at 87) (by decide +kernel)
    hlookup).1
  subst hbody
  intro R hR
  dsimp only
  have h8 : (out + 8#64).toNat = out.toNat + 8 := by bv_omega
  have h16 : (out + 16#64).toNat = out.toNat + 16 := by bv_omega
  have h24 : (out + 24#64).toNat = out.toNat + 24 := by bv_omega
  have htrap : ∀ r : Result σ, Trap r → Trap r ∨
      ((⌜∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆ Assn.Range lo hi) ⋆ R).holds r.st :=
    fun r ht => Or.inl ht
  refine WPr.seq_ite_skip ?_ ?_
  · -- aligned: four word stores
    refine WPr.decCall_quiet (bswap64_quiet hE) (bswap64_raises hE)
      (fun r hr => by cases r <;> first | exact hr.elim | exact Or.inl hr) (fun vw hsh => ?_)
    obtain ⟨x0, rfl⟩ := word_of_shape_one hsh
    have hR0 := Assn.holds_congr (s' := (⟨updatePanValueMap s.locals "w" (.word x0), s.globals,
      s.memory, s.ffi⟩ : St σ)) rfl rfl hR
    refine WPr.seq_store_at hE hR0 (addr := out) (w := x0) (of_eval (by lk [hout]))
      (of_eval (by lk [])) (Step.range hlo (by omega)) (fun m1 hm1 => ?_)
    refine WPr.seq_callA_quiet (o := x0) (by lk []) (bswap64_quiet hE) (bswap64_raises hE)
      (fun r hr => by
        cases r <;> first | exact hr.elim | (simp only [restorePanValueFfiLocal]; exact Or.inl hr))
      (fun x1 => ?_)
    have hR1 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap s.locals "w"
      (.word x0)) "w" (.word x1), s.globals, m1, s.ffi⟩ : St σ)) rfl rfl hm1
    refine WPr.seq_store_at hE hR1 (addr := out + 8#64) (w := x1) (of_eval (by ev [hout]))
      (of_eval (by lk [])) (Step.range (by omega) (by omega)) (fun m2 hm2 => ?_)
    refine WPr.seq_callA_quiet (o := x1) (by lk []) (bswap64_quiet hE) (bswap64_raises hE)
      (fun r hr => by
        cases r <;> first | exact hr.elim | (simp only [restorePanValueFfiLocal]; exact Or.inl hr))
      (fun x2 => ?_)
    have hR2 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap
      (updatePanValueMap s.locals "w" (.word x0)) "w" (.word x1)) "w" (.word x2), s.globals, m2,
      s.ffi⟩ : St σ)) rfl rfl hm2
    refine WPr.seq_store_at hE hR2 (addr := out + 16#64) (w := x2) (of_eval (by ev [hout]))
      (of_eval (by lk [])) (Step.range (by omega) (by omega)) (fun m3 hm3 => ?_)
    refine WPr.seq_callA_quiet (o := x2) (by lk []) (bswap64_quiet hE) (bswap64_raises hE)
      (fun r hr => by
        cases r <;> first | exact hr.elim | (simp only [restorePanValueFfiLocal]; exact Or.inl hr))
      (fun x3 => ?_)
    have hR3 := Assn.holds_congr (s' := (⟨updatePanValueMap (updatePanValueMap (updatePanValueMap
      (updatePanValueMap s.locals "w" (.word x0)) "w" (.word x1)) "w" (.word x2)) "w" (.word x3),
      s.globals, m3, s.ffi⟩ : St σ)) rfl rfl hm3
    refine WPr.seq_store_at hE hR3 (addr := out + 24#64) (w := x3) (of_eval (by ev [hout]))
      (of_eval (by lk [])) (Step.range (by omega) (by omega)) (fun m4 hm4 => ?_)
    refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    exact Or.inr (Assn.holds_pure_intro ⟨_, _, _, rfl⟩ (Assn.holds_congr rfl rfl hm4))
  · -- unaligned: four `st_be64`
    refine WPr.seq_call_framedT hR (st_be64_hc hE (p := out) (v := w3)
      (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        evalF_rField, hout, ha]) lo hi hl8 hlo (by omega) hb) htrap ?_ ?_
    rotate_left
    · intro l g m ffi exc v' _ h
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    intro l g m ffi vs h
    obtain ⟨⟨_, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    refine WPr.seq_call_framedT hk (st_be64_hc hE (p := out + 8#64) (v := w2)
      (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        evalF_rField, evalF_op hE.word, eval_const, wordOp, hout, ha]) lo hi hl8 (by omega)
      (by omega) hb) htrap ?_ ?_
    rotate_left
    · intro l2 g2 m2 ffi2 exc v' _ h
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    intro l2 g2 m2 ffi2 vs2 h
    obtain ⟨⟨_, _, _, hC⟩, hk2⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    refine WPr.seq_call_framedT hk2 (st_be64_hc hE (p := out + 16#64) (v := w1)
      (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        evalF_rField, evalF_op hE.word, eval_const, wordOp, hout, ha]) lo hi hl8 (by omega)
      (by omega) hb) htrap ?_ ?_
    rotate_left
    · intro l3 g3 m3 ffi3 exc v' _ h
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    intro l3 g3 m3 ffi3 vs3 h
    obtain ⟨⟨_, _, _, hC⟩, hk3⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    refine WPr.seq_call_framedT hk3 (st_be64_hc hE (p := out + 24#64) (v := w0)
      (by simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, eval_local,
        evalF_rField, evalF_op hE.word, eval_const, wordOp, hout, ha]) lo hi hl8 (by omega)
      (by omega) hb) htrap ?_ ?_
    rotate_left
    · intro l4 g4 m4 ffi4 exc v' _ h
      obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim h
      cases hC
    intro l4 g4 m4 ffi4 vs4 h
    obtain ⟨⟨_, _, _, hC⟩, hk4⟩ := Assn.holds_pure_elim h
    injection hC with _ _ _ hf _
    subst hf
    exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
      (Or.inr (Assn.holds_pure_intro ⟨_, _, _, rfl⟩ (Assn.holds_congr rfl rfl hk4)))

end InitECandidate.Solver.GuestBound
