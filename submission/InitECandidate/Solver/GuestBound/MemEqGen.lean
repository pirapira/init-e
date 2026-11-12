import InitECandidate.Solver.GuestBound.MemCpy

/-!
# `memeq` on equal bytes

When the `n` bytes at `a` and at `b` are equal, no comparison in `memeq`
fails, so the function returns 1 if it returns.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The compared ranges do not wrap and hold the same bytes. -/
structure EqPre (m : Word → Option (PanValue Word)) (A B nW : Word) : Prop where
  hA : A.toNat + nW.toNat < 2 ^ 64
  hB : B.toNat + nW.toNat < 2 ^ 64
  hn : nW.toNat < 2 ^ 63
  bytes : ∀ k, k < nW.toNat → byteAt m (off A k) = byteAt m (off B k)

variable {m : Word → Option (PanValue Word)} {A B nW : Word}

theorem off_off (a : Word) (j k : Nat) : off (off a j) k = off a (j + k) := by
  unfold off
  rw [BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The cell at an aligned offset holds the bytes of the range. -/
theorem byteAt_cell {a : Word} {j k : Nat} {w : Word} (h64 : a.toNat + j + 8 ≤ 2 ^ 64)
    (h8 : (a.toNat + j) % 8 = 0) (hk : k < 8) (hw : m (off a j) = some (.word w)) :
    byteAt m (off a (j + k)) = some (gb (off (off a j) k) w) := by
  have hal : al8 (off a (j + k)) = off a j := by
    apply BitVec.eq_of_toNat_eq
    rw [align8_toNat, off_toNat (by omega), off_toNat (by omega)]
    omega
  unfold byteAt
  rw [hal, hw, off_off]

/-- `if lds 1 ea != lds 1 eb { return 0; }` on equal aligned words. -/
theorem eq_wguard (hE : GuestEnv E) (P : EqPre m A B nW) (hm : s.memory = m)
    {ea eb : Exp Word} {rest : Prog Word} {j : Nat}
    (hea : E.eval s ea = some (.word (off A j))) (heb : E.eval s eb = some (.word (off B j)))
    (hj : j + 8 ≤ nW.toNat) (hA8 : (A.toNat + j) % 8 = 0) (hB8 : (B.toNat + j) % 8 = 0)
    (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual (.load .one ea) (.load .one eb))
      (.return (.const 0#64)) .skip) rest) Q := by
  have hPA := P.hA
  have hPB := P.hB
  refine WPs.guard0 ?_ h
  intro x hx
  rw [evalF_cmp hE.word] at hx
  cases h1 : E.eval s (.load .one ea) with
  | none => rw [h1] at hx; simp at hx
  | some y1 =>
    cases h2 : E.eval s (.load .one eb) with
    | none => rw [h1, h2] at hx; simp at hx
    | some y2 =>
      obtain ⟨a1, w1, ha1, rfl, hm1⟩ := eval_load_one hE.mem h1
      obtain ⟨a2, w2, ha2, rfl, hm2⟩ := eval_load_one hE.mem h2
      rw [hea] at ha1
      rw [heb] at ha2
      simp only [Option.some.injEq, PanValue.word.injEq] at ha1 ha2
      subst ha1 ha2
      rw [hm] at hm1 hm2
      have hw : w1 = w2 := by
        refine word_ext (A := off A j) (B := off B j) (by rw [off_toNat (by omega)]; exact hA8)
          (by rw [off_toNat (by omega)]; exact hB8) (by rw [off_toNat (by omega)]; omega)
          (by rw [off_toNat (by omega)]; omega) ?_
        intro k hk
        have hb := P.bytes (j + k) (by omega)
        rw [byteAt_cell (by omega) hA8 hk hm1, byteAt_cell (by omega) hB8 hk hm2] at hb
        exact Option.some.inj hb
      subst hw
      rw [h1, h2] at hx
      simp only [Option.some.injEq] at hx
      rw [← hx]
      simp [evalPanCmp]

/-- `if ld8 ea != ld8 eb { return 0; }` on equal bytes. -/
theorem eq_bguard (hE : GuestEnv E) (P : EqPre m A B nW) (hm : s.memory = m)
    {ea eb : Exp Word} {rest : Prog Word} {j : Nat}
    (hea : E.eval s ea = some (.word (off A j))) (heb : E.eval s eb = some (.word (off B j)))
    (hj : j < nW.toNat) (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual (.loadByte ea) (.loadByte eb))
      (.return (.const 0#64)) .skip) rest) Q := by
  refine WPs.guard0 ?_ h
  intro x hx
  rw [evalF_cmp hE.word] at hx
  cases h1 : E.eval s (.loadByte ea) with
  | none => rw [h1] at hx; simp at hx
  | some y1 =>
    cases h2 : E.eval s (.loadByte eb) with
    | none => rw [h1, h2] at hx; simp at hx
    | some y2 =>
      obtain ⟨a1, c1, ha1, hc1, rfl⟩ := eval_loadByte hE.mem h1
      obtain ⟨a2, c2, ha2, hc2, rfl⟩ := eval_loadByte hE.mem h2
      rw [hea] at ha1
      rw [heb] at ha2
      simp only [Option.some.injEq, PanValue.word.injEq] at ha1 ha2
      subst ha1 ha2
      rw [hE.bytes, hm] at hc1 hc2
      have hb := P.bytes j hj
      unfold byteAt at hb
      rw [hc1, hc2] at hb
      have hv := Option.some.inj hb
      rw [h1, h2] at hx
      simp only [Option.some.injEq] at hx
      rw [← hx, hE.bytes]
      show PanValue.word (evalPanCmp .notEqual (gb (off A j) c1) (gb (off B j) c2)) = _
      rw [hv]
      simp [evalPanCmp]

/-- State of `memeq` with `i = jb`. -/
def EqS (m : Word → Option (PanValue Word)) (A B nW : Word)
    (g : VarName → Option (PanValue Word)) (f : FfiState σ) (jb : Nat) (s : St σ) : Prop :=
  s.globals = g ∧ s.memory = m ∧ s.ffi = f ∧ s.locals "a" = some (.word A) ∧
    s.locals "b" = some (.word B) ∧ s.locals "n" = some (.word nW) ∧
    s.locals "i" = some (.word (BitVec.ofNat 64 jb))

variable {g : VarName → Option (PanValue Word)} {f : FfiState σ} {jb : Nat}

theorem eval_offc (hE : GuestEnv E) {x : VarName} {a : Word} (c : Word)
    (hx : s.locals x = some (.word a)) :
    E.eval s (.op .add [.var .local x, .const c]) = some (.word (off a c.toNat)) := by
  rw [eval_addc hE c hx]
  unfold off
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem eval_offv {x : VarName} {a : Word} (hx : s.locals x = some (.word a)) :
    E.eval s (.var .local x) = some (.word (off a 0)) := by
  rw [evalF_local, hx, off_zero]

variable {rest : Prog Word}

theorem eqW_v (hE : GuestEnv E) (P : EqPre m A B nW) (hS : EqS m A B nW g f jb s)
    (hj : 0 + 8 ≤ nW.toNat) (hA8 : (A.toNat + 0) % 8 = 0) (hB8 : (B.toNat + 0) % 8 = 0)
    (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual (.load .one (.var .local "a"))
      (.load .one (.var .local "b"))) (.return (.const 0#64)) .skip) rest) Q :=
  eq_wguard hE P hS.2.1 (eval_offv hS.2.2.2.1) (eval_offv hS.2.2.2.2.1) hj hA8 hB8 h

theorem eqW_c (hE : GuestEnv E) (P : EqPre m A B nW) (hS : EqS m A B nW g f jb s) (c : Word)
    (hj : c.toNat + 8 ≤ nW.toNat) (hA8 : (A.toNat + c.toNat) % 8 = 0)
    (hB8 : (B.toNat + c.toNat) % 8 = 0) (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local "a", .const c]))
      (.load .one (.op .add [.var .local "b", .const c]))) (.return (.const 0#64)) .skip) rest)
      Q :=
  eq_wguard hE P hS.2.1 (eval_offc hE c hS.2.2.2.1) (eval_offc hE c hS.2.2.2.2.1) hj hA8 hB8 h

theorem eqW_i (hE : GuestEnv E) (P : EqPre m A B nW) (hS : EqS m A B nW g f jb s)
    (hj : jb + 8 ≤ nW.toNat) (hA8 : (A.toNat + jb) % 8 = 0) (hB8 : (B.toNat + jb) % 8 = 0)
    (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual (.load .one (.op .add [.var .local "a", .var .local "i"]))
      (.load .one (.op .add [.var .local "b", .var .local "i"]))) (.return (.const 0#64)) .skip)
      rest) Q :=
  eq_wguard hE P hS.2.1 (eval_off0 hE hS.2.2.2.1 hS.2.2.2.2.2.2)
    (eval_off0 hE hS.2.2.2.2.1 hS.2.2.2.2.2.2) hj hA8 hB8 h

theorem eqW_ic (hE : GuestEnv E) (P : EqPre m A B nW) (hS : EqS m A B nW g f jb s) (c : Word)
    (hj : jb + c.toNat + 8 ≤ nW.toNat) (hA8 : (A.toNat + (jb + c.toNat)) % 8 = 0)
    (hB8 : (B.toNat + (jb + c.toNat)) % 8 = 0) (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual
      (.load .one (.op .add [.var .local "a", .var .local "i", .const c]))
      (.load .one (.op .add [.var .local "b", .var .local "i", .const c])))
      (.return (.const 0#64)) .skip) rest) Q :=
  eq_wguard hE P hS.2.1 (eval_offk hE c hS.2.2.2.1 hS.2.2.2.2.2.2)
    (eval_offk hE c hS.2.2.2.2.1 hS.2.2.2.2.2.2) hj hA8 hB8 h

theorem eqB_c (hE : GuestEnv E) (P : EqPre m A B nW) (hS : EqS m A B nW g f jb s) (c : Word)
    (hj : c.toNat < nW.toNat) (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local "a", .const c]))
      (.loadByte (.op .add [.var .local "b", .const c]))) (.return (.const 0#64)) .skip) rest)
      Q :=
  eq_bguard hE P hS.2.1 (eval_offc hE c hS.2.2.2.1) (eval_offc hE c hS.2.2.2.2.1) hj h

theorem eqB_i (hE : GuestEnv E) (P : EqPre m A B nW) (hS : EqS m A B nW g f jb s)
    (hj : jb < nW.toNat) (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual (.loadByte (.op .add [.var .local "a", .var .local "i"]))
      (.loadByte (.op .add [.var .local "b", .var .local "i"]))) (.return (.const 0#64)) .skip)
      rest) Q :=
  eq_bguard hE P hS.2.1 (eval_off0 hE hS.2.2.2.1 hS.2.2.2.2.2.2)
    (eval_off0 hE hS.2.2.2.2.1 hS.2.2.2.2.2.2) hj h

theorem eqB_ic (hE : GuestEnv E) (P : EqPre m A B nW) (hS : EqS m A B nW g f jb s) (c : Word)
    (hj : jb + c.toNat < nW.toNat) (h : WPs E s rest Q) :
    WPs E s (.seq (.ite (.cmp .notEqual
      (.loadByte (.op .add [.var .local "a", .var .local "i", .const c]))
      (.loadByte (.op .add [.var .local "b", .var .local "i", .const c])))
      (.return (.const 0#64)) .skip) rest) Q :=
  eq_bguard hE P hS.2.1 (eval_offk hE c hS.2.2.2.1 hS.2.2.2.2.2.2)
    (eval_offk hE c hS.2.2.2.2.1 hS.2.2.2.2.2.2) hj h

/-- `i = i + k` in `memeq`. -/
theorem eq_assign (hE : GuestEnv E) (k : Word) {j : Nat} (hS : EqS m A B nW g f jb s)
    (hjk : j = jb + k.toNat) :
    WPs E s (.assign .local "i" (.op .add [.var .local "i", .const k]))
      (fun r => ∃ l g' m' f', r = .normal l g' m' f' ∧ EqS m A B nW g f j ⟨l, g', m', f'⟩) := by
  obtain ⟨hg, hm, hf, h1, h2, h3, h4⟩ := hS
  have hval : BitVec.ofNat 64 jb + k = BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hjk]
    omega
  refine WPs.assign (old := BitVec.ofNat 64 jb) h4
    (of_eval (w := BitVec.ofNat 64 j) (by rw [← hval]; ev [h4])) ?_
  exact ⟨_, _, _, _, rfl, hg, hm, hf, by lk [h1], by lk [h2], by lk [h3], by lk []⟩

/-- The guard `n >=+ i + k` holds. -/
theorem eq_cond (hE : GuestEnv E) (hn63 : nW.toNat < 2 ^ 63) (k : Word) (hk : k.toNat ≤ 64)
    (hS : EqS m A B nW g f jb s) (hjb : jb ≤ nW.toNat)
    (hct : CondTrue E s (.cmp .notLower (.var .local "n")
      (.op .add [.var .local "i", .const k]))) : jb + k.toNat ≤ nW.toNat := by
  obtain ⟨-, -, -, -, -, h3, h4⟩ := hS
  obtain ⟨w, c, hcond, hw⟩ := hct
  have hev := cond_of_eval hcond
  have := eval_cmp_inv hE (of_eval (w := nW) (by lk [h3]))
    (of_eval (w := BitVec.ofNat 64 jb + k) (by ev [h4])) _ hev
  simp only [PanValue.word.injEq] at this
  by_contra hlt
  have hsum : (BitVec.ofNat 64 jb + k).toNat = jb + k.toNat := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hl : nW < BitVec.ofNat 64 jb + k := by
    rw [BitVec.lt_def, hsum]
    omega
  rw [this] at hw
  simp [evalPanCmp, hl] at hw

/-- The test `n == c` succeeded. -/
theorem eq_nIs (hE : GuestEnv E) (hS : EqS m A B nW g f jb s) {c w : Word}
    (hw : E.eval s (.cmp .equal (.var .local "n") (.const c)) = some (.word w)) (hne : ¬ w = 0) :
    nW.toNat = c.toNat := by
  have := eval_cmp_inv hE (of_eval (w := nW) (by lk [hS.2.2.2.2.2.1]))
    (of_eval (eval_const _ c)) _ hw
  simp only [PanValue.word.injEq] at this
  by_contra hcn
  apply hne
  rw [this]
  have : nW ≠ c := fun h => hcn (by rw [h])
  simp [evalPanCmp, this]

macro "bnd" : tactic => `(tactic| first | omega | (simp <;> omega) | simp)

set_option hygiene false in
macro "eqg" : tactic => `(tactic| first
  | refine eqW_v hE P hS (by bnd) (by bnd) (by bnd) ?_
  | refine eqW_c hE P hS _ (by bnd) (by bnd) (by bnd) ?_
  | refine eqW_i hE P hS (by bnd) (by bnd) (by bnd) ?_
  | refine eqW_ic hE P hS _ (by bnd) (by bnd) (by bnd) ?_
  | refine eqB_c hE P hS _ (by bnd) ?_
  | refine eqB_i hE P hS (by bnd) ?_
  | refine eqB_ic hE P hS _ (by bnd) ?_)

set_option maxHeartbeats 4000000 in
/-- `memeq(a, b, n)` on equal bytes returns 1 if it returns, and changes nothing. -/
theorem memeq_eq (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "memeq" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A B nW : Word) (ha : s.locals "a" = some (.word A))
    (hb : s.locals "b" = some (.word B)) (hn : s.locals "n" = some (.word nW))
    (P : EqPre s.memory A B nW) (h : Runs E s body r) :
    Stopped r ∨ ∃ l, r = .returned l s.globals s.memory s.ffi [.word 1#64] := by
  have hbody := (fun_of_index 18 hE.functions (by guest_decl_at 18) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l, r = .returned l s.globals s.memory s.ffi [.word 1#64]))
    r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l, r = .returned l s.globals s.memory s.ffi [.word 1#64])
    ?_ (by rintro r ⟨l, rfl⟩; exact ⟨_, rfl⟩)
  have hS0 : EqS s.memory A B nW s.globals s.ffi 0
      ⟨updatePanValueMap s.locals "i" (.word 0#64), s.globals, s.memory, s.ffi⟩ :=
    ⟨rfl, rfl, rfl, by lk [ha], by lk [hb], by lk [hn], by lk []⟩
  have hn63 := P.hn
  have hret : ∀ (a : St σ) (jb : Nat) (Q' : Result σ → Prop),
      EqS s.memory A B nW s.globals s.ffi jb a →
      (∀ l, Q' (.returned l s.globals s.memory s.ffi [.word 1#64])) →
      WPs E a (.return (.const 1#64)) Q' := by
    intro a jb Q' hS hQ
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    obtain ⟨hg, hm, hf, -⟩ := hS
    rw [hg, hm, hf]
    exact hQ _
  have h8 : (8#64 : Word).toNat = 8 := by decide
  have h32 : (32#64 : Word).toNat = 32 := by decide
  have h1 : (1#64 : Word).toNat = 1 := by decide
  refine WPs.seqG (fun a => ∃ jb, EqS s.memory A B nW s.globals s.ffi jb a ∧ jb ≤ nW.toNat)
    ?_ ?_
  · refine WPs.ite_both (fun w hw => ?_)
    split
    · exact WPs.skip ⟨0, hS0, Nat.zero_le _⟩
    · rename_i hw0
      have hal : A.toNat % 8 = 0 ∧ B.toNat % 8 = 0 := by
        have hand : ∀ a b : Word, AndOp.and a b = a &&& b := fun _ _ => rfl
        have hor : ∀ a b : Word, OrOp.or a b = a ||| b := fun _ _ => rfl
        have hones : ∀ a : Word, a &&& 18446744073709551615#64 = a := by intro a; bv_decide
        simp [evalF_cmp hE.word, evalF_op hE.word, evalArgs_cons, evalArgs_nil,
          update_lookup, ha, hb, wordOp, hand, hor, hones, evalPanCmp] at hw
        have hz : (A ||| B) &&& 7#64 = 0#64 := by
          by_contra hne
          rw [if_neg hne] at hw
          exact hw0 hw.symm
        exact or_and7 A B hz
      obtain ⟨hA8, hB8⟩ := hal
      have hS := hS0
      -- n == 20
      refine WPs.seqG (fun a => EqS s.memory A B nW s.globals s.ffi 0 a) ?_ ?_
      · refine WPs.ite_both (fun w hw => ?_)
        split
        · exact WPs.skip hS
        · rename_i hne
          have hnn := eq_nIs hE hS hw hne
          simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hnn
          eqg
          eqg
          eqg
          eqg
          eqg
          eqg
          exact hret _ 0 _ hS (fun l => ⟨l, rfl⟩)
      intro a1 hS
      -- n == 32
      refine WPs.seqG (fun a => EqS s.memory A B nW s.globals s.ffi 0 a) ?_ ?_
      · refine WPs.ite_both (fun w hw => ?_)
        split
        · exact WPs.skip hS
        · rename_i hne
          have hnn := eq_nIs hE hS hw hne
          simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hnn
          eqg
          eqg
          eqg
          eqg
          exact hret _ 0 _ hS (fun l => ⟨l, rfl⟩)
      intro a2 hS
      -- n == 52
      refine WPs.seqG (fun a => EqS s.memory A B nW s.globals s.ffi 0 a) ?_ ?_
      · refine WPs.ite_both (fun w hw => ?_)
        split
        · exact WPs.skip hS
        · rename_i hne
          have hnn := eq_nIs hE hS hw hne
          simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hnn
          eqg
          eqg
          eqg
          eqg
          eqg
          eqg
          eqg
          eqg
          eqg
          eqg
          exact hret _ 0 _ hS (fun l => ⟨l, rfl⟩)
      intro a3 hS
      -- word loops
      refine WPs.seq (fun a => ∃ jb, EqS s.memory A B nW s.globals s.ffi jb a ∧ jb ≤ nW.toNat ∧
          jb % 8 = 0)
        (WPs.loop (I := fun a => ∃ jb, EqS s.memory A B nW s.globals s.ffi jb a ∧
            jb ≤ nW.toNat ∧ jb % 8 = 0) ⟨0, hS, Nat.zero_le _, rfl⟩ ?_
          (fun a k hI _ => ⟨_, _, _, _, rfl, hI⟩)) ?_
      · rintro a ⟨jb, hS, hj, hj8⟩ hct
        have hle := eq_cond hE hn63 32#64 (by decide) hS hj hct
        rw [h32] at hle
        eqg
        eqg
        eqg
        eqg
        exact (eq_assign hE 32#64 hS (j := jb + 32) (by rw [h32])).conseq
          (fun r ⟨l, g', m', f', hr, hS'⟩ => ⟨l, g', m', f', hr, jb + 32, hS', by omega, by omega⟩)
      · rintro a4 ⟨jb0, hS, hj0, hj08⟩
        refine WPs.loop (I := fun a => ∃ jb, EqS s.memory A B nW s.globals s.ffi jb a ∧
            jb ≤ nW.toNat ∧ jb % 8 = 0) ⟨jb0, hS, hj0, hj08⟩ ?_
          (fun a k ⟨jb, hI, hj, _⟩ _ => ⟨jb, hI, hj⟩)
        rintro a ⟨jb, hS, hj, hj8⟩ hct
        have hle := eq_cond hE hn63 8#64 (by decide) hS hj hct
        rw [h8] at hle
        eqg
        exact (eq_assign hE 8#64 hS (j := jb + 8) (by rw [h8])).conseq
          (fun r ⟨l, g', m', f', hr, hS'⟩ => ⟨l, g', m', f', hr, jb + 8, hS', by omega, by omega⟩)
  · rintro a ⟨jb0, hS, hj0⟩
    refine WPs.seq (fun a => ∃ jb, EqS s.memory A B nW s.globals s.ffi jb a ∧ jb ≤ nW.toNat)
      (WPs.loop (I := fun a => ∃ jb, EqS s.memory A B nW s.globals s.ffi jb a ∧
          jb ≤ nW.toNat) ⟨jb0, hS, hj0⟩ ?_ (fun a k hI _ => ⟨_, _, _, _, rfl, hI⟩)) ?_
    · rintro a ⟨jb, hS, hj⟩ hct
      have hle := eq_cond hE hn63 8#64 (by decide) hS hj hct
      rw [h8] at hle
      eqg
      eqg
      eqg
      eqg
      eqg
      eqg
      eqg
      eqg
      exact (eq_assign hE 8#64 hS (j := jb + 8) (by rw [h8])).conseq
        (fun r ⟨l, g', m', f', hr, hS'⟩ => ⟨l, g', m', f', hr, jb + 8, hS', by omega⟩)
    · rintro a' ⟨jb1, hS, hj1⟩
      refine WPs.seq (fun a => ∃ jb, EqS s.memory A B nW s.globals s.ffi jb a ∧ jb ≤ nW.toNat)
        (WPs.loop (I := fun a => ∃ jb, EqS s.memory A B nW s.globals s.ffi jb a ∧
            jb ≤ nW.toNat) ⟨jb1, hS, hj1⟩ ?_ (fun a k hI _ => ⟨_, _, _, _, rfl, hI⟩)) ?_
      · rintro a ⟨jb, hS, hj⟩ ⟨w, c, hcond, hw⟩
        have hjt : (BitVec.ofNat 64 jb : Word).toNat = jb := by
          rw [BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (by omega)
        have hc := eval_cmp_inv hE (op := .lower)
          (of_eval (w := BitVec.ofNat 64 jb) (by lk [hS.2.2.2.2.2.2]))
          (of_eval (w := nW) (by lk [hS.2.2.2.2.2.1])) _ (cond_of_eval hcond)
        simp only [PanValue.word.injEq] at hc
        have hlt : jb < nW.toNat := by
          by_contra hge
          have hnl : ¬ (BitVec.ofNat 64 jb : Word) < nW := by
            rw [BitVec.lt_def, hjt]
            exact hge
          rw [hc] at hw
          simp [evalPanCmp, hnl] at hw
        eqg
        exact (eq_assign hE 1#64 hS (j := jb + 1) (by rw [h1])).conseq
          (fun r ⟨l, g', m', f', hr, hS'⟩ => ⟨l, g', m', f', hr, jb + 1, hS', by omega⟩)
      · rintro a'' ⟨jb2, hS, -⟩
        exact hret _ jb2 _ hS (fun l => ⟨l, rfl⟩)

end InitECandidate.Solver.GuestBound
