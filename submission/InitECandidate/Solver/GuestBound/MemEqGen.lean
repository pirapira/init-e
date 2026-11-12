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

end InitECandidate.Solver.GuestBound
