import InitECandidate.Solver.GuestBound.CompactNibbles
import InitECandidate.Solver.GuestBound.KeyNibblesSeg
import InitECandidate.Solver.GuestBound.NibStore
import InitECandidate.Solver.GuestBound.ResolveStep
import InitECandidate.Solver.GuestBound.RlpItemFrame
import InitECandidate.Solver.GuestBound.WorldRestore

/-!
# `compact_to_nibbles` produces a nibble array

`compact_to_nibbles(p, n)` allocates `2 * n` bytes at the heap pointer and
writes `k + 2 * (n - 1)` nibbles there (`k` is 1 when the compact encoding has
an odd number of nibbles).  On return the block holds nibbles only, so it can
be registered as an immutable block (`WorldTJ.fresh_nibs`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Nibbles survive a change that leaves their bytes alone. -/
theorem Nibs.bytes {m m' : Word → Option (PanValue Word)} {o : Word} {c : Nat}
    (h : Nibs m o c) (hc : o.toNat + c ≤ 2 ^ 64)
    (hb : ∀ p : Word, p.toNat < o.toNat + c → byteAt m' p = byteAt m p) : Nibs m' o c := by
  intro j hj
  obtain ⟨b, hb1, hb2⟩ := h j hj
  refine ⟨b, ?_, hb2⟩
  rw [hb _ (by rw [off_toNat (by omega)]; omega)]
  exact hb1

/-- Two adjacent nibble arrays. -/
theorem Nibs.append {m : Word → Option (PanValue Word)} {o o' : Word} {c1 c2 : Nat}
    (h1 : Nibs m o c1) (h2 : Nibs m o' c2) (ho : o'.toNat = o.toNat + c1)
    (hc : o.toNat + c1 + c2 ≤ 2 ^ 64) : Nibs m o (c1 + c2) := by
  intro j hj
  by_cases hj1 : j < c1
  · exact h1 j hj1
  · obtain ⟨b, hb1, hb2⟩ := h2 (j - c1) (by omega)
    refine ⟨b, ?_, hb2⟩
    have e : off o j = off o' (j - c1) := by
      apply BitVec.eq_of_toNat_eq
      rw [off_toNat (by omega), off_toNat (by omega), ho]
      omega
    rw [e]
    exact hb1

/-- What a returning `key_to_nibbles` leaves, with the bytes below the output. -/
theorem keynibbles_ret2 (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {kw nw ow0 : Word}
    {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
    {m : Word → Option (PanValue Word)} {ffi : FfiState σ}
    (h : CalleeRet E s "key_to_nibbles" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word kw)) (h2 : E.eval s e2 = some (.word nw))
    (h3 : E.eval s e3 = some (.word ow0)) (hob : ow0.toNat < 33806089704 + 16) :
    g = s.globals ∧ ffi = s.ffi ∧ ow0.toNat + 2 * nw.toNat < 33806089704 + 16 ∧
      Nibs m ow0 (2 * nw.toNat) ∧
      (∀ x : Word, (x.toNat < ow0.toNat / 8 * 8 ∨ ow0.toNat + 2 * nw.toNat ≤ x.toNat) →
        m x = s.memory x) ∧
      ∀ p : Word, p.toNat < ow0.toNat → byteAt m p = byteAt s.memory p := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 248 hE.functions (by guest_decl_at 248) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases key_to_nibbles_nib2 hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    kw nw ow0 (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hob hrun
    with hst | ⟨l', m', heq, hb, hnb, hfr, hby⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hb, hnb, hfr, hby⟩

/-- Returning three words. -/
theorem WPs.ret_triple {e1 e2 e3 : Exp Word} {a b c : Word}
    (h1 : ∀ y, E.eval s e1 = some y → y = .word a)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word b)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word c)
    (h : Q (.returned (fun _ => none) s.globals s.memory s.ffi
      [.rStruct [.word a, .word b, .word c]])) :
    WPs E s (.return (.rStruct [e1, e2, e3])) Q := by
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
        have := h1 _ k1
        subst this
        have := h2 _ k2
        subst this
        have := h3 _ k3
        subst this
        rw [k1, k2, k3] at hv
        simp at hv
        subst hv
        exact h

/-- What `compact_to_nibbles` guarantees. -/
def CnQ (s : St σ) (hv0 : Word) (r : Result σ) : Prop :=
  ∃ l qv m b wl, r = .returned l (updatePanValueMap s.globals "heap_ptr" (.word qv)) m s.ffi
      [.rStruct [.word hv0, .word b, .word wl]] ∧
    InHeap qv ∧ hv0.toNat + b.toNat ≤ qv.toNat ∧ Nibs m hv0 b.toNat ∧
    ∀ x : Word, (x.toNat < hv0.toNat ∨ qv.toNat ≤ x.toNat) → m x = s.memory x

theorem CnQ.restore {hv0 : Word} {x : VarName} {old : Option (PanValue Word)} {r : Result σ}
    (h : CnQ s hv0 r) : CnQ s hv0 (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, qv, m, b, wl, rfl, hk⟩ := h
  exact ⟨_, qv, m, b, wl, rfl, hk⟩

set_option maxHeartbeats 16000000 in
theorem compact_to_nibbles_nib (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "compact_to_nibbles" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pw nw hv0 : Word) (hpw : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw))
    (hh : s.globals "heap_ptr" = some (.word hv0)) (hhH : InHeap hv0) (h : Runs E s body r) :
    Stopped r ∨ CnQ s hv0 r := by
  have hbody := (fun_of_index 249 hE.functions (by guest_decl_at 249) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (CnQ s hv0)) r h
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  refine WPs.seqG (fun a => a = s ∧ nw ≠ 0#64) (WPs.ite_both (fun w hw => ?_)) ?_
  · obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
    simp only [evalF_local, hn, eval_const, Option.some.injEq, PanValue.word.injEq] at hx hy
    subst hx hy
    split
    · rename_i hw0
      exact WPs.skip ⟨rfl, by
        rintro rfl
        rw [hwv] at hw0
        simp [evalPanCmp] at hw0⟩
    · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
  intro a ha
  obtain ⟨ha, hn0⟩ := ha
  rw [ha]
  clear ha a
  refine WPs.dec_ev (fun vc0 hvc0 => WPs.conseq (Q' := CnQ s hv0) ?_ (fun r h => h.restore))
  obtain ⟨c0w, rfl, hc0⟩ := loadByte_lt hE hvc0
  refine WPs.dec_ev (fun vfirst _ => WPs.conseq (Q' := CnQ s hv0) ?_ (fun r h => h.restore))
  refine WPs.dec_ev (fun vleaf hvleaf => WPs.conseq (Q' := CnQ s hv0) ?_ (fun r h => h.restore))
  obtain ⟨wl, rfl⟩ := isw_op hE _ hvleaf
  refine WPs.dec_ev (fun vodd _ => WPs.conseq (Q' := CnQ s hv0) ?_ (fun r h => h.restore))
  try dsimp only
  refine WPs.decCall_alloc hE (nv := 2#64 * nw) (by ev [hn]) hh hhH (fun qv a1 a2 => ?_)
  refine WPs.conseq (Q' := CnQ s hv0) ?_ (fun r h => h.restore)
  try dsimp only
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := CnQ s hv0) ?_ (fun r h => h.restore)
  generalize hL : updatePanValueMap _ "k" (PanValue.word 0#64) = L
  have L_out : L "out" = some (.word hv0) := by rw [← hL]; lk []
  have L_k : L "k" = some (.word 0#64) := by rw [← hL]; lk []
  have L_p : L "p" = some (.word pw) := by rw [← hL]; lk [hpw]
  have L_n : L "n" = some (.word nw) := by rw [← hL]; lk [hn]
  have L_c0 : L "c0" = some (.word c0w) := by rw [← hL]; lk []
  have L_lf : L "is_leaf" = some (.word wl) := by rw [← hL]; lk []
  have hal := hhH.2
  have hend := hhH.1
  have hqE := a2.1
  refine WPs.seq (fun a => a.globals = updatePanValueMap s.globals "heap_ptr" (.word qv) ∧
      a.ffi = s.ffi ∧ a.locals "out" = some (.word hv0) ∧ a.locals "p" = some (.word pw) ∧
      a.locals "n" = some (.word nw) ∧ a.locals "is_leaf" = some (.word wl) ∧
      (∃ kw : Word, a.locals "k" = some (.word kw) ∧ kw.toNat ≤ 1 ∧
        Nibs a.memory hv0 kw.toNat) ∧
      ∀ x : Word, x.toNat ≠ hv0.toNat → a.memory x = s.memory x)
    (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip ⟨_, _, _, _, rfl, rfl, rfl, L_out, L_p, L_n, L_lf,
        ⟨0#64, L_k, by decide, fun j hj => absurd hj (by simp)⟩, fun _ _ => rfl⟩
    · refine WPs.seq_storeByte_nib hE (addr := hv0) (of_eval (by lk [L_out]))
        (nib_and15 hE (b := c0w) L_c0) (fun m1 w1 hd1 hf1 hw1 hy1 => ?_)
      refine WPs.assign (old := 0#64) L_k (of_eval (w := 1#64) (eval_const _ _)) ?_
      have hn0' : Nibs s.memory hv0 0 := fun j hj => absurd hj (Nat.not_lt_zero _)
      have hn1 := hn0'.snoc (by omega) (by omega) hw1 hy1
      refine ⟨_, _, _, _, rfl, rfl, rfl, by lk [L_out], by lk [L_p], by lk [L_n], by lk [L_lf],
        ⟨1#64, by lk [], by decide, hn1⟩, fun x hx => hf1 x (by omega)⟩
  rintro ⟨la, ga, ma, fa⟩ ⟨hg, hfa, hO, hP, hN, hLf, ⟨kw, hK, hk1, hnk⟩, hfr⟩
  simp only at hg hfa hO hP hN hLf hK hnk hfr
  subst hg hfa
  have hok : (hv0 + kw).toNat = hv0.toNat + kw.toNat := by
    rw [BitVec.toNat_add]
    omega
  refine WPs.seq_call_ret (fun vs g m2 ffi hret => ?_)
  obtain ⟨hg, hf', hb, hnb2, hfr2, hby2⟩ := keynibbles_ret2 hE hret (kw := pw + 1#64)
    (nw := nw - 1#64) (ow0 := hv0 + kw) (by ev [hP]) (by ev [hN]) (by ev [hO, hK])
    (by rw [hok]; omega)
  subst g ffi
  dsimp only at hfr2 hby2
  rw [hok] at hb hfr2 hby2
  have hnl := nw.isLt
  have hn1 : 1 ≤ nw.toNat := by
    by_contra hlt
    exact hn0 (BitVec.eq_of_toNat_eq (by simp; omega))
  have hsub : (nw - 1#64).toNat = nw.toNat - 1 := by
    rw [BitVec.toNat_sub, show (1#64 : Word).toNat = 1 by decide]
    omega
  rw [hsub] at hb hnb2 hfr2
  have hmul : (2#64 * nw).toNat = 2 * nw.toNat := by
    rw [BitVec.toNat_mul, show (2#64 : Word).toNat = 2 by decide]
    omega
  have hmul1 : (2#64 * (nw - 1#64)).toNat = 2 * (nw.toNat - 1) := by
    rw [BitVec.toNat_mul, show (2#64 : Word).toNat = 2 by decide, hsub]
    omega
  have hbv : (kw + 2#64 * (nw - 1#64)).toNat = kw.toNat + 2 * (nw.toNat - 1) := by
    rw [BitVec.toNat_add, hmul1]
    omega
  have a1' : hv0.toNat + 2 * nw.toNat ≤ qv.toNat := by
    have := a1
    rw [hmul] at this
    exact this
  have hpre : Nibs m2 hv0 kw.toNat := hnk.bytes (by omega) (fun p hp => hby2 p hp)
  have hall : Nibs m2 hv0 (kw.toNat + 2 * (nw.toNat - 1)) :=
    hpre.append hnb2 hok (by omega)
  refine WPs.ret_triple (a := hv0) (b := kw + 2#64 * (nw - 1#64)) (c := wl)
    (of_eval (by lk [hO])) (of_eval (by ev [hK, hN])) (of_eval (by lk [hLf])) ?_
  refine ⟨_, qv, m2, _, wl, rfl, a2, by rw [hbv]; omega, by rw [hbv]; exact hall,
    fun x hx => ?_⟩
  rw [hfr2 x (by omega)]
  exact hfr x (by omega)

end InitECandidate.Solver.GuestBound
