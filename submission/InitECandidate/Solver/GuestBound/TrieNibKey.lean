import InitECandidate.Solver.GuestBound.TrieSet
import InitECandidate.Solver.GuestBound.Keccak256Frame
import InitECandidate.Solver.GuestBound.KeyNibblesSeg
import InitECandidate.Solver.GuestBound.TrieFresh
import InitECandidate.Solver.GuestBound.RlpItemFrame

/-!
# `mpt_nibble_key` against the world invariant

`mpt_nibble_key(m, key, klen)` either hashes the key into `mpt_hash_scratch`
and expands the 32-byte hash to 64 nibbles, or expands the key itself.  The
nibbles go to a fresh allocation, which becomes an immutable block.  The three
hashing buffers (`keccak_st`, `keccak_pad`, `mpt_hash_scratch`) must lie in
registered free ranges holding no protected cell: that is `KPre`.  This
discharges the interface `NibKeySpec` of `mpt_set`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Returning a pair of words. -/
theorem WPs.ret_pair {e1 e2 : Exp Word} {a b : Word}
    (h1 : ∀ y, E.eval s e1 = some y → y = .word a)
    (h2 : ∀ y, E.eval s e2 = some y → y = .word b)
    (h : Q (.returned (fun _ => none) s.globals s.memory s.ffi [.rStruct [.word a, .word b]])) :
    WPs E s (.return (.rStruct [e1, e2])) Q := by
  refine WPs.ret_ev (fun v hv => ?_)
  rw [evalF_rStruct] at hv
  simp only [evalArgs_cons, evalArgs_nil] at hv
  cases k1 : E.eval s e1 with
  | none => rw [k1] at hv; simp at hv
  | some y1 =>
    cases k2 : E.eval s e2 with
    | none => rw [k1, k2] at hv; simp at hv
    | some y2 =>
      have := h1 _ k1
      subst this
      have := h2 _ k2
      subst this
      rw [k1, k2] at hv
      simp at hv
      subst hv
      exact h

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

/-- What a returning `keccak256` leaves. -/
theorem keccak256_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {pv nv ov stp pad : Word}
    (h : CalleeRet E s "keccak256" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word pv)) (h2 : E.eval s e2 = some (.word nv))
    (h3 : E.eval s e3 = some (.word ov))
    (hst : s.globals "keccak_st" = some (.word stp))
    (hpd : s.globals "keccak_pad" = some (.word pad))
    (hs64 : stp.toNat + 232 < 2 ^ 64) (hp64 : pad.toNat + 168 < 2 ^ 64)
    (ho64 : ov.toNat + 64 < 2 ^ 64) (hn64 : nv.toNat + 136 < 2 ^ 64) :
    g = s.globals ∧ ffi = s.ffi ∧ KFr stp pad ov s.memory m := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 103 hE.functions (by guest_decl_at 103) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases keccak256_frame hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    pv nv ov stp pad
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hst hpd hs64 hp64 ho64 hn64 hrun with hst' | ⟨l', m', heq, hfr⟩
  · exact absurd hst' (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr⟩

/-- What a returning `key_to_nibbles` leaves. -/
theorem key_to_nibbles_ret (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {kw nw ow0 : Word}
    (h : CalleeRet E s "key_to_nibbles" [e1, e2, e3] vs g m ffi)
    (h1 : E.eval s e1 = some (.word kw)) (h2 : E.eval s e2 = some (.word nw))
    (h3 : E.eval s e3 = some (.word ow0)) (hob : ow0.toNat < 33806089704 + 16) :
    g = s.globals ∧ ffi = s.ffi ∧ Nibs m ow0 (2 * nw.toNat) ∧
      ∀ x : Word, (x.toNat < ow0.toNat / 8 * 8 ∨ ow0.toNat + 2 * nw.toNat ≤ x.toNat) →
        m x = s.memory x := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 248 hE.functions (by guest_decl_at 248) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases key_to_nibbles_nib hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    kw nw ow0
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hob hrun with hst' | ⟨l', m', heq, -, hnb, hfr⟩
  · exact absurd hst' (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hnb, hfr⟩

end rets

section world

variable {Rg : Reg} {g : VarName → Option (PanValue Word)}
  {m m' : Word → Option (PanValue Word)}

/-- A registered free range lies inside the heap. -/
theorem WorldTJ.blk_bounds {lo hi : Word} (hW : WorldTJ Rg g m) (hb : Rg.B lo hi) :
    HBASE ≤ lo.toNat ∧ hi.toNat ≤ 2952790016 := by
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hD, hB, hCn, hNd, hIm⟩ := hW
  have hf := hB lo hi hb
  have := hf.lo_
  have := hf.hi_
  have := hpH.1
  exact ⟨by omega, by omega⟩

/-- A change confined to three registered free ranges without protected cells. -/
theorem WorldTJ.write_free3 {l1 h1 l2 h2 l3 h3 : Word} (h : WorldTJ Rg g m)
    (b1 : Rg.B l1 h1) (b2 : Rg.B l2 h2) (b3 : Rg.B l3 h3)
    (c1 : ∀ x w, Rg.Cn x w → ¬ (l1.toNat ≤ x.toNat ∧ x.toNat < h1.toNat))
    (c2 : ∀ x w, Rg.Cn x w → ¬ (l2.toNat ≤ x.toNat ∧ x.toNat < h2.toNat))
    (c3 : ∀ x w, Rg.Cn x w → ¬ (l3.toNat ≤ x.toNat ∧ x.toNat < h3.toNat))
    (hm : ∀ a : Word, ¬ (l1.toNat ≤ a.toNat ∧ a.toNat < h1.toNat) →
      ¬ (l2.toNat ≤ a.toNat ∧ a.toNat < h2.toNat) →
      ¬ (l3.toNat ≤ a.toNat ∧ a.toNat < h3.toNat) → m' a = m a) :
    WorldTJ Rg g m' := by
  obtain ⟨_, _⟩ := h.blk_bounds b1
  obtain ⟨_, _⟩ := h.blk_bounds b2
  obtain ⟨_, _⟩ := h.blk_bounds b3
  let mA : Word → Option (PanValue Word) := fun a =>
    if l1.toNat ≤ a.toNat ∧ a.toNat < h1.toNat then m' a else m a
  let mB : Word → Option (PanValue Word) := fun a =>
    if l2.toNat ≤ a.toNat ∧ a.toNat < h2.toNat then m' a else mA a
  have hA : WorldTJ Rg g mA := h.write_free b1 (fun a _ hn _ => if_neg hn)
    (fun a ha => if_neg (by omega)) c1
  have hB : WorldTJ Rg g mB := hA.write_free b2 (fun a _ hn _ => if_neg hn)
    (fun a ha => if_neg (by omega)) c2
  have key : ∀ a : Word, ¬ (l3.toNat ≤ a.toNat ∧ a.toNat < h3.toNat) → m' a = mB a := by
    intro a n3
    by_cases k2 : l2.toNat ≤ a.toNat ∧ a.toNat < h2.toNat
    · exact (if_pos k2).symm
    · rw [show mB a = mA a from if_neg k2]
      by_cases k1 : l1.toNat ≤ a.toNat ∧ a.toNat < h1.toNat
      · exact (if_pos k1).symm
      · rw [show mA a = m a from if_neg k1]
        exact hm a k1 k2 n3
  exact hB.write_free b3 (fun a _ hn _ => key a hn) (fun a ha => key a (by omega)) c3

end world

/-- A buffer of `n` bytes at `x` inside a registered free range without protected cells. -/
def KBuf (Rg : Reg) (x : Word) (n : Nat) : Prop :=
  ∃ lo hi, Rg.B lo hi ∧ lo.toNat % 8 = 0 ∧ lo.toNat ≤ x.toNat ∧ x.toNat + n ≤ hi.toNat ∧
    ∀ c w, Rg.Cn c w → ¬ (lo.toNat ≤ c.toNat ∧ c.toNat < hi.toNat)

/-- The hashing buffers are registered. -/
def KPre (Rg : Reg) (g : VarName → Option (PanValue Word)) : Prop :=
  ∃ stp pad hs, g "keccak_st" = some (.word stp) ∧ g "keccak_pad" = some (.word pad) ∧
    g "mpt_hash_scratch" = some (.word hs) ∧ KBuf Rg stp 200 ∧ KBuf Rg pad 136 ∧ KBuf Rg hs 32

/-- What the allocation of a nibble array gives. -/
def NkT (Rg : Reg) (s : St σ) (r : Result σ) : Prop :=
  ∃ l g m nb nl, r = .returned l g m s.ffi [.rStruct [.word nb, .word nl]] ∧
    WorldTJ (Rg.addIm nb (nb + nl)) g m ∧ (nb + nl).toNat = nb.toNat + nl.toNat ∧
    (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m addr = s.memory addr

set_option maxHeartbeats 4000000 in
/-- `var x = alloc(n); key_to_nibbles(src, cnt, x); return <x, n>` with `n = 2 * cnt`. -/
theorem nk_tail (hE : GuestEnv E) {x : VarName} {en esrc ecnt eret : Exp Word}
    {Rg : Reg} {src cnt nW : Word} (hW : WorldTJ Rg s.globals s.memory)
    (hen : E.eval s en = some (.word nW)) (hnW : nW.toNat = 2 * cnt.toNat)
    (hsrc : ∀ pv qv : Word, E.eval ⟨updatePanValueMap s.locals x (.word pv),
      updatePanValueMap s.globals "heap_ptr" (.word qv), s.memory, s.ffi⟩ esrc =
        some (.word src))
    (hcnt : ∀ pv qv : Word, E.eval ⟨updatePanValueMap s.locals x (.word pv),
      updatePanValueMap s.globals "heap_ptr" (.word qv), s.memory, s.ffi⟩ ecnt =
        some (.word cnt))
    (hret : ∀ (pv qv : Word) (m : Word → Option (PanValue Word)),
      E.eval ⟨updatePanValueMap s.locals x (.word pv),
        updatePanValueMap s.globals "heap_ptr" (.word qv), m, s.ffi⟩ eret = some (.word nW)) :
    WPs E s (.decCall x .one "alloc" [en]
      (.seq (.call (some (none, none)) "key_to_nibbles" [esrc, ecnt, .var .local x])
        (.return (.rStruct [.var .local x, eret])))) (NkT Rg s) := by
  obtain ⟨pv, hp, hpH, hpB⟩ : ∃ pv, s.globals "heap_ptr" = some (.word pv) ∧ InHeap pv ∧
      HBASE ≤ pv.toNat := by
    obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, -⟩ := hW
    have := hHW.jrn.lo
    have := hHW.jrn.hi
    exact ⟨pv, hp, hpH, by omega⟩
  have hpE := hpH.1
  have hp8 := hpH.2
  refine WPs.decCall_alloc hE (pv := pv) (nv := nW) hen hp hpH (fun qv hq hqH => ?_)
  have hqE := hqH.1
  refine WPs.seq_call_ret (fun vs g m2 ffi hcall => ?_)
  obtain ⟨rfl, rfl, hnib, hfr⟩ := key_to_nibbles_ret hE hcall (kw := src) (nw := cnt)
    (ow0 := pv) (hsrc pv qv) (hcnt pv qv) (by lk []) (by omega)
  dsimp only at hfr ⊢
  have e2 : (pv + nW).toNat = pv.toNat + nW.toNat := by
    rw [BitVec.toNat_add]
    omega
  refine WPs.ret_pair (a := pv) (b := nW) (of_eval (by lk [])) (of_eval (hret pv qv m2)) ?_
  simp only [restorePanValueFfiLocal]
  refine ⟨_, _, m2, pv, nW, rfl, WorldTJ.fresh_nibs hW hp (by simp [updatePanValueMap]) hqH
    (by omega) (fun y hy => by simp [update_lookup, hy])
    (fun A h8 hlt => hfr A (Or.inl (by omega)))
    (fun A hA => hfr A (by omega)) (by omega)
    (by rw [e2, hnW, Nat.add_sub_cancel_left]; exact hnib), e2,
    fun y hy => by simp [update_lookup, hy], fun A hA => hfr A (by omega)⟩

/-- What `mpt_nibble_key` guarantees. -/
def NkQ (Rg : Reg) (s : St σ) (r : Result σ) : Prop :=
  ∃ l g m nb nl R', r = .returned l g m s.ffi [.rStruct [.word nb, .word nl]] ∧ Rg.Le R' ∧
    WorldTJ R' g m ∧
    (nl ≠ 0#64 → ∃ lo hi, R'.Im lo hi ∧ lo.toNat ≤ nb.toNat ∧
      nb.toNat + nl.toNat ≤ hi.toNat) ∧
    (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m addr = s.memory addr

set_option maxHeartbeats 4000000 in
theorem mpt_nibble_key_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "mpt_nibble_key" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (mv kv kl : Word)
    (hm : s.locals "m" = some (.word mv)) (hk : s.locals "key" = some (.word kv))
    (hl : s.locals "klen" = some (.word kl)) (hkl : kl.toNat < 2 ^ 32)
    (hW : WorldTJ Rg s.globals s.memory) (hPre : KPre Rg s.globals) (h : Runs E s body r) :
    Stopped r ∨ NkQ Rg s r := by
  have hbody := (fun_of_index 270 hE.functions (by guest_decl_at 270) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (NkQ Rg s)) r h
  obtain ⟨stp, pad, hs, hst, hpd, hhs, ⟨l1, h1, b1, a1, lo1, hi1, c1⟩,
    ⟨l2, h2, b2, a2, lo2, hi2, c2⟩, ⟨l3, h3, b3, a3, lo3, hi3, c3⟩⟩ := hPre
  obtain ⟨_, _⟩ := hW.blk_bounds b1
  obtain ⟨_, _⟩ := hW.blk_bounds b2
  obtain ⟨_, _⟩ := hW.blk_bounds b3
  refine WPs.seqG (fun a => a = s) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
      obtain ⟨rfl, rfl, hfr⟩ := keccak256_ret hE hret (pv := kv) (nv := kl) (ov := hs)
        (stp := stp) (pad := pad) (by lk [hk]) (by lk [hl]) (by rw [eval_global]; exact hhs)
        hst hpd (by omega) (by omega) (by omega) (by omega)
      have hW1 : WorldTJ Rg s.globals m1 := hW.write_free3 b1 b2 b3 c1 c2 c3
        (fun a n1 n2 n3 => hfr a (by unfold KOut; omega))
      refine WPs.conseq (Q' := NkT Rg ⟨s.locals, s.globals, m1, s.ffi⟩)
        (nk_tail hE (src := hs) (cnt := 32#64) (nW := 64#64) hW1 (eval_const _ _) (by decide)
          (fun pv qv => by lk [hhs]) (fun pv qv => eval_const _ _)
          (fun pv qv m => eval_const _ _)) ?_
      rintro r ⟨l, g, m, nb, nl, rfl, hWn, e2, hg, hmo⟩
      exact ⟨l, g, m, nb, nl, _, rfl, Reg.Le.addIm _ _ _, hWn,
        fun _ => ⟨nb, nb + nl, Or.inr ⟨rfl, rfl⟩, Nat.le_refl _, by omega⟩, hg,
        fun addr ha => (hmo addr ha).trans (hfr addr (by unfold KOut; omega))⟩
  intro a ha
  rw [ha]
  have emul : (2#64 * kl).toNat = 2 * kl.toNat := by
    rw [BitVec.toNat_mul]
    have : (2#64 : Word).toNat = 2 := by decide
    rw [this]
    omega
  refine WPs.conseq (Q' := NkT Rg s)
    (nk_tail hE (src := kv) (cnt := kl) (nW := 2#64 * kl) hW (by ev [hl]) emul
      (fun pv qv => by lk [hk]) (fun pv qv => by lk [hl]) (fun pv qv m => by ev [hl])) ?_
  rintro r ⟨l, g, m, nb, nl, rfl, hWn, e2, hg, hmo⟩
  exact ⟨l, g, m, nb, nl, _, rfl, Reg.Le.addIm _ _ _, hWn,
    fun _ => ⟨nb, nb + nl, Or.inr ⟨rfl, rfl⟩, Nat.le_refl _, by omega⟩, hg, hmo⟩

/-- The interface of `mpt_set` holds with the hashing buffers registered. -/
theorem nibKeySpec (hE : GuestEnv E) : NibKeySpec E KPre := by
  intro Rg s e1 e2 e3 mv kv kl v g m ffi hret h1 h2 h3 hkl hW hPre
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := hret
  have hparams := (fun_of_index 270 hE.functions (by guest_decl_at 270) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some, Option.some.injEq]
    at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases mpt_nibble_key_world hE parameters body hlookup Rg ⟨cl, s.globals, s.memory, s.ffi⟩ _
    mv kv kl
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hkl hW hPre hrun with hst | ⟨l', g', m', nb, nl, R', heq, hle, hW', hblk, hg, hmo⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨nb, nl, R', rfl, rfl, hle, hW', hblk, hg, hmo⟩

end InitECandidate.Solver.GuestBound
