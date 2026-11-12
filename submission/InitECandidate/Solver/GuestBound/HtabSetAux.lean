import InitECandidate.Solver.GuestBound.HtabSetCalls

/-!
# Hash tables: helper facts for `htab_set`
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The test `HT_BIT(key, x) == 0` for a bit index held in the local `x`. -/
def htBitZeroV (x : VarName) : Exp Word :=
  .cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local "key",
    .shift .lsr (.var .local x) (.const 3#64)]))
    (.op .sub [.const 7#64, .op .and [.var .local x, .const 7#64]]), .const 1#64])
    (.const 0#64)

theorem htbit_cond_v (hE : GuestEnv E) (xn : VarName) {s : St σ} {kp bv : Word} {bit : Bool}
    (hkey : s.locals "key" = some (.word kp)) (hb : s.locals xn = some (.word bv))
    (hbit : KeyBitIs E.bytesInWord s.memory kp bv bit) {x : PanValue Word}
    (h : E.eval s (htBitZeroV xn) = some x) : x = .word (if bit then 0#64 else 1#64) := by
  unfold htBitZeroV at h
  cases hlb : E.eval s (.loadByte (.op .add [.var .local "key",
      .shift .lsr (.var .local xn) (.const 3#64)])) with
  | none =>
    simp [evalF_cmp hE.word, evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_shift hE.word,
      hlb] at h
  | some y =>
    obtain ⟨addr, cell, ha, hcell, rfl⟩ := eval_loadByte hE.mem hlb
    have hand : ∀ a b : Word, AndOp.and a b = a &&& b := fun _ _ => rfl
    have hones : ∀ a : Word, a &&& 18446744073709551615#64 = a := by intro a; bv_decide
    cases hs1 : RiscV.panRiscVShift .lsr bv 3#64 with
    | none =>
      simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_shift hE.word, evalF_local, hb,
        hkey, hs1] at ha
    | some a =>
      simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_shift hE.word, evalF_local, hb,
        hkey, hs1, wordsProj_cons, wordsProj_nil, wordOp] at ha
      subst ha
      cases hs2 : RiscV.panRiscVShift .lsr (RiscV.panRiscVGetByte E.bytesInWord (kp + a) cell)
          (7#64 - (bv &&& 7#64)) with
      | none =>
        simp [evalF_cmp hE.word, evalF_op hE.word, evalArgs_cons, evalArgs_nil,
          evalF_shift hE.word, hlb, evalF_local, hb, wordsProj_cons, wordsProj_nil, wordOp, hand,
          hones, hs2] at h
      | some y =>
        have hy := hbit a cell y hs1 hcell hs2
        simp [evalF_cmp hE.word, evalF_op hE.word, evalArgs_cons, evalArgs_nil,
          evalF_shift hE.word, hlb, evalF_local, hb, wordsProj_cons, wordsProj_nil, wordOp, hand,
          hones, hs2, evalPanCmp] at h
        subst h
        cases bit <;> simp at hy <;> simp [hy]

/-- A key bit known through `KeyBitIs` is the bit of the byte read. -/
theorem KeyBitIs.bit_eq {M : Word → Option (PanValue Word)} {kp j x : Word} {bit : Bool}
    (h : KeyBitIs 8#64 M kp j bit) (hx : byteAt M (kp + (j >>> (3 : Nat))) = some x) :
    bit = bitOf x (j.toNat % 8) := by
  unfold byteAt at hx
  cases hc : M (al8 (kp + (j >>> (3 : Nat)))) with
  | none => rw [hc] at hx; cases hx
  | some pv =>
    cases pv with
    | word cell =>
      rw [hc] at hx
      simp only [Option.some.injEq] at hx
      have hsh : (7#64 - (j &&& 7#64)).toNat = 7 - j.toNat % 8 := by
        have h7 : (7#64 : Word).toNat = 7 := by decide
        rw [BitVec.toNat_sub, h7, and7_toNat]
        omega
      have hs1 : RiscV.panRiscVShift .lsr j 3#64 = some (j >>> (3 : Nat)) := by
        unfold RiscV.panRiscVShift
        rfl
      have hs2 : RiscV.panRiscVShift .lsr (RiscV.panRiscVGetByte 8#64 (kp + (j >>> (3 : Nat))) cell)
          (7#64 - (j &&& 7#64)) = some (x >>> (7 - j.toNat % 8)) := by
        unfold RiscV.panRiscVShift
        rw [if_pos (by rw [hsh]; omega), hsh, ← hx]
      have hy := h _ cell _ hs1 hc hs2
      unfold bitOf
      by_cases hb1 : x.getLsbD (7 - j.toNat % 8) = true
      · have hne := (and_one_ne_zero _ _).mpr hb1
        rw [hb1]
        cases bit with
        | true => rfl
        | false => simp [hne] at hy
      · have hz : (x >>> (7 - j.toNat % 8)) &&& 1#64 = 0#64 := by
          by_contra hne
          exact hb1 ((and_one_ne_zero _ _).mp hne)
        have hf : x.getLsbD (7 - j.toNat % 8) = false := by simpa using hb1
        rw [hf]
        rw [hz] at hy
        cases bit with
        | true => simp at hy
        | false => rfl
    | _ => rw [hc] at hx; cases hx

variable {m : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

/-- A node agrees with each of its ancestors on the bits before the ancestor's. -/
theorem anc_rep (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {a c : Nat}
    (h : Anc m v a c) : LiveN v kind c → ∀ ba, Rd m (nodeField v a 24) ba →
      ∀ j : Word, j.toNat < ba.toNat → rep c j = rep a j := by
  induction h with
  | refl => intro _ _ _ _ _; rfl
  | @up c p hp hp0 hanc ih =>
    intro hc ba hba j hj
    obtain ⟨p', hp', hpar⟩ := live_parent hwf hc
    have := Rd.inj hp' hp
    subst this
    obtain ⟨hlive, hkind, bp, l', r', hbp, hl', hr', hside, hrl, hrr, hagree, hup⟩ :=
      parent_internal hwf hk hc.2.1 hpar hp0
    have hle : ba.toNat ≤ bp.toNat := by
      by_cases hap : a = p'.toNat
      · subst hap
        rw [Rd.inj hba hbp]
      · have hai := anc_internal hwf hk hanc hlive hap
        obtain ⟨_, la, ra, _, -, hla, hra, -⟩ := hwf.internal_ok a hai.1.1 hai.1.2.1 hai.2
        have := (anc_child hwf hk hanc hlive hap ba la ra bp hba hla hra hbp).1
        omega
    rw [hagree j (by omega)]
    exact ih hlive ba hba j hj

/-- A loop whose body keeps an invariant, breaks, or leaves with `Q`. -/
theorem WPs.loopB {I : St σ → Prop} {c : Exp Word} {body : Prog Word} (hinit : I s)
    (hbody : ∀ a, I a → CondTrue E a c → WPs E a body (fun r => match r with
      | .normal l g m f | .continued l g m f => I ⟨l, g, m, f⟩
      | .broke l g m f => Q (.normal l g m f)
      | r => Q r))
    (hexit : ∀ a k, I a → E.cond a c = some (0, k) →
      Q (.normal a.locals a.globals a.memory a.ffi)) :
    WPs E s (.while c body) Q := by
  intro r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  refine while_inv (I := I) (Q := fun r => Stopped r ∨ Q r)
    (fun r hr => Or.inl (Stopped.of_error hr)) (fun a k hI hc => Or.inr (hexit a k hI hc)) ?_
    fuel s r n hinit hrun
  intro fuel' a r' n' hI hct hrun'
  rcases hbody a hI hct r' (Runs.of_run hrun') with hst | hpost
  · cases r' with
    | error l g m f => exact Or.inl trivial
    | raised l g m f ex val => exact Or.inl trivial
    | finalFfi l g m f ev => exact Or.inl trivial
    | _ => exact absurd hst (fun h => h)
  · cases r' with
    | normal l g m f => exact hpost
    | continued l g m f => exact hpost
    | broke l g m f => exact Or.inr hpost
    | _ => exact Or.inr hpost

/-- The address of a node field, with the node block read from the header. -/
theorem eval_node_ld (hE : GuestEnv E) {t : Word} {v : HtabV} (hlay : HtabLayout t v)
    {idx : VarName} {iv : Word} (hi : iv.toNat ≤ v.nc.toNat)
    (ht : s.locals "t" = some (.word t)) (hnd : Rd s.memory (t + 40#64) v.nodes)
    (hidx : s.locals idx = some (.word iv)) (off : Word) (hoff : off.toNat < 32) :
    ∀ y, E.eval s (.op .add [.load .one (.op .add [.var .local "t", .const 40#64]),
      .panOp .mul [.var .local idx, .const 32#64], .const off]) = some y →
      y = .word (nodeField v iv.toNat off.toNat) := by
  intro y hy
  rw [← nodeField_eq hlay hi off hoff]
  cases hl : E.eval s (.load .one (.op .add [.var .local "t", .const 40#64])) with
  | none =>
    simp [evalF_op hE.word, evalArgs_cons, hl] at hy
  | some x =>
    have := eval_load_rd hE (eval_addc hE 40#64 ht) hnd x hl
    subst this
    simp (config := { decide := true }) [evalF_op hE.word, evalF_panOp, evalArgs_cons,
      evalArgs_nil, evalF_local, hl, hidx, wordsProj_cons, wordsProj_nil, wordOp, evalPanOp,
      BitVec.add_assoc] at hy
    exact hy.symm

end InitECandidate.Solver.GuestBound
