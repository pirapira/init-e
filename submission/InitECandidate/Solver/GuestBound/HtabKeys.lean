import InitECandidate.Solver.GuestBound.HtabFind

/-!
# Hash tables: the crit-bit order

`HtabKeys` adds the key order to the structural invariant `HtabWF`: every
internal node tests a bit on which its two subtrees differ and on whose
earlier bits they agree, and bit indices grow towards the leaves. From it,
the root is an ancestor of every live node, and the descent for a stored key
stays on the ancestors of its leaf.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Ghost key bits: `rep i j` is bit `j` of some key below node `i`. -/
abbrev KeyRep := Nat → Word → Bool

/-- The crit-bit order of a table. -/
structure HtabKeys (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind)
    (rep : KeyRep) : Prop where
  internal_bits : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .internal →
    ∀ b l r : Word, Rd m (nodeField v i 24) b → Rd m (nodeField v i 8) l →
      Rd m (nodeField v i 16) r →
      b.toNat < (v.kl * 8#64).toNat ∧ rep l.toNat b = false ∧ rep r.toNat b = true ∧
      (∀ j : Word, j.toNat < b.toNat → rep l.toNat j = rep i j ∧ rep r.toNat j = rep i j) ∧
      (∀ bl, Rd m (nodeField v l.toNat 24) bl → b.toNat < bl.toNat) ∧
      (∀ br, Rd m (nodeField v r.toNat 24) br → b.toNat < br.toNat)

/-- A node index handed out and not on the free list. -/
def LiveN (v : HtabV) (kind : Nat → NodeKind) (i : Nat) : Prop :=
  1 ≤ i ∧ i < v.next.toNat ∧ kind i ≠ .free

/-- `Anc a c`: following parent fields from `c` reaches `a`. -/
inductive Anc (m : Word → Option (PanValue Word)) (v : HtabV) : Nat → Nat → Prop
  | refl (c : Nat) : Anc m v c c
  | up {a c : Nat} (p : Word) : Rd m (nodeField v c 0) p → p ≠ 0 → Anc m v a p.toNat →
      Anc m v a c

variable {m : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

theorem live_bit (hwf : HtabWF m t v kind) {i : Nat} (h : LiveN v kind i) :
    ∃ b, Rd m (nodeField v i 24) b := by
  obtain ⟨h1, h2, h3⟩ := h
  cases hk : kind i with
  | free => exact absurd hk h3
  | leaf =>
    obtain ⟨_, _, _, -, -, -, hb, -⟩ := hwf.leaf_ok i h1 h2 hk
    exact ⟨_, hb⟩
  | internal =>
    obtain ⟨_, _, _, b, -, -, -, hb, -⟩ := hwf.internal_ok i h1 h2 hk
    exact ⟨b, hb⟩

theorem live_parent (hwf : HtabWF m t v kind) {i : Nat} (h : LiveN v kind i) :
    ∃ p, Rd m (nodeField v i 0) p ∧ ParentOk m v kind i p := by
  obtain ⟨h1, h2, h3⟩ := h
  cases hk : kind i with
  | free => exact absurd hk h3
  | leaf =>
    obtain ⟨p, _, _, hp, -, -, -, hpar, -⟩ := hwf.leaf_ok i h1 h2 hk
    exact ⟨p, hp, hpar⟩
  | internal =>
    obtain ⟨p, _, _, _, hp, -, -, -, -, hpar, -⟩ := hwf.internal_ok i h1 h2 hk
    exact ⟨p, hp, hpar⟩

/-- The parent of a live node below the root: a live internal node testing an
earlier bit, with the node as one of its children. -/
theorem parent_internal (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {i : Nat}
    (hi : i < v.next.toNat) {p : Word} (hpar : ParentOk m v kind i p) (hp0 : p ≠ 0) :
    LiveN v kind p.toNat ∧ kind p.toNat = .internal ∧
      ∃ b l r : Word, Rd m (nodeField v p.toNat 24) b ∧ Rd m (nodeField v p.toNat 8) l ∧
        Rd m (nodeField v p.toNat 16) r ∧ (l.toNat = i ∨ r.toNat = i) ∧
        rep l.toNat b = false ∧ rep r.toNat b = true ∧
        (∀ j : Word, j.toNat < b.toNat → rep i j = rep p.toNat j) ∧
        (∀ bi, Rd m (nodeField v i 24) bi → b.toNat < bi.toNat) := by
  rcases hpar with ⟨h0, -⟩ | ⟨h1, h2, hkind, hchild⟩
  · exact absurd h0 hp0
  obtain ⟨_, l, r, b, -, hl, hr, hb, -⟩ := hwf.internal_ok _ h1 h2 hkind
  obtain ⟨-, hrl, hrr, hagree, hbl, hbr⟩ := hk.internal_bits _ h1 h2 hkind b l r hb hl hr
  have hi64 : i < 2 ^ 64 := by have := v.next.isLt; omega
  have hside : l.toNat = i ∨ r.toNat = i := by
    rcases hchild with hc | hc
    · left
      rw [Rd.inj hl hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
    · right
      rw [Rd.inj hr hc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64]
  refine ⟨⟨h1, h2, by rw [hkind]; exact NodeKind.noConfusion⟩, hkind, b, l, r, hb, hl, hr,
    hside, hrl, hrr, ?_, ?_⟩
  · intro j hj
    rcases hside with rfl | rfl
    · exact (hagree j hj).1
    · exact (hagree j hj).2
  · intro bi hbi
    rcases hside with rfl | rfl
    · exact hbl bi hbi
    · exact hbr bi hbi

/-- The root is an ancestor of every live node. -/
theorem root_anc (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) :
    ∀ (n c : Nat) (b : Word), LiveN v kind c → Rd m (nodeField v c 24) b → b.toNat < n →
      Anc m v v.root.toNat c := by
  intro n
  induction n with
  | zero => intro c b _ _ h; omega
  | succ n ih =>
    intro c b hc hb hlt
    obtain ⟨p, hp, hpar⟩ := live_parent hwf hc
    by_cases hp0 : p = 0
    · rcases hpar with ⟨-, hroot⟩ | ⟨h1, -⟩
      · rw [hroot]
        exact .refl c
      · rw [hp0] at h1
        exact absurd h1 (by decide)
    · obtain ⟨hlive, -, bp, _, _, hbp, -, -, -, -, -, -, hup⟩ :=
        parent_internal hwf hk hc.2.1 hpar hp0
      have := hup b hb
      exact .up p hp hp0 (ih p.toNat bp hlive hbp (by omega))

/-- A strict ancestor of a live node is a live internal node. -/
theorem anc_internal (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {a c : Nat}
    (h : Anc m v a c) : LiveN v kind c → a ≠ c → LiveN v kind a ∧ kind a = .internal := by
  induction h with
  | refl => intro _ hne; exact absurd rfl hne
  | @up c p hp hp0 _ ih =>
    intro hc _
    obtain ⟨p', hp', hpar⟩ := live_parent hwf hc
    have := Rd.inj hp' hp
    subst this
    obtain ⟨hlive, hkind, -⟩ := parent_internal hwf hk hc.2.1 hpar hp0
    by_cases hap : a = p'.toNat
    · subst hap
      exact ⟨hlive, hkind⟩
    · exact ih hlive hap

/-- Below a strict ancestor `a` of `c`, the child on the side of `c`'s bit at
`a` is again an ancestor of `c`. -/
theorem anc_child (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {a c : Nat}
    (h : Anc m v a c) : LiveN v kind c → a ≠ c →
      ∀ ba l r bc : Word, Rd m (nodeField v a 24) ba → Rd m (nodeField v a 8) l →
        Rd m (nodeField v a 16) r → Rd m (nodeField v c 24) bc →
        ba.toNat < bc.toNat ∧ (rep c ba = false → Anc m v l.toNat c) ∧
          (rep c ba = true → Anc m v r.toNat c) := by
  induction h with
  | refl => intro _ hne; exact absurd rfl hne
  | @up c p hp hp0 hanc ih =>
    intro hc _ ba l r bc hba hl hr hbc
    obtain ⟨p', hp', hpar⟩ := live_parent hwf hc
    have := Rd.inj hp' hp
    subst this
    obtain ⟨hlive, -, bp, l', r', hbp, hl', hr', hside, hrl, hrr, hagree, hup⟩ :=
      parent_internal hwf hk hc.2.1 hpar hp0
    have hlt := hup bc hbc
    by_cases hap : a = p'.toNat
    · subst hap
      have e1 := Rd.inj hba hbp
      have e2 := Rd.inj hl hl'
      have e3 := Rd.inj hr hr'
      subst e1 e2 e3
      refine ⟨hlt, ?_, ?_⟩
      · intro hf
        rcases hside with rfl | rfl
        · exact .refl _
        · rw [hrr] at hf
          cases hf
      · intro hf
        rcases hside with rfl | rfl
        · rw [hrl] at hf
          cases hf
        · exact .refl _
    · obtain ⟨hlt', hleft, hright⟩ := ih hlive hap ba l r bp hba hl hr hbp
      have hrep : rep c ba = rep p'.toNat ba := hagree ba hlt'
      refine ⟨by omega, ?_, ?_⟩
      · intro hf
        exact .up p' hp hp0 (hleft (hrep ▸ hf))
      · intro hf
        exact .up p' hp hp0 (hright (hrep ▸ hf))

variable {σ : Type} {E : Env σ}

/-- Bit `j` of the key at `kp` is `bit`, read the way `HT_BIT` reads it. -/
def KeyBitIs (bw : Word) (m : Word → Option (PanValue Word)) (kp j : Word) (bit : Bool) :
    Prop :=
  ∀ a cell y, RiscV.panRiscVShift .lsr j 3#64 = some a →
    m (RiscV.panRiscVByteAlign bw (kp + a)) = some (.word cell) →
    RiscV.panRiscVShift .lsr (RiscV.panRiscVGetByte bw (kp + a) cell) (7#64 - (j &&& 7#64)) =
      some y →
    ((y &&& 1#64) == 0#64) = !bit

/-- The test `HT_BIT(key, b) == 0`. -/
def htBitZero : Exp Word :=
  .cmp .equal (.op .and [.shift .lsr (.loadByte (.op .add [.var .local "key",
    .shift .lsr (.var .local "b") (.const 3#64)]))
    (.op .sub [.const 7#64, .op .and [.var .local "b", .const 7#64]]), .const 1#64])
    (.const 0#64)

theorem htbit_cond (hE : GuestEnv E) {s : St σ} {kp bv : Word} {bit : Bool}
    (hkey : s.locals "key" = some (.word kp)) (hb : s.locals "b" = some (.word bv))
    (hbit : KeyBitIs E.bytesInWord s.memory kp bv bit) {x : PanValue Word}
    (h : E.eval s htBitZero = some x) : x = .word (if bit then 0#64 else 1#64) := by
  unfold htBitZero at h
  cases hlb : E.eval s (.loadByte (.op .add [.var .local "key",
      .shift .lsr (.var .local "b") (.const 3#64)])) with
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

/-- Loop invariant of the descent for the key of leaf `L`. -/
def SelfI (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (v : HtabV) (kind : Nat → NodeKind) (kp : Word) (L : Nat) (s : St σ) :
    Prop :=
  s.globals = g ∧ s.memory = m ∧ s.ffi = f ∧
    s.locals "keybits" = some (.word (v.kl * 8#64)) ∧
    s.locals "nodes" = some (.word v.nodes) ∧ s.locals "key" = some (.word kp) ∧
    ∃ nv, s.locals "n" = some (.word nv) ∧ LiveN v kind nv.toNat ∧ Anc m v nv.toNat L

/-- Exit condition of that descent: `n` is the leaf. -/
def SelfQ (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (Lw : Word) (r : Result σ) : Prop :=
  r.isError = true ∨ ∃ l, r = .normal l g m f ∧ l "n" = some (.word Lw)

/-- One step of the descent for a stored key stays on the ancestors of its leaf. -/
theorem self_body (hE : GuestEnv E) {g : VarName → Option (PanValue Word)} {f : FfiState σ}
    (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {kp Lw : Word}
    (hL : LiveN v kind Lw.toNat) (hLk : kind Lw.toNat = .leaf)
    (hkey : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs E.bytesInWord m kp j (rep Lw.toNat j))
    (s : St σ) (r : Result σ) (hI : SelfI g m f v kind kp Lw.toNat s)
    (h : Runs E s
      (.dec "b" .one (.load .one (.op .add [.var .local "nodes",
          .panOp .mul [.var .local "n", .const 32#64], .const 24#64]))
        (.seq (.ite (.cmp .equal (.var .local "b") (.var .local "keybits")) .break .skip)
          (.ite htBitZero
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const 8#64])))
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const 16#64])))))) r) :
    BodyInv (SelfI g m f v kind kp Lw.toNat) (SelfQ g m f Lw) r := by
  obtain ⟨rfl, rfl, rfl, hkb, hnodes, hkp, nv, hn, hl, hanc⟩ := hI
  rw [runs_dec] at h
  cases he : E.eval s (.load .one (.op .add [.var .local "nodes",
      .panOp .mul [.var .local "n", .const 32#64], .const 24#64])) with
  | none =>
    rw [he] at h
    simp only at h
    subst h
    exact Or.inl rfl
  | some x =>
    obtain ⟨bv, rfl, hb⟩ := eval_field hE hwf hl.2.1 hnodes hn 24#64 (by decide) he
    rw [he] at h
    simp only [shape_word, shape_matches_self, if_true] at h
    obtain ⟨rb, hrb, rfl⟩ := h
    obtain ⟨r1, h1, hrest⟩ := runs_seq.mp hrb
    rw [runs_ite] at h1
    simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      hkb, if_true, if_false] at h1
    cases hkd : kind nv.toNat with
    | free => exact absurd hkd hl.2.2
    | leaf =>
      obtain ⟨p, value, pos, -, -, -, hkdf, -⟩ := hwf.leaf_ok _ hl.1 hl.2.1 hkd
      have := Rd.inj hb hkdf
      subst this
      simp [evalPanCmp] at h1
      rw [runs_break] at h1
      subst h1
      simp only at hrest
      subst hrest
      have hnL : nv = Lw := by
        apply BitVec.eq_of_toNat_eq
        by_contra hne
        have := (anc_internal hwf hk hanc hL hne).2
        rw [hkd] at this
        cases this
      subst hnL
      refine Or.inr ⟨_, rfl, ?_⟩
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hn]
    | internal =>
      have hne : nv.toNat ≠ Lw.toNat := by
        intro heq
        rw [heq, hLk] at hkd
        cases hkd
      obtain ⟨p, lc, rc, b', -, hlc, hrc, hb', hbne, -, hcl, hcr, -⟩ :=
        hwf.internal_ok _ hl.1 hl.2.1 hkd
      have := Rd.inj hb hb'
      subst this
      obtain ⟨hblt, -⟩ := hk.internal_bits _ hl.1 hl.2.1 hkd bv lc rc hb hlc hrc
      obtain ⟨bL, hbL⟩ := live_bit hwf hL
      obtain ⟨-, hleft, hright⟩ := anc_child hwf hk hanc hL hne bv lc rc bL hb hlc hrc hbL
      simp [evalPanCmp, hbne] at h1
      rw [runs_skip] at h1
      subst h1
      simp only at hrest
      have hnodes' : (updatePanValueMap s.locals "b" (.word bv)) "nodes" =
          some (.word v.nodes) := by
        simp (config := { decide := true }) [update_lookup, hnodes]
      have hn' : (updatePanValueMap s.locals "b" (.word bv)) "n" = some (.word nv) := by
        simp (config := { decide := true }) [update_lookup, hn]
      have hkp' : (updatePanValueMap s.locals "b" (.word bv)) "key" = some (.word kp) := by
        simp (config := { decide := true }) [update_lookup, hkp]
      have hb'' : (updatePanValueMap s.locals "b" (.word bv)) "b" = some (.word bv) := by
        simp [update_lookup]
      have step : ∀ (off c : Word), off.toNat < 32 →
          Rd s.memory (nodeField v nv.toNat off.toNat) c → ChildOk s.memory v kind nv.toNat c →
          Anc s.memory v c.toNat Lw.toNat →
          Runs E ⟨updatePanValueMap s.locals "b" (.word bv), s.globals, s.memory, s.ffi⟩
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const off]))) rb →
          BodyInv (SelfI s.globals s.memory s.ffi v kind kp Lw.toNat)
            (SelfQ s.globals s.memory s.ffi Lw)
            (restorePanValueFfiLocal "b" (s.locals "b") rb) := by
        intro off c hoff hc hch hca hr
        rcases assign_field hE (s := ⟨updatePanValueMap s.locals "b" (.word bv), s.globals,
          s.memory, s.ffi⟩) hwf hl.2.1 hnodes' hn' off hoff hc hr with rfl | rfl
        · exact Or.inl rfl
        · refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, c, ?_, ⟨hch.1, hch.2.1, hch.2.2.1⟩, hca⟩
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hkb]
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hnodes]
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hkp]
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      rw [runs_ite] at hrest
      cases hcv : E.eval ⟨updatePanValueMap s.locals "b" (.word bv), s.globals, s.memory, s.ffi⟩
          htBitZero with
      | none =>
        rw [hcv] at hrest
        simp only at hrest
        subst hrest
        exact Or.inl rfl
      | some x =>
        have hx := htbit_cond hE (s := ⟨updatePanValueMap s.locals "b" (.word bv), s.globals,
          s.memory, s.ffi⟩) hkp' hb'' (hkey bv hblt) hcv
        subst hx
        rw [hcv] at hrest
        cases hbit : rep Lw.toNat bv with
        | false =>
          simp (config := { decide := true }) only [hbit, if_false, Bool.false_eq_true] at hrest
          exact step 8#64 lc (by decide) hlc hcl (hleft hbit) hrest
        | true =>
          simp (config := { decide := true }) only [hbit, if_true] at hrest
          exact step 16#64 rc (by decide) hrc hcr (hright hbit) hrest

/-- `htab_find_leaf(t, key)` for the stored key of a live leaf returns that leaf. -/
theorem htab_find_self_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_find_leaf" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t : Word) (v : HtabV) (kind : Nat → NodeKind) (rep : KeyRep)
    (kp Lw : Word) (ht : s.locals "t" = some (.word t)) (hkp : s.locals "key" = some (.word kp))
    (hwf : HtabWF s.memory t v kind) (hk : HtabKeys s.memory v kind rep)
    (hL : LiveN v kind Lw.toNat) (hLk : kind Lw.toNat = .leaf)
    (hkey : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs E.bytesInWord s.memory kp j (rep Lw.toNat j))
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l, r = .returned l s.globals s.memory s.ffi [.word Lw] := by
  have hbody := (fun_of_index 131 hE.functions (by guest_decl_at 131) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  obtain ⟨hkl, -, -, -, -, hnd, -, hroot, -⟩ := hwf.hdr
  rw [runs_dec] at h
  cases he : E.eval s (.panOp .mul [.load .one (.op .add [.var .local "t", .const 0#64]),
      .const 8#64]) with
  | none =>
    rw [he] at h
    simp only at h
    subst h
    exact Or.inl (Stopped.err s)
  | some x =>
    obtain ⟨va, vb, hload, hconst, rfl⟩ := eval_mul_inv he
    have := eval_hdr hE ht hkl hload
    simp only [PanValue.word.injEq] at this
    subst this
    simp only [eval_const, Option.some.injEq, PanValue.word.injEq] at hconst
    subst hconst
    rw [he] at h
    simp only [shape_word, shape_matches_self, if_true] at h
    obtain ⟨r1, h1, rfl⟩ := h
    rcases dec_load_hdr hE (t := t) (w := v.nodes)
      (s := ⟨updatePanValueMap s.locals "keybits" (.word (v.kl * 8#64)), s.globals, s.memory,
        s.ffi⟩)
      (by simp (config := { decide := true }) [update_lookup, ht]) hnd h1 with hst |
      ⟨r2, h2, rfl⟩
    · exact Or.inl hst.restore
    rcases dec_load_hdr hE (t := t) (w := v.root)
      (s := ⟨updatePanValueMap (updatePanValueMap s.locals "keybits" (.word (v.kl * 8#64)))
        "nodes" (.word v.nodes), s.globals, s.memory, s.ffi⟩)
      (by simp (config := { decide := true }) [update_lookup, ht]) hroot h2 with hst |
      ⟨r3, h3, rfl⟩
    · exact Or.inl hst.restore.restore
    obtain ⟨rl, hw, hrest⟩ := runs_seq.mp h3
    obtain ⟨fuel, n, hrun⟩ := hw
    obtain ⟨bL, hbL⟩ := live_bit hwf hL
    have hra : Anc s.memory v v.root.toNat Lw.toNat :=
      root_anc hwf hk (bL.toNat + 1) Lw.toNat bL hL hbL (by omega)
    have hrl : LiveN v kind v.root.toNat := by
      by_cases hne : v.root.toNat = Lw.toNat
      · rw [hne]
        exact hL
      · exact (anc_internal hwf hk hra hL hne).1
    have hQ : SelfQ s.globals s.memory s.ffi Lw rl := by
      refine while_inv (I := SelfI s.globals s.memory s.ffi v kind kp Lw.toNat)
        (Q := SelfQ s.globals s.memory s.ffi Lw) (fun r hr => Or.inl hr)
        ?_ ?_ fuel _ rl n ?_ hrun
      · rintro s' k ⟨hg, hm, hf, -, -, -, nv, hn, hlv, -⟩ hcond
        rw [cond_eq] at hcond
        simp [evalF_cmp hE.word, hn, evalPanCmp] at hcond
        have h1 := hlv.1
        rw [hcond.1] at h1
        exact absurd h1 (by decide)
      · intro fuel' s' r' n' hI _ hrun'
        exact self_body hE hwf hk hL hLk hkey s' r' hI (Runs.of_run hrun')
      · refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, v.root, ?_, hrl, hra⟩
        · simp (config := { decide := true }) [update_lookup]
        · simp (config := { decide := true }) [update_lookup]
        · simp (config := { decide := true }) [update_lookup, hkp]
        · simp (config := { decide := true }) [update_lookup]
    rcases hQ with herr | ⟨l, rfl, hn⟩
    · cases rl with
      | error l g m f =>
        simp only at hrest
        subst hrest
        exact Or.inl (Stopped.restore (Stopped.restore (Stopped.restore trivial)))
      | _ => cases herr
    · simp only at hrest
      rw [runs_return] at hrest
      simp only [evalF_local, hn, payload_word, if_true] at hrest
      subst hrest
      exact Or.inr ⟨_, rfl⟩

end InitECandidate.Solver.GuestBound
