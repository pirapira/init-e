import InitECandidate.Solver.GuestBound.TrieWalkDefs

/-!
# The witness decoder `_decode_witness_node_body`: stack, measure, interface

The decoder is a state machine over `mode` with an explicit stack of 88-byte
records in the scratch arena (`+0` parent record, `+8` kind: 1 extension, else
branch, `+16` the branch node, `+24` slice array, `+32` slot index, `+40`
occupancy, `+48/+56` the node's RLP, `+64/+72` the extension's nibbles,
`+80` hash of the child being resolved).

* mode 1: `_decode_step(db, cur_p, cur_n)` returns a finished node (a leaf or
  null; mode 0) or a fresh record (pushed; mode 2).
* mode 2: `_resolve_step` on a slice of the top record returns a finished
  child (null or a hash stub; mode 0) or the RLP of a child to decode (mode 1).
* mode 0: with an empty stack the loop ends; an extension record is popped
  and the extension created over `result`; a branch record stores `result`
  in its slot and either advances to the next slot (mode 2) or is popped.

`DStk R m lim sp top ℓ`: the records from `top` down, where `ℓ` is the level at
which the node currently being produced will sit (children are created before
their extension, so levels are fixed top-down by the stack).

The measure `dcMu` is read off the state: scratch pointer (a push lowers it,
nothing is released), address of the top record (a pop raises it), slot index
of the top record, mode, `go`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The records of the decoder, newest first; the node being produced sits at level `ℓ`,
the node of the oldest record at level `ℓ0`. -/
inductive DStk (R : Reg) (m : Word → Option (PanValue Word)) (lim ℓ0 : Nat) :
    Nat → Word → Nat → Prop
  | nil {sp : Nat} : DStk R m lim ℓ0 sp 0#64 ℓ0
  | ext {sp : Nat} {top prev seg sl : Word} {ℓ : Nat} :
      top ≠ 0#64 → top.toNat % 8 = 0 → sp ≤ top.toNat → top.toNat + 88 ≤ lim →
      Rd m top prev → Rd m (top + 8#64) 1#64 → Rd m (top + 64#64) seg →
      Rd m (top + 72#64) sl → 1 ≤ sl.toNat →
      (∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ seg.toNat ∧ seg.toNat + sl.toNat ≤ hi.toNat) →
      DStk R m lim ℓ0 (top.toNat + 88) prev ℓ → DStk R m lim ℓ0 sp top (ℓ + sl.toNat)
  | br {sp : Nat} {top prev kd b i : Word} {ℓ : Nat} :
      top ≠ 0#64 → top.toNat % 8 = 0 → sp ≤ top.toNat → top.toNat + 88 ≤ lim →
      Rd m top prev → Rd m (top + 8#64) kd → kd ≠ 1#64 → Rd m (top + 16#64) b →
      Rd m (top + 32#64) i → i.toNat < 16 → R.Kd b 3#64 → R.Lv b ℓ →
      DStk R m lim ℓ0 (top.toNat + 88) prev ℓ → DStk R m lim ℓ0 sp top (ℓ + 1)

theorem DStk.mono {R R' : Reg} {m : Word → Option (PanValue Word)} {lim ℓ0 sp : Nat}
    {top : Word} {ℓ : Nat} (hle : R.Le R') (h : DStk R m lim ℓ0 sp top ℓ) :
    DStk R' m lim ℓ0 sp top ℓ := by
  induction h with
  | nil => exact .nil
  | ext h1 h2 h3 h4 r0 r1 r2 r3 hs hi _ ih =>
    obtain ⟨lo, hi', hI, a1, a2⟩ := hi
    exact .ext h1 h2 h3 h4 r0 r1 r2 r3 hs ⟨lo, hi', hle.Im _ _ hI, a1, a2⟩ ih
  | br h1 h2 h3 h4 r0 r1 hk r2 r3 hi hK hL _ ih =>
    exact .br h1 h2 h3 h4 r0 r1 hk r2 r3 hi (hle.Kd _ _ hK) (hle.Lv _ _ hL) ih

theorem DStk.lower {R : Reg} {m : Word → Option (PanValue Word)} {lim ℓ0 sp sp' : Nat}
    {top : Word} {ℓ : Nat} (hsp : sp' ≤ sp) (h : DStk R m lim ℓ0 sp top ℓ) :
    DStk R m lim ℓ0 sp' top ℓ := by
  cases h with
  | nil => exact .nil
  | ext h1 h2 h3 h4 r0 r1 r2 r3 hs hi ht => exact .ext h1 h2 (by omega) h4 r0 r1 r2 r3 hs hi ht
  | br h1 h2 h3 h4 r0 r1 hk r2 r3 hi hK hL ht =>
    exact .br h1 h2 (by omega) h4 r0 r1 hk r2 r3 hi hK hL ht

/-- Offsets inside a decoder record. -/
theorem drec_off {top : Word} {lim : Nat} (hlim : lim < 2 ^ 64) (h : top.toNat + 88 ≤ lim)
    (c : Nat) (hc : c ≤ 80) : (top + BitVec.ofNat 64 c).toNat = top.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- The stack survives a change that leaves the cells from `sp` up to `lim` alone. -/
theorem DStk.frame {R : Reg} {m m' : Word → Option (PanValue Word)} {lim ℓ0 sp : Nat}
    {top : Word} {ℓ : Nat} (hlim : lim < 2 ^ 64)
    (hm : ∀ x : Word, sp ≤ x.toNat → x.toNat < lim → m' x = m x)
    (h : DStk R m lim ℓ0 sp top ℓ) : DStk R m' lim ℓ0 sp top ℓ := by
  induction h with
  | nil => exact .nil
  | @ext sp top prev seg sl ℓ h1 h2 h3 h4 r0 r1 r2 r3 hs hi _ ih =>
    have rd : ∀ (c : Nat) (w : Word), c ≤ 80 → Rd m (top + BitVec.ofNat 64 c) w →
        Rd m' (top + BitVec.ofNat 64 c) w := by
      intro c w hc hr
      have e := drec_off hlim h4 c hc
      unfold Rd at hr ⊢
      rw [hm _ (by omega) (by omega)]
      exact hr
    have r0' : Rd m' top prev := by
      unfold Rd at r0 ⊢
      rw [hm _ h3 (by omega)]
      exact r0
    exact .ext h1 h2 h3 h4 r0' (rd 8 _ (by omega) r1) (rd 64 _ (by omega) r2)
      (rd 72 _ (by omega) r3) hs hi (ih (fun x hx hx' => hm x (by omega) hx'))
  | @br sp top prev kd b i ℓ h1 h2 h3 h4 r0 r1 hk r2 r3 hi hK hL _ ih =>
    have rd : ∀ (c : Nat) (w : Word), c ≤ 80 → Rd m (top + BitVec.ofNat 64 c) w →
        Rd m' (top + BitVec.ofNat 64 c) w := by
      intro c w hc hr
      have e := drec_off hlim h4 c hc
      unfold Rd at hr ⊢
      rw [hm _ (by omega) (by omega)]
      exact hr
    have r0' : Rd m' top prev := by
      unfold Rd at r0 ⊢
      rw [hm _ h3 (by omega)]
      exact r0
    exact .br h1 h2 h3 h4 r0' (rd 8 _ (by omega) r1) hk (rd 16 _ (by omega) r2)
      (rd 32 _ (by omega) r3) hi hK hL (ih (fun x hx hx' => hm x (by omega) hx'))

/-- The empty stack produces at the entry level. -/
theorem DStk.zero {R : Reg} {m : Word → Option (PanValue Word)} {lim ℓ0 sp : Nat} {ℓ : Nat}
    (h : DStk R m lim ℓ0 sp 0#64 ℓ) : ℓ = ℓ0 := by
  cases h with
  | nil => rfl
  | ext h1 => exact absurd rfl h1
  | br h1 => exact absurd rfl h1

/-- A finished node at level `ℓ`: null, or registered there. -/
def DRes (R : Reg) (ℓ : Nat) (x : Word) : Prop := x = 0#64 ∨ ∃ k, R.Kd x k ∧ R.Lv x ℓ

/-- A record just returned by `_decode_step`, for a node at level `ℓ`
(its parent link is not written yet). -/
def DRecNew (R : Reg) (m : Word → Option (PanValue Word)) (q : Word) (ℓ : Nat) : Prop :=
  (Rd m (q + 8#64) 1#64 ∧ ∃ seg sl, Rd m (q + 64#64) seg ∧ Rd m (q + 72#64) sl ∧
      1 ≤ sl.toNat ∧
      ∃ lo hi, R.Im lo hi ∧ lo.toNat ≤ seg.toNat ∧ seg.toNat + sl.toNat ≤ hi.toNat) ∨
    ∃ kd b, Rd m (q + 8#64) kd ∧ kd ≠ 1#64 ∧ Rd m (q + 16#64) b ∧ R.Kd b 3#64 ∧ R.Lv b ℓ ∧
      Rd m (q + 32#64) 0#64

/-- What the decoder loop needs of `_decode_step` and `_resolve_step`.
`ℓ` is the level at which the node being produced will sit. -/
structure DecIface (E : Env σ) where
  /-- What decoding needs of the registry and the globals (the node database). -/
  Pre : Reg → (VarName → Option (PanValue Word)) → Prop
  pre_mono : ∀ {R R' : Reg} {g g' : VarName → Option (PanValue Word)}, Pre R g → R.Le R' →
    (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g' x = g x) → Pre R' g'
  decode : ∀ (R : Reg) (s : St σ) (e1 e2 e3 : Exp Word) (dbv pw nw sp fv : Word) (ℓ : Nat)
    (v : PanValue Word) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (ffi : FfiState σ),
    CalleeRet E s "_decode_step" [e1, e2, e3] [v] g m ffi →
    E.eval s e1 = some (.word dbv) → E.eval s e2 = some (.word pw) →
    E.eval s e3 = some (.word nw) →
    WorldTJ R s.globals s.memory → Pre R s.globals →
    s.globals "scratch_ptr" = some (.word sp) → s.globals "frame_mem_ptr" = some (.word fv) →
    fv.toNat ≤ sp.toNat → 2952790016 ≤ fv.toNat →
    ffi = s.ffi ∧ ∃ (R' : Reg) (d0 d1 sp' : Word), v = .rStruct [.word d0, .word d1] ∧
      R.Le R' ∧ WorldTJ R' g m ∧
      (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g x = s.globals x) ∧
      g "scratch_ptr" = some (.word sp') ∧ fv.toNat ≤ sp'.toNat ∧ sp'.toNat ≤ sp.toNat ∧
      (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
        m addr = s.memory addr) ∧
      (d0 = 0#64 → DRes R' ℓ d1) ∧
      (d0 ≠ 0#64 → sp' = d1 ∧ d1.toNat % 8 = 0 ∧ d1.toNat + 88 ≤ sp.toNat ∧ DRecNew R' m d1 ℓ)
  resolve : ∀ (R : Reg) (s : St σ) (e1 e2 e3 : Exp Word) (dbv pw nw sp fv : Word) (ℓ : Nat)
    (v : PanValue Word) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (ffi : FfiState σ),
    CalleeRet E s "_resolve_step" [e1, e2, e3] [v] g m ffi →
    E.eval s e1 = some (.word dbv) → E.eval s e2 = some (.word pw) →
    E.eval s e3 = some (.word nw) →
    WorldTJ R s.globals s.memory → Pre R s.globals →
    s.globals "scratch_ptr" = some (.word sp) → s.globals "frame_mem_ptr" = some (.word fv) →
    fv.toNat ≤ sp.toNat → 2952790016 ≤ fv.toNat →
    ffi = s.ffi ∧ ∃ (R' : Reg) (r0 r1 r2 r3 : Word),
      v = .rStruct [.word r0, .word r1, .word r2, .word r3] ∧
      R.Le R' ∧ WorldTJ R' g m ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
      (∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp.toNat ≤ addr.toNat) →
        m addr = s.memory addr) ∧
      (r0 = 0#64 → DRes R' ℓ r1)

/-- Distance of the top record from the end of the address space. -/
def tT (t : Word) : Nat := if t = 0#64 then 0 else 2 ^ 64 - t.toNat

/-- Slots left in the top record (meaningful for a branch record). -/
def icOf (m : Word → Option (PanValue Word)) (t : Word) : Nat :=
  if t = 0#64 then 0 else
    match m (t + 32#64) with
    | some (.word i) => 16 - min i.toNat 16
    | _ => 0

def rankOf (md : Word) : Nat := if md = 2#64 then 2 else if md = 1#64 then 1 else 0

def goOf (g : Word) : Nat := if g = 0#64 then 0 else 1

def wordOf (v : Option (PanValue Word)) : Word :=
  match v with
  | some (.word w) => w
  | _ => 0#64

/-- The measure of the decoder loop. -/
def dcMu (a : St σ) : Nat :=
  spOf a.globals * 2 ^ 73 + tT (wordOf (a.locals "top")) * 256 +
    icOf a.memory (wordOf (a.locals "top")) * 8 + rankOf (wordOf (a.locals "mode")) * 2 +
    goOf (wordOf (a.locals "go"))

theorem dcMu_eq {a : St σ} {sp t md gv : Word} (hsp : a.globals "scratch_ptr" = some (.word sp))
    (ht : a.locals "top" = some (.word t)) (hmd : a.locals "mode" = some (.word md))
    (hgo : a.locals "go" = some (.word gv)) :
    dcMu a = sp.toNat * 2 ^ 73 + tT t * 256 + icOf a.memory t * 8 + rankOf md * 2 + goOf gv := by
  unfold dcMu spOf wordOf
  rw [hsp, ht, hmd, hgo]

theorem tT_le (t : Word) : tT t ≤ 2 ^ 64 := by
  unfold tT
  split <;> omega

theorem icOf_le (m : Word → Option (PanValue Word)) (t : Word) : icOf m t ≤ 16 := by
  unfold icOf
  split
  · omega
  · split <;> omega

theorem rankOf_le (md : Word) : rankOf md ≤ 2 := by
  unfold rankOf
  split <;> [omega; (split <;> omega)]

theorem goOf_le (g : Word) : goOf g ≤ 1 := by
  unfold goOf
  split <;> omega

theorem dcMu_le (a : St σ) : dcMu a ≤ 2 ^ 138 := by
  unfold dcMu
  have h1 : spOf a.globals < 2 ^ 64 := by
    unfold spOf
    split
    · rename_i w _
      exact w.isLt
    · omega
  have h2 := tT_le (wordOf (a.locals "top"))
  have h3 := icOf_le a.memory (wordOf (a.locals "top"))
  have h4 := rankOf_le (wordOf (a.locals "mode"))
  have h5 := goOf_le (wordOf (a.locals "go"))
  omega

/-- A pop: the parent record is null or lies above. -/
theorem tT_pop {t p : Word} {lim : Nat} (hlim : lim < 2 ^ 64) (ht : t ≠ 0#64)
    (h : p = 0#64 ∨ t.toNat + 88 ≤ p.toNat) : tT p + 1 ≤ tT t := by
  unfold tT
  rw [if_neg ht]
  have := t.isLt
  have := p.isLt
  split
  · omega
  · rcases h with h | h
    · rename_i hp
      exact absurd h hp
    · omega

/-- The parent link of a stack record. -/
theorem DStk.prev_above {R : Reg} {m : Word → Option (PanValue Word)} {lim ℓ0 sp : Nat}
    {top : Word} {ℓ : Nat} (h : DStk R m lim ℓ0 sp top ℓ) : top = 0#64 ∨ sp ≤ top.toNat := by
  cases h with
  | nil => exact Or.inl rfl
  | ext h1 h2 h3 => exact Or.inr h3
  | br h1 h2 h3 => exact Or.inr h3

end InitECandidate.Solver.GuestBound
