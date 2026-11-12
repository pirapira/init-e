import InitECandidate.Solver.GuestBound.HtabKeys

/-!
# Hash tables: what `htab_find_leaf` finds for an arbitrary key

The leaf found agrees with the key on every bit tested on the way down.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {m : Word → Option (PanValue Word)} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
  {rep : KeyRep}

/-- The key with bits `κ` agrees with node `c` on the bits tested by the strict
ancestors of `c`. -/
def PathAgree (m : Word → Option (PanValue Word)) (v : HtabV) (rep : KeyRep) (κ : Word → Bool)
    (c : Nat) : Prop :=
  ∀ a, Anc m v a c → a ≠ c → ∀ ba, Rd m (nodeField v a 24) ba → rep c ba = κ ba

theorem pathAgree_root (hwf : HtabWF m t v kind) (hr : v.root ≠ 0) (κ : Word → Bool) :
    PathAgree m v rep κ v.root.toNat := by
  intro a hanc hne
  cases hanc with
  | refl => exact absurd rfl hne
  | up p hp hp0 _ =>
    rcases hwf.root_ok with h | ⟨-, -, -, h0⟩
    · exact absurd h hr
    · exact absurd (Rd.inj hp h0) hp0

/-- Stepping to the child on the key's side keeps the agreement. -/
theorem pathAgree_child (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {κ : Word → Bool}
    {n : Nat} (hl : LiveN v kind n) (hkd : kind n = .internal) {bv lc rc c : Word}
    (hb : Rd m (nodeField v n 24) bv) (hlc : Rd m (nodeField v n 8) lc)
    (hrc : Rd m (nodeField v n 16) rc) (hc : ChildOk m v kind n c)
    (hside : (c = lc ∧ κ bv = false) ∨ (c = rc ∧ κ bv = true))
    (hpp : PathAgree m v rep κ n) : PathAgree m v rep κ c.toNat := by
  obtain ⟨-, hrl, hrr, hagree, -, -⟩ := hk.internal_bits n hl.1 hl.2.1 hkd bv lc rc hb hlc hrc
  have hn64 : n < 2 ^ 64 := by have := v.next.isLt; have := hl.2.1; omega
  intro a hanc hne ba hba
  cases hanc with
  | refl => exact absurd rfl hne
  | up p hp hp0 hanc' =>
    have hpn : p.toNat = n := by
      rw [Rd.inj hp hc.2.2.2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn64]
    rw [hpn] at hanc'
    by_cases han : a = n
    · subst han
      have := Rd.inj hba hb
      subst this
      rcases hside with ⟨rfl, hκ⟩ | ⟨rfl, hκ⟩
      · rw [hrl, hκ]
      · rw [hrr, hκ]
    · have hai := anc_internal hwf hk hanc' hl han
      obtain ⟨_, la, ra, ba', -, hla, hra, hba', -⟩ := hwf.internal_ok a hai.1.1 hai.1.2.1 hai.2
      have := Rd.inj hba hba'
      subst this
      obtain ⟨hlt, -, -⟩ := anc_child hwf hk hanc' hl han ba la ra bv hba hla hra hb
      have hrep : rep c.toNat ba = rep n ba := by
        rcases hside with ⟨rfl, -⟩ | ⟨rfl, -⟩
        · exact (hagree ba hlt).1
        · exact (hagree ba hlt).2
      rw [hrep]
      exact hpp a hanc' han ba hba

variable {σ : Type} {E : Env σ}

/-- Loop invariant of the descent for a key with bits `κ`. -/
def PathI (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (v : HtabV) (kind : Nat → NodeKind) (rep : KeyRep) (κ : Word → Bool)
    (kp : Word) (s : St σ) : Prop :=
  s.globals = g ∧ s.memory = m ∧ s.ffi = f ∧
    s.locals "keybits" = some (.word (v.kl * 8#64)) ∧
    s.locals "nodes" = some (.word v.nodes) ∧ s.locals "key" = some (.word kp) ∧
    ∃ nv, s.locals "n" = some (.word nv) ∧
      ((nv = 0 ∧ v.root = 0) ∨ (LiveN v kind nv.toNat ∧ PathAgree m v rep κ nv.toNat))

/-- What the descent leaves in `n`. -/
def PathR (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind)
    (rep : KeyRep) (κ : Word → Bool) (nv : Word) : Prop :=
  (nv = 0 ∧ v.root = 0) ∨
    (LiveN v kind nv.toNat ∧ kind nv.toNat = .leaf ∧ PathAgree m v rep κ nv.toNat)

def PathQ (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (v : HtabV) (kind : Nat → NodeKind) (rep : KeyRep) (κ : Word → Bool)
    (r : Result σ) : Prop :=
  r.isError = true ∨ ∃ l, r = .normal l g m f ∧ ∃ nv, l "n" = some (.word nv) ∧
    PathR m v kind rep κ nv

set_option maxHeartbeats 4000000 in
theorem path_body (hE : GuestEnv E) {g : VarName → Option (PanValue Word)} {f : FfiState σ}
    (hwf : HtabWF m t v kind) (hk : HtabKeys m v kind rep) {kp : Word} {κ : Word → Bool}
    (hkey : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat → KeyBitIs E.bytesInWord m kp j (κ j))
    (s : St σ) (r : Result σ) (hI : PathI g m f v kind rep κ kp s)
    (hnz : ∀ nv, s.locals "n" = some (.word nv) → nv ≠ 0)
    (h : Runs E s
      (.dec "b" .one (.load .one (.op .add [.var .local "nodes",
          .panOp .mul [.var .local "n", .const 32#64], .const 24#64]))
        (.seq (.ite (.cmp .equal (.var .local "b") (.var .local "keybits")) .break .skip)
          (.ite htBitZero
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const 8#64])))
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const 16#64])))))) r) :
    BodyInv (PathI g m f v kind rep κ kp) (PathQ g m f v kind rep κ) r := by
  obtain ⟨rfl, rfl, rfl, hkb, hnodes, hkp, nv, hn, hcase⟩ := hI
  rcases hcase with ⟨h0, -⟩ | ⟨hl, hpp⟩
  · exact absurd h0 (hnz nv hn)
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
      refine Or.inr ⟨_, rfl, nv, ?_, Or.inr ⟨hl, hkd, hpp⟩⟩
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hn]
    | internal =>
      obtain ⟨p, lc, rc, b', -, hlc, hrc, hb', hbne, -, hcl, hcr, -⟩ :=
        hwf.internal_ok _ hl.1 hl.2.1 hkd
      have := Rd.inj hb hb'
      subst this
      obtain ⟨hblt, -⟩ := hk.internal_bits _ hl.1 hl.2.1 hkd bv lc rc hb hlc hrc
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
          PathAgree s.memory v rep κ c.toNat →
          Runs E ⟨updatePanValueMap s.locals "b" (.word bv), s.globals, s.memory, s.ffi⟩
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const off]))) rb →
          BodyInv (PathI s.globals s.memory s.ffi v kind rep κ kp)
            (PathQ s.globals s.memory s.ffi v kind rep κ)
            (restorePanValueFfiLocal "b" (s.locals "b") rb) := by
        intro off c hoff hc hch hca hr
        rcases assign_field hE (s := ⟨updatePanValueMap s.locals "b" (.word bv), s.globals,
          s.memory, s.ffi⟩) hwf hl.2.1 hnodes' hn' off hoff hc hr with rfl | rfl
        · exact Or.inl rfl
        · refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, c, ?_, Or.inr ⟨⟨hch.1, hch.2.1, hch.2.2.1⟩, hca⟩⟩
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
        cases hbit : κ bv with
        | false =>
          simp (config := { decide := true }) only [hbit, if_false, Bool.false_eq_true] at hrest
          exact step 8#64 lc (by decide) hlc hcl
            (pathAgree_child hwf hk hl hkd hb hlc hrc hcl (Or.inl ⟨rfl, hbit⟩) hpp) hrest
        | true =>
          simp (config := { decide := true }) only [hbit, if_true] at hrest
          exact step 16#64 rc (by decide) hrc hcr
            (pathAgree_child hwf hk hl hkd hb hlc hrc hcr (Or.inr ⟨rfl, hbit⟩) hpp) hrest

set_option maxHeartbeats 4000000 in
/-- `htab_find_leaf(t, key)`: no leaf in an empty table, otherwise a leaf that
agrees with the key on the bits tested along its path. -/
theorem htab_find_path_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_find_leaf" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t : Word) (v : HtabV) (kind : Nat → NodeKind) (rep : KeyRep)
    (kp : Word) (κ : Word → Bool) (ht : s.locals "t" = some (.word t))
    (hkp : s.locals "key" = some (.word kp))
    (hwf : HtabWF s.memory t v kind) (hk : HtabKeys s.memory v kind rep)
    (hkey : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs E.bytesInWord s.memory kp j (κ j))
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l nv, r = .returned l s.globals s.memory s.ffi [.word nv] ∧
      PathR s.memory v kind rep κ nv := by
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
    have hQ : PathQ s.globals s.memory s.ffi v kind rep κ rl := by
      refine while_inv (I := PathI s.globals s.memory s.ffi v kind rep κ kp)
        (Q := PathQ s.globals s.memory s.ffi v kind rep κ) (fun r hr => Or.inl hr)
        ?_ ?_ fuel _ rl n ?_ hrun
      · rintro s' k ⟨hg, hm, hf, -, -, -, nv, hn, hcase⟩ hcond
        rw [cond_eq] at hcond
        simp [evalF_cmp hE.word, hn, evalPanCmp] at hcond
        refine Or.inr ⟨_, by rw [hg, hm, hf], nv, hn, ?_⟩
        rcases hcase with h0 | ⟨hlv, -⟩
        · exact Or.inl h0
        · have h1 := hlv.1
          rw [hcond.1] at h1
          exact absurd h1 (by decide)
      · intro fuel' s' r' n' hI hct hrun'
        refine path_body hE hwf hk hkey s' r' hI (fun nv hn h0 => ?_) (Runs.of_run hrun')
        obtain ⟨w, c, hcond, hw⟩ := hct
        rw [cond_eq] at hcond
        simp [evalF_cmp hE.word, hn, evalPanCmp, h0] at hcond
        rw [← hcond.1] at hw
        exact absurd hw (by decide)
      · refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, v.root, ?_, ?_⟩
        · simp (config := { decide := true }) [update_lookup]
        · simp (config := { decide := true }) [update_lookup]
        · simp (config := { decide := true }) [update_lookup, hkp]
        · simp (config := { decide := true }) [update_lookup]
        · by_cases hr0 : v.root = 0
          · exact Or.inl ⟨hr0, hr0⟩
          · rcases hwf.root_ok with h | ⟨a, b, c, -⟩
            · exact absurd h hr0
            · exact Or.inr ⟨⟨a, b, c⟩, pathAgree_root hwf hr0 κ⟩
    rcases hQ with herr | ⟨l, rfl, nv, hn, hres⟩
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
      exact Or.inr ⟨_, nv, rfl, hres⟩

end InitECandidate.Solver.GuestBound
