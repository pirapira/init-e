import InitECandidate.Solver.GuestBound.Htab

/-!
# Hash tables: `htab_find_leaf`

Under the table invariant, the descent from the root only visits live nodes
and ends at 0 or at a leaf, without changing the state.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem runs_break {s : St σ} {r : Result σ} :
    Runs E s .break r ↔ r = .broke s.locals s.globals s.memory s.ffi := by
  constructor
  · rintro ⟨fuel, n, h⟩
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at h
    | succ fuel =>
      simp only [Env.run, evalPanValueFfiProgSteps, Option.pure_def, Option.some.injEq,
        Prod.mk.injEq] at h
      exact h.1.symm
  · rintro rfl
    exact runs_of_map (fuel := 1) (by simp [Env.run, evalPanValueFfiProgSteps])

/-- A product of two expressions evaluates both to words. -/
theorem eval_mul_inv {s : St σ} {a b : Exp Word} {x : PanValue Word}
    (h : E.eval s (.panOp .mul [a, b]) = some x) :
    ∃ va vb, E.eval s a = some (.word va) ∧ E.eval s b = some (.word vb) ∧
      x = .word (va * vb) := by
  rw [evalF_panOp] at h
  simp only [evalArgs_cons, evalArgs_nil] at h
  cases ha : E.eval s a with
  | none => rw [ha] at h; cases h
  | some xa =>
    cases hb : E.eval s b with
    | none => rw [ha, hb] at h; cases h
    | some xb =>
      rw [ha, hb] at h
      cases xa <;> cases xb <;> simp at h
      rename_i va vb
      exact ⟨va, vb, rfl, rfl, h.symm⟩

/-- The address of a node field, as the guest computes it. -/
theorem nodeField_eq {t : Word} {v : HtabV} (hlay : HtabLayout t v) {nv : Word}
    (hn : nv.toNat ≤ v.nc.toNat) (off : Word) (hoff : off.toNat < 32) :
    v.nodes + (nv * 32#64 + off) = nodeField v nv.toNat off.toNat := by
  unfold nodeField
  congr 1
  apply BitVec.eq_of_toNat_eq
  obtain ⟨-, -, h3, h4⟩ := hlay
  have h32 : (32#64).toNat = 32 := by decide
  have hnl := nv.isLt
  have hmul : (nv * 32#64).toNat = nv.toNat * 32 := by
    rw [BitVec.toNat_mul, h32]
    apply Nat.mod_eq_of_lt
    omega
  have : nv.toNat * 32 + off.toNat < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, hmul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this]

theorem Rd.inj {m : Word → Option (PanValue Word)} {a w w' : Word} (h : Rd m a w)
    (h' : Rd m a w') : w = w' := by
  unfold Rd at h h'
  rw [h] at h'
  simpa using h'

theorem Stopped.err (s : St σ) : Stopped s.err := trivial

/-- A header field load reads the value the header holds. -/
theorem eval_hdr (hE : GuestEnv E) {s : St σ} {t k w : Word} {x : PanValue Word}
    (ht : s.locals "t" = some (.word t)) (hw : Rd s.memory (t + k) w)
    (h : E.eval s (.load .one (.op .add [.var .local "t", .const k])) = some x) :
    x = .word w := by
  obtain ⟨addr, w', ha, rfl, hm⟩ := eval_load_one hE.mem h
  rw [eval_addc hE k ht] at ha
  simp only [Option.some.injEq, PanValue.word.injEq] at ha
  subst ha
  rw [Rd.inj hm hw]

/-- `var x = lds 1 (t + k); body` for a header field. -/
theorem dec_load_hdr (hE : GuestEnv E) {x : VarName} {k : Word} {body : Prog Word} {s : St σ}
    {r : Result σ} {t w : Word} (ht : s.locals "t" = some (.word t))
    (hw : Rd s.memory (t + k) w)
    (h : Runs E s (.dec x .one (.load .one (.op .add [.var .local "t", .const k])) body) r) :
    Stopped r ∨ ∃ r', Runs E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory,
      s.ffi⟩ body r' ∧ r = restorePanValueFfiLocal x (s.locals x) r' := by
  cases he : E.eval s (.load .one (.op .add [.var .local "t", .const k])) with
  | none =>
    rw [runs_dec, he] at h
    simp only at h
    subst h
    exact Or.inl (Stopped.err s)
  | some y =>
    have := eval_hdr hE ht hw he
    subst this
    exact Or.inr (dec_word_runs he h)

/-- A node index handed out and not on the free list. -/
def Live (v : HtabV) (kind : Nat → NodeKind) (n : Word) : Prop :=
  1 ≤ n.toNat ∧ n.toNat < v.next.toNat ∧ kind n.toNat ≠ .free

/-- A node field load reads the cell of that field. -/
theorem eval_field (hE : GuestEnv E) {s : St σ} {t : Word} {v : HtabV} {kind : Nat → NodeKind}
    (hwf : HtabWF s.memory t v kind) {nv : Word} (hlt : nv.toNat < v.next.toNat)
    (hnodes : s.locals "nodes" = some (.word v.nodes)) (hn : s.locals "n" = some (.word nv))
    (off : Word) (hoff : off.toNat < 32) {x : PanValue Word}
    (h : E.eval s (.load .one (.op .add [.var .local "nodes",
      .panOp .mul [.var .local "n", .const 32#64], .const off])) = some x) :
    ∃ w, x = .word w ∧ Rd s.memory (nodeField v nv.toNat off.toNat) w := by
  obtain ⟨addr, w, ha, rfl, hm⟩ := eval_load_one hE.mem h
  have he : E.eval s (.op .add [.var .local "nodes",
      .panOp .mul [.var .local "n", .const 32#64], .const off]) =
      some (.word (v.nodes + (nv * 32#64 + off))) := by
    ev [hnodes, hn, evalPanOp, BitVec.add_assoc]
  rw [he] at ha
  simp only [Option.some.injEq, PanValue.word.injEq] at ha
  subst ha
  have hle : nv.toNat ≤ v.nc.toNat := by have := hwf.next_le; omega
  rw [nodeField_eq hwf.layout hle off hoff] at hm
  exact ⟨w, rfl, hm⟩

/-- `n = lds 1 (nodes + n * 32 + off)` for a field holding `c`. -/
theorem assign_field (hE : GuestEnv E) {s : St σ} {t : Word} {v : HtabV}
    {kind : Nat → NodeKind} (hwf : HtabWF s.memory t v kind) {nv : Word}
    (hlt : nv.toNat < v.next.toNat) (hnodes : s.locals "nodes" = some (.word v.nodes))
    (hn : s.locals "n" = some (.word nv)) (off : Word) (hoff : off.toNat < 32) {c : Word}
    (hc : Rd s.memory (nodeField v nv.toNat off.toNat) c) {r : Result σ}
    (h : Runs E s (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
      .panOp .mul [.var .local "n", .const 32#64], .const off]))) r) :
    r = s.err ∨ r = .normal (updatePanValueMap s.locals "n" (.word c)) s.globals s.memory
      s.ffi := by
  rw [runs_assign_local] at h
  cases he : E.eval s (.load .one (.op .add [.var .local "nodes",
      .panOp .mul [.var .local "n", .const 32#64], .const off])) with
  | none =>
    rw [he] at h
    exact Or.inl h
  | some x =>
    obtain ⟨w, rfl, hw⟩ := eval_field hE hwf hlt hnodes hn off hoff he
    have := Rd.inj hw hc
    subst this
    rw [he] at h
    simp only [panValueAssignmentValid, hn, shape_word, shape_matches_self, if_true] at h
    exact Or.inr h

/-- Loop invariant of the descent. -/
def FindI (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (v : HtabV) (kind : Nat → NodeKind) (s : St σ) : Prop :=
  s.globals = g ∧ s.memory = m ∧ s.ffi = f ∧
    s.locals "keybits" = some (.word (v.kl * 8#64)) ∧
    s.locals "nodes" = some (.word v.nodes) ∧
    ∃ nv, s.locals "n" = some (.word nv) ∧ (nv = 0 ∨ Live v kind nv)

/-- Exit condition of the descent: `n` is 0 or a live leaf. -/
def FindQ (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (v : HtabV) (kind : Nat → NodeKind) (r : Result σ) : Prop :=
  r.isError = true ∨ ∃ l nv, r = .normal l g m f ∧ l "n" = some (.word nv) ∧
    (nv = 0 ∨ (Live v kind nv ∧ kind nv.toNat = .leaf))

/-- One step of the descent keeps the invariant or ends at a leaf. -/
theorem find_body (hE : GuestEnv E) {t : Word} {v : HtabV} {kind : Nat → NodeKind}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {f : FfiState σ} (hwf : HtabWF m t v kind) {c2 : Exp Word} (s : St σ) (r : Result σ)
    (hI : FindI g m f v kind s)
    (hc : CondTrue E s (.cmp .notEqual (.var .local "n") (.const 0#64)))
    (h : Runs E s
      (.dec "b" .one (.load .one (.op .add [.var .local "nodes",
          .panOp .mul [.var .local "n", .const 32#64], .const 24#64]))
        (.seq (.ite (.cmp .equal (.var .local "b") (.var .local "keybits")) .break .skip)
          (.ite c2
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const 8#64])))
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const 16#64])))))) r) :
    BodyInv (FindI g m f v kind) (FindQ g m f v kind) r := by
  obtain ⟨rfl, rfl, rfl, hkb, hnodes, nv, hn, hlive⟩ := hI
  have hnz : nv ≠ 0 := by
    rintro rfl
    obtain ⟨c, k, hcond, hne⟩ := hc
    rw [cond_eq] at hcond
    simp [evalF_cmp hE.word, evalF_local, hn, evalPanCmp] at hcond
    rw [← hcond.1] at hne
    simp at hne
  have hl : Live v kind nv := hlive.resolve_left hnz
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
    cases hk : kind nv.toNat with
    | free => exact absurd hk hl.2.2
    | leaf =>
      obtain ⟨p, value, pos, -, -, -, hkd, -⟩ := hwf.leaf_ok _ hl.1 hl.2.1 hk
      have := Rd.inj hb hkd
      subst this
      simp [evalPanCmp] at h1
      rw [runs_break] at h1
      subst h1
      simp only at hrest
      subst hrest
      refine Or.inr ⟨_, nv, rfl, ?_, Or.inr ⟨hl, hk⟩⟩
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hn]
    | internal =>
      obtain ⟨p, lc, rc, b', -, hlc, hrc, hb', hbne, -, hcl, hcr, -⟩ :=
        hwf.internal_ok _ hl.1 hl.2.1 hk
      have := Rd.inj hb hb'
      subst this
      simp [evalPanCmp, hbne] at h1
      rw [runs_skip] at h1
      subst h1
      simp only at hrest
      have hnodes' : (updatePanValueMap s.locals "b" (.word bv)) "nodes" =
          some (.word v.nodes) := by
        simp (config := { decide := true }) [update_lookup, hnodes]
      have hn' : (updatePanValueMap s.locals "b" (.word bv)) "n" = some (.word nv) := by
        simp (config := { decide := true }) [update_lookup, hn]
      have step : ∀ (off c : Word), off.toNat < 32 →
          Rd s.memory (nodeField v nv.toNat off.toNat) c → ChildOk s.memory v kind nv.toNat c →
          Runs E ⟨updatePanValueMap s.locals "b" (.word bv), s.globals, s.memory, s.ffi⟩
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const off]))) rb →
          BodyInv (FindI s.globals s.memory s.ffi v kind) (FindQ s.globals s.memory s.ffi v kind)
            (restorePanValueFfiLocal "b" (s.locals "b") rb) := by
        intro off c hoff hc hch hr
        rcases assign_field hE (s := ⟨updatePanValueMap s.locals "b" (.word bv), s.globals,
          s.memory, s.ffi⟩) hwf hl.2.1 hnodes' hn' off hoff hc hr with rfl | rfl
        · exact Or.inl rfl
        · refine ⟨rfl, rfl, rfl, ?_, ?_, c, ?_, Or.inr ⟨hch.1, hch.2.1, hch.2.2.1⟩⟩
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hkb]
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hnodes]
          · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      rw [runs_ite] at hrest
      split at hrest
      · split at hrest
        · exact step 16#64 rc (by decide) hrc hcr hrest
        · exact step 8#64 lc (by decide) hlc hcl hrest
      · subst hrest
        exact Or.inl rfl

/-- `htab_find_leaf(t, key)` on a well-formed table: 0 or a live leaf, state unchanged. -/
theorem htab_find_leaf_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_find_leaf" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t : Word) (v : HtabV) (kind : Nat → NodeKind)
    (ht : s.locals "t" = some (.word t)) (hwf : HtabWF s.memory t v kind)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l nv, r = .returned l s.globals s.memory s.ffi [.word nv] ∧
      (nv = 0 ∨ (Live v kind nv ∧ kind nv.toNat = .leaf)) := by
  have hbody := (fun_of_index 131 hE.functions (by guest_decl_at 131) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  obtain ⟨hkl, -, -, -, -, hnd, -, hroot, -⟩ := hwf.hdr
  -- keybits
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
    have hQ : FindQ s.globals s.memory s.ffi v kind rl := by
      refine while_inv (I := FindI s.globals s.memory s.ffi v kind)
        (Q := FindQ s.globals s.memory s.ffi v kind) (fun r hr => Or.inl hr)
        ?_ ?_ fuel _ rl n ?_ hrun
      · rintro s' k ⟨hg, hm, hf, -, -, nv, hn, -⟩ hcond
        refine Or.inr ⟨s'.locals, nv, by rw [hg, hm, hf], hn, Or.inl ?_⟩
        rw [cond_eq] at hcond
        simp [evalF_cmp hE.word, hn, evalPanCmp] at hcond
        exact hcond.1
      · intro fuel' s' r' n' hI hc hrun'
        exact find_body hE hwf s' r' hI hc (Runs.of_run hrun')
      · refine ⟨rfl, rfl, rfl, ?_, ?_, v.root, ?_, ?_⟩
        · simp (config := { decide := true }) [update_lookup]
        · simp (config := { decide := true }) [update_lookup]
        · simp (config := { decide := true }) [update_lookup]
        · rcases hwf.root_ok with h0 | ⟨a, b, c, -⟩
          · exact Or.inl h0
          · exact Or.inr ⟨a, b, c⟩
    rcases hQ with herr | ⟨l, nv, rfl, hn, hres⟩
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
