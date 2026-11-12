import InitECandidate.Solver.GuestBound.Wp
import InitECandidate.Solver.GuestBound.MemEq

/-!
# Hash tables: `htab_del` of a stored key

Deleting the key of a live leaf always removes that leaf: the lookup finds
it, the key comparison succeeds, and the stores unlink it.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The table invariant: structure, crit-bit order, and the stored keys. -/
structure HtabOK (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV)
    (kind : Nat → NodeKind) (rep : KeyRep) : Prop where
  wf : HtabWF m t v kind
  keys : HtabKeys m v kind rep
  keys8 : v.keys.toNat % 8 = 0
  kl_st : v.kl.toNat ≤ v.st.toNat
  kl8 : v.kl.toNat * 8 < 2 ^ 64
  leaf_key : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .leaf →
    ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs 8#64 m (v.keys + BitVec.ofNat 64 i * v.st) j (rep i j)

variable {s : St σ} {Q : Result σ → Prop}

theorem of_eval {e : Exp Word} {w : Word} (h : E.eval s e = some (.word w)) :
    ∀ y, E.eval s e = some y → y = .word w := by
  intro y hy
  rw [h] at hy
  exact (Option.some.inj hy).symm

/-- A word load from a known address holding `w`. -/
theorem eval_load_rd (hE : GuestEnv E) {a : Exp Word} {addr w : Word}
    (ha : E.eval s a = some (.word addr)) (hw : Rd s.memory addr w) :
    ∀ y, E.eval s (.load .one a) = some y → y = .word w := by
  intro y hy
  obtain ⟨addr', w', ha', rfl, hm⟩ := eval_load_one hE.mem hy
  rw [ha] at ha'
  simp only [Option.some.injEq, PanValue.word.injEq] at ha'
  subst ha'
  rw [Rd.inj hm hw]

/-- The address of a node field. -/
theorem eval_node (hE : GuestEnv E) {t : Word} {v : HtabV} (hlay : HtabLayout t v)
    {idx : VarName} {iv : Word} (hi : iv.toNat ≤ v.nc.toNat)
    (hnodes : s.locals "nodes" = some (.word v.nodes)) (hidx : s.locals idx = some (.word iv))
    (off : Word) (hoff : off.toNat < 32) :
    E.eval s (.op .add [.var .local "nodes", .panOp .mul [.var .local idx, .const 32#64],
      .const off]) = some (.word (nodeField v iv.toNat off.toNat)) := by
  rw [← nodeField_eq hlay hi off hoff]
  ev [hnodes, hidx, evalPanOp, BitVec.add_assoc]

/-- The address of an order slot. -/
theorem eval_ord (hE : GuestEnv E) {t : Word} {v : HtabV} (hlay : HtabLayout t v)
    {idx : VarName} {iv : Word} (hi : iv.toNat ≤ v.nc.toNat)
    (horder : s.locals "order" = some (.word v.order)) (hidx : s.locals idx = some (.word iv)) :
    E.eval s (.op .add [.var .local "order", .panOp .mul [.var .local idx, .const 8#64]]) =
      some (.word (orderSlot v iv.toNat)) := by
  have hmul : (iv * 8#64).toNat = iv.toNat * 8 := by
    obtain ⟨-, -, -, h4⟩ := hlay
    have h8 : (8#64 : Word).toNat = 8 := by decide
    rw [BitVec.toNat_mul, h8]
    exact Nat.mod_eq_of_lt (by omega)
  have : v.order + iv * 8#64 = orderSlot v iv.toNat := by
    unfold orderSlot
    congr 1
  rw [← this]
  ev [horder, hidx, evalPanOp]

/-- `var x = htab_find_leaf(t, key)` for the stored key of the live leaf `Lw`. -/
theorem WPs.decCall_find (hE : GuestEnv E) {x : VarName} {body : Prog Word} {t kp Lw : Word}
    {v : HtabV} {kind : Nat → NodeKind} {rep : KeyRep}
    (ht : s.locals "t" = some (.word t)) (hkp : s.locals "key" = some (.word kp))
    (hwf : HtabWF s.memory t v kind) (hk : HtabKeys s.memory v kind rep)
    (hL : LiveN v kind Lw.toNat) (hLk : kind Lw.toNat = .leaf)
    (hkey : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat →
      KeyBitIs 8#64 s.memory kp j (rep Lw.toNat j))
    (h : WPs E ⟨updatePanValueMap s.locals x (.word Lw), s.globals, s.memory, s.ffi⟩ body
      (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "htab_find_leaf" [.var .local "t", .var .local "key"] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 131 hE.functions (by guest_decl_at 131) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ht, hkp, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := htab_find_self_runs hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩
    rb t v kind rep kp Lw (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hwf hk hL hLk
    (by rw [hE.bytes]; exact hkey) hcallee
  rcases hpost with hst | ⟨l, rfl⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f => exact hout.elim
    | _ => exact absurd hst (fun h => h)
  · obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

/-- `var x = memeq(e1, e2, e3)` with both pointers equal. -/
theorem WPs.decCall_memeq (hE : GuestEnv E) {x : VarName} {body : Prog Word}
    {e1 e2 e3 : Exp Word} {pa n : Word} (h1 : E.eval s e1 = some (.word pa))
    (h2 : E.eval s e2 = some (.word pa)) (h3 : E.eval s e3 = some (.word n))
    (h : WPs E ⟨updatePanValueMap s.locals x (.word 1#64), s.globals, s.memory, s.ffi⟩ body
      (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "memeq" [e1, e2, e3] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 18 hE.functions (by guest_decl_at 18) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := memeq_self hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hcallee
  cases rb with
  | returned lr g m f vs =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpost
    obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq
  | raised lr g m f ex v =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m f ev =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | _ => exact hout.elim

end InitECandidate.Solver.GuestBound
