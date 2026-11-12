import InitECandidate.Solver.GuestBound.HtabGrowInv

/-!
# Hash tables: `htab_new_node`

A node index comes from the free list, or from the never-used tail after
growing the table when it is full.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `htab_grow(t)` as a statement. -/
theorem WPs.call_grow (hE : GuestEnv E) {t pv : Word} {v : HtabV} {kind : Nat → NodeKind}
    (ht : s.locals "t" = some (.word t)) (hhdr : HtabHdr s.memory t v) (hlay : HtabLayout t v)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat)
    (h : ∀ N O q mF, GrowRel s.memory t v pv N O q mF →
      Q (.normal s.locals (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals
        "heap_ptr" (.word N)) "heap_ptr" (.word O)) "heap_ptr" (.word q)) mF s.ffi)) :
    WPs E s (.call (some (none, none)) "htab_grow" [.var .local "t"]) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 137 hE.functions (by guest_decl_at 137) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ht, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := htab_grow_exec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb t pv
    v kind (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hhdr hlay hp
    hpH hend hcallee
  rcases hpost with hst | ⟨l, N, O, q, mF, rfl, hR⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only [CallOutcome] at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only [CallOutcome] at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f =>
      simp only [CallOutcome] at hout
      exact Or.inl (Stopped.of_error hout)
    | _ => exact absurd hst (fun h => h)
  · simp only [CallOutcome] at hout
    rcases hout with herr | ⟨l', g', hassign, rfl⟩
    · exact Or.inl (Stopped.of_error herr)
    · obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
      have : l' = s.locals := funext (fun x => hl x (by simp))
      subst this
      exact Or.inr (h N O q mF hR)

/-- The table after the optional growth in `htab_new_node`: unchanged, or grown. -/
def NodeGS (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV) (kind : Nat → NodeKind)
    (rep : KeyRep) (det : Nat → Prop) (g : VarName → Option (PanValue Word)) (pv : Word)
    (g1 : VarName → Option (PanValue Word)) (m1 : Word → Option (PanValue Word)) (v1 : HtabV) :
    Prop :=
  HtabOKd m1 t v1 kind rep det ∧ v1.kl = v.kl ∧ v1.st = v.st ∧ v1.cnt = v.cnt ∧ v1.root = v.root ∧
    v1.next = v.next ∧ v1.free = v.free ∧ v.next.toNat ≤ v1.nc.toNat ∧
    ((m1 = m ∧ v1 = v ∧ g1 = g) ∨ ∃ N O q, GrowRel m t v pv N O q m1 ∧
      v1 = ⟨v.kl, v.st, v.cp * 2#64, v.nc * 2#64, v.cnt, pv, N, O, v.root, v.next, v.free⟩ ∧
      g1 = updatePanValueMap (updatePanValueMap (updatePanValueMap g "heap_ptr" (.word N))
        "heap_ptr" (.word O)) "heap_ptr" (.word q))

/-- What `htab_new_node` did: popped the free list, or bumped `next` after an
optional growth. -/
def NewNodeRel (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV)
    (kind : Nat → NodeKind) (rep : KeyRep) (det : Nat → Prop)
    (g : VarName → Option (PanValue Word)) (pv : Word)
    (m' : Word → Option (PanValue Word)) (g' : VarName → Option (PanValue Word)) (n : Word) :
    Prop :=
  (v.free ≠ 0#64 ∧ n = v.free ∧ g' = g ∧
    ∃ nf, Rd m (nodeField v v.free.toNat 0) nf ∧ m' = setCell m (t + 72#64) nf) ∨
  (v.free = 0#64 ∧ n = v.next ∧
    ∃ m1 v1, NodeGS m t v kind rep det g pv g' m1 v1 ∧ m' = setCell m1 (t + 64#64) (v.next + 1#64))

set_option maxHeartbeats 4000000 in
theorem htab_new_node_exec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_new_node" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t pv : Word) (v : HtabV) (kind : Nat → NodeKind) (rep : KeyRep)
    (det : Nat → Prop)
    (ht : s.locals "t" = some (.word t)) (hok : HtabOKd s.memory t v kind rep det)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' n, r = .returned l g' m' s.ffi [.word n] ∧
      NewNodeRel s.memory t v kind rep det s.globals pv m' g' n := by
  have hbody := (fun_of_index 134 hE.functions (by guest_decl_at 134) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' n, r = .returned l g' m' s.ffi [.word n] ∧
      NewNodeRel s.memory t v kind rep det s.globals pv m' g' n)) r h
  have hwf := hok.wf
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  have hnl := hwf.next_le
  refine WPs.dec (eval_load_rd hE (eval_addc hE 72#64 ht) hfree) ?_
  by_cases hf0 : v.free = 0#64
  · refine WPs.guard0 (fun y hy => by
      rw [eval_cmp_inv hE (of_eval (w := v.free) (by lk [])) (of_eval (eval_const _ _)) y hy]
      simp [evalPanCmp, hf0]) ?_
    refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 64#64 (by lk [ht])) hnext) ?_
    refine WPs.seq (fun a => a.locals = updatePanValueMap (updatePanValueMap s.locals "f"
        (.word v.free)) "next" (.word v.next) ∧ a.ffi = s.ffi ∧
        ∃ v1, NodeGS s.memory t v kind rep det s.globals pv a.globals a.memory v1) ?_ ?_
    · refine WPs.ite (w := evalPanCmp .lower v.nc v.next) (eval_cmp_inv hE
        (eval_load_rd hE (eval_addc hE (a := t) 80#64 (by lk [ht])) hnc)
        (of_eval (w := v.next) (by lk []))) ?_
      split
      · rename_i hc
        have hle : v.next.toNat ≤ v.nc.toNat := by
          have := lower_zero hc
          rw [BitVec.lt_def] at this
          omega
        exact WPs.skip ⟨_, _, _, _, rfl, rfl, rfl, v, hok, rfl, rfl, rfl, rfl, rfl, rfl, hle,
          Or.inl ⟨rfl, rfl, rfl⟩⟩
      · refine WPs.call_grow hE (kind := kind) (by lk [ht]) hwf.hdr hlay hp hpH hend ?_
        intro N O q mF hR
        have h2 : (2#64 : Word).toNat = 2 := by decide
        have hnc2 : (v.nc * 2#64).toNat = v.nc.toNat * 2 := by
          rw [BitVec.toNat_mul, h2]
          exact Nat.mod_eq_of_lt (by omega)
        have hpos := hok.nc_pos
        exact ⟨_, _, _, _, rfl, rfl, rfl, _, htab_grow_ok hok hpH hend hR, rfl, rfl, rfl, rfl,
          rfl, rfl, by show v.next.toNat ≤ (v.nc * 2#64).toNat; omega, Or.inr ⟨N, O, q, hR, rfl, rfl⟩⟩
    · rintro a ⟨hl, hf, v1, hok1, e1, e2, e3, e4, e5, e6, hle, hcase⟩
      have hta : a.locals "t" = some (.word t) := by rw [hl]; lk [ht]
      have hnext1 : Rd a.memory (t + 64#64) v.next := by
        have := hok1.wf.hdr.2.2.2.2.2.2.2.2.1
        rw [e5] at this
        exact this
      refine WPs.dec (eval_load_rd hE (eval_addc hE 64#64 hta) hnext1) ?_
      refine WPs.seq_store hE (eval_addc hE (a := t) 64#64 (by lk [hta]))
        (of_eval (eval_addc hE (a := v.next) 1#64 (by lk []))) ?_
      refine WPs.ret (of_eval (w := v.next) (by lk [])) ?_
      refine ⟨_, a.globals, _, v.next, by simp only [restorePanValueFfiLocal]; rw [hf],
        Or.inr ⟨hf0, rfl, a.memory, v1, ⟨hok1, e1, e2, e3, e4, e5, e6, hle, hcase⟩, rfl⟩⟩
  · obtain ⟨hf1, hf2, hfk⟩ := hwf.free_ok.resolve_left hf0
    obtain ⟨nf, hnf, -⟩ := hwf.free_next _ hf1 hf2 hfk
    refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
    refine WPs.ite (w := 1#64) (fun y hy => by
      rw [eval_cmp_inv hE (of_eval (w := v.free) (by lk [])) (of_eval (eval_const _ _)) y hy]
      simp [evalPanCmp, hf0]) ?_
    split
    · rename_i h10
      exact absurd h10 (by decide)
    refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 40#64 (by lk [ht])) hnd) ?_
    refine WPs.dec (eval_load_rd hE (eval_node hE hlay (idx := "f") (by omega) (by lk [])
      (by lk []) 0#64 (by decide)) hnf) ?_
    refine WPs.seq_store hE (eval_addc hE (a := t) 72#64 (by lk [ht]))
      (of_eval (w := nf) (by lk [])) ?_
    refine WPs.ret (of_eval (w := v.free) (by lk [])) ?_
    exact ⟨_, _, _, _, rfl, Or.inl ⟨hf0, rfl, rfl, nf, hnf, rfl⟩⟩

end InitECandidate.Solver.GuestBound
