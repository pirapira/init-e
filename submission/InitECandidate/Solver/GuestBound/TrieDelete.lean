import InitECandidate.Solver.GuestBound.TrieDelLoop

/-!
# `_mpt_delete_node_body`: world invariant and step bound

The descent loop pushes records until it stops with a result; the unwind loop
pops them. Both terminate only under the world invariant: the descent because
levels grow within the key, the unwind because the stack is a well-formed
list in the scratch arena.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

local notation "DGUARD" => ((Exp.cmp Cmp.notEqual (Exp.var VarKind.local "go") (Exp.const (BitVec.ofNat 64 0))) : Exp Word)

local notation "DBODY" => ((Prog.seq (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 0))) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "node") (Exp.const (BitVec.ofNat 64 0))) (Prog.assign VarKind.local "res" (Exp.const (BitVec.ofNat 64 0))) (Prog.dec "k" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 0))])) (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 0))) (Prog.call (some (none, none)) "mpt_fail" [(Exp.const (BitVec.ofNat 64 2))]) Prog.skip) (Prog.seq (Prog.call (some (none, none)) "node_invalidate" [(Exp.var VarKind.local "node")]) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 1))) (Prog.seq (Prog.assign VarKind.local "res" (Exp.var VarKind.local "node")) (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 40))])) (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")])) (Prog.decCall "eq" Shape.one "memeq" [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 32))])), (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")]), (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")])] (Prog.ite (Exp.cmp Cmp.notEqual (Exp.var VarKind.local "eq") (Exp.const (BitVec.ofNat 64 0))) (Prog.assign VarKind.local "res" (Exp.const (BitVec.ofNat 64 0))) Prog.skip)) Prog.skip)) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "k") (Exp.const (BitVec.ofNat 64 2))) (Prog.dec "seg" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 32))])) (Prog.dec "sl" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 40))])) (Prog.decCall "pl" Shape.one "common_prefix_length" [(Exp.var VarKind.local "seg"), (Exp.var VarKind.local "sl"), (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")]), (Exp.op BinOp.sub [(Exp.var VarKind.local "klen"), (Exp.var VarKind.local "level")])] (Prog.ite (Exp.cmp Cmp.lower (Exp.var VarKind.local "pl") (Exp.var VarKind.local "sl")) (Prog.assign VarKind.local "res" (Exp.var VarKind.local "node")) (Prog.decCall "fr" Shape.one "scratch_alloc" [(Exp.const (BitVec.ofNat 64 40))] (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "top")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "node")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 2))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 24))]) (Exp.var VarKind.local "seg")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr"), (Exp.const (BitVec.ofNat 64 32))]) (Exp.var VarKind.local "sl")) (Prog.seq (Prog.assign VarKind.local "top" (Exp.var VarKind.local "fr")) (Prog.seq (Prog.assign VarKind.local "node" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 48))]))) (Prog.seq (Prog.assign VarKind.local "level" (Exp.op BinOp.add [(Exp.var VarKind.local "level"), (Exp.var VarKind.local "sl")])) (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 1)))))))))))))))) (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "level") (Exp.var VarKind.local "klen")) (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 168))])) (Exp.const (BitVec.ofNat 64 0))) (Prog.assign VarKind.local "res" (Exp.var VarKind.local "node")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 160))]) (Exp.const (BitVec.ofNat 64 0))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 168))]) (Exp.const (BitVec.ofNat 64 0))) (Prog.call (some ((some (VarKind.local, "res")), none)) "_collapse_branch" [(Exp.var VarKind.local "node")])))) (Prog.dec "idx" Shape.one (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.var VarKind.local "level")])) (Prog.decCall "fr2" Shape.one "scratch_alloc" [(Exp.const (BitVec.ofNat 64 40))] (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr2"), (Exp.const (BitVec.ofNat 64 0))]) (Exp.var VarKind.local "top")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr2"), (Exp.const (BitVec.ofNat 64 8))]) (Exp.var VarKind.local "node")) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr2"), (Exp.const (BitVec.ofNat 64 16))]) (Exp.const (BitVec.ofNat 64 3))) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fr2"), (Exp.const (BitVec.ofNat 64 32))]) (Exp.var VarKind.local "idx")) (Prog.seq (Prog.assign VarKind.local "top" (Exp.var VarKind.local "fr2")) (Prog.seq (Prog.assign VarKind.local "node" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "node"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "idx"), (Exp.const (BitVec.ofNat 64 8))])]))) (Prog.seq (Prog.assign VarKind.local "level" (Exp.op BinOp.add [(Exp.var VarKind.local "level"), (Exp.const (BitVec.ofNat 64 1))])) (Prog.assign VarKind.local "go" (Exp.const (BitVec.ofNat 64 1)))))))))))))))))))) : Prog Word)

local notation "UGUARD" => ((Exp.cmp Cmp.notEqual (Exp.var VarKind.local "top") (Exp.const (BitVec.ofNat 64 0))) : Exp Word)

local notation "UBODY" => ((Prog.dec "fnode" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 8))])) (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 16))])) (Exp.const (BitVec.ofNat 64 2))) (Prog.call (some ((some (VarKind.local, "res")), none)) "_delete_ext_finish" [(Exp.var VarKind.local "fnode"), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 24))])), (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))])), (Exp.var VarKind.local "res")]) (Prog.seq (Prog.store (Exp.op BinOp.add [(Exp.var VarKind.local "fnode"), (Exp.const (BitVec.ofNat 64 32)), (Exp.panOp PanOp.mul [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 32))])), (Exp.const (BitVec.ofNat 64 8))])]) (Exp.var VarKind.local "res")) (Prog.call (some ((some (VarKind.local, "res")), none)) "_collapse_branch" [(Exp.var VarKind.local "fnode")]))) (Prog.assign VarKind.local "top" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "top"), (Exp.const (BitVec.ofNat 64 0))]))))) : Prog Word)

/-- At the end of the descent the unwind invariant holds. -/
theorem uw_of_dl (hE : GuestEnv E) {Rg : Reg} {G : VarName → Option (PanValue Word)}
    {M : Word → Option (PanValue Word)} {F : FfiState σ} {fv lim : Word} {ℓ0 : Nat}
    {key klen : Word} (hF : 2952790016 ≤ fv.toNat) {a : St σ} {k : Nat}
    (hI : DlI Rg G M F fv lim ℓ0 key klen a) (hc : E.cond a DGUARD = some (0, k)) :
    UwI Rg G M F lim ℓ0 a := by
  obtain ⟨hf, gw, lv, R, topv, resv, nd, sp, ℓ, hle, hW, hg, hsp, hfv, hfs, hsl, hm, k1, k2, k3,
    k4, k5, k6, k7, hst, hgo, hres⟩ := hI
  have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := gw) (by lk [k7]))
    (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hc)
  simp only [PanValue.word.injEq] at hcv
  have hgw : gw = 0#64 := by
    by_contra hne
    simp [evalPanCmp, hne] at hcv
  exact ⟨R, topv, resv, ℓ, sp, hle, hW, hf, hg, hsp, by omega, hsl, hm, k5, k6, hst, hres hgw⟩

/-- Result of `_mpt_delete_node_body`: null or a registered node at level `L`;
the scratch pointer may have moved down from `sp0`, and memory changed only in
the heap and below `sp0`. -/
def DelBQ (Rg : Reg) (s : St σ) (L : Nat) (sp0 : Word) (r : Result σ) : Prop :=
  ∃ l g' m' a R' sp', r = .returned l g' m' s.ffi [.word a] ∧ Rg.Le R' ∧
    (a = 0#64 ∨ ∃ k, R'.Kd a k ∧ k ≠ 0#64 ∧ R'.Lv a L) ∧ WorldTJ R' g' m' ∧
    (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g' x = s.globals x) ∧
    g' "scratch_ptr" = some (.word sp') ∧ sp'.toNat ≤ sp0.toNat ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) → m' addr = s.memory addr

theorem DelBQ.restore {Rg : Reg} {s : St σ} {L : Nat} {sp0 : Word} {r : Result σ} (x : VarName)
    (old : Option (PanValue Word)) (h : DelBQ Rg s L sp0 r) :
    DelBQ Rg s L sp0 (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g', m', a, R', sp', rfl, hq⟩ := h
  exact ⟨_, g', m', a, R', sp', rfl, hq⟩

set_option maxHeartbeats 8000000 in
theorem delete_body_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_mpt_delete_node_body" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (node key klen level sp0 fv : Word)
    (hnode : s.locals "node" = some (.word node)) (hkeyv : s.locals "key" = some (.word key))
    (hklen : s.locals "klen" = some (.word klen))
    (hlevel : s.locals "level" = some (.word level))
    (hW : WorldTJ Rg s.globals s.memory) (hnd : node = 0#64 ∨ ∃ k, Rg.Kd node k)
    (hLn : node ≠ 0#64 → Rg.Lv node level.toNat) (hlv : level.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ DelBQ Rg s level.toNat sp0 r := by
  have hbody := (fun_of_index 278 hE.functions (by guest_decl_at 278) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (DelBQ Rg s level.toNat sp0)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DelBQ Rg s level.toNat sp0) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DelBQ Rg s level.toNat sp0) ?_ (fun r h => h.restore _ _)
  refine WPs.dec (w := 1#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := DelBQ Rg s level.toNat sp0) ?_ (fun r h => h.restore _ _)
  refine WPs.seqG (fun a => UwI Rg s.globals s.memory s.ffi sp0 level.toNat a)
    (WPs.loopG (I := DlI Rg s.globals s.memory s.ffi fv sp0 level.toNat key klen)
      ⟨rfl, 1#64, level, Rg, 0#64, 0#64, node, sp0, level.toNat, Reg.Le.refl Rg, hW,
        fun _ _ _ => rfl, hsp, hfv, hfs, Nat.le_refl _, fun _ _ => rfl, by lk [hkeyv],
        by lk [hklen], by lk [hlevel], by lk [hnode], by lk [], by lk [], by lk [],
        DelStack.nil, fun _ => ⟨rfl, hlv, hnd, hLn⟩, fun h0 => absurd h0 (by decide)⟩
      (fun a hI hct => WPs.conseq (dl_body hE hF hkey hI hct)
        (by rintro r ⟨l, g, m, f, rfl, hI', -⟩; exact hI'))
      (fun a k hI hc => uw_of_dl hE hF hI hc)) ?_
  intro a hU
  refine WPs.seqG (fun b => UwI Rg s.globals s.memory s.ffi sp0 level.toNat b ∧
      ∃ k, E.cond b UGUARD = some (0, k))
    (WPs.loopG (I := UwI Rg s.globals s.memory s.ffi sp0 level.toNat) hU
      (fun b hI hct => WPs.conseq (uw_body hE hI hct)
        (by rintro r ⟨l, g, m, f, rfl, hI', -⟩; exact hI'))
      (fun b k hI hc => ⟨hI, k, hc⟩)) ?_
  rintro b ⟨⟨R, topv, resv, ℓ, sp, hle, hW', hf, hg, hgsp, hsp2, hspl, hm, qtop, qres, hst,
    hres⟩, kk, hc⟩
  have hcv := eval_cmp_inv hE (op := .notEqual) (of_eval (w := topv) (by lk [qtop]))
    (of_eval (w := 0#64) (eval_const _ _)) _ (cond_of_eval hc)
  simp only [PanValue.word.injEq] at hcv
  have htop : topv = 0#64 := by
    by_contra hne
    simp [evalPanCmp, hne] at hcv
  subst htop
  have hℓ := hst.zero
  subst hℓ
  refine WPs.ret (w := resv) (of_eval (by lk [qres])) ?_
  exact ⟨_, b.globals, b.memory, resv, R, sp, by rw [hf], hle, hres, hW', hg, hgsp, hspl, hm⟩

theorem del_ret_cost (hE : GuestEnv E) :
    Costs E (Prog.return (Exp.var VarKind.local "res") : Prog Word) 10 := by
  have h : ∃ B, Costs E (Prog.return (Exp.var VarKind.local "res") : Prog Word) B ∧ B ≤ 10 :=
    ⟨_, by cost_derive [], by decide +kernel⟩
  obtain ⟨B, hB, hle⟩ := h
  exact hB.consequence (fun _ h => h) hle (fun _ h => h)

set_option maxHeartbeats 8000000 in
/-- Step bound of `_mpt_delete_node_body` from a state satisfying the world invariant. -/
theorem delete_body_cost (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "_mpt_delete_node_body" E.functions = some (parameters, body))
    (Rg : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat)
    (node key klen level sp0 fv : Word)
    (hnode : s.locals "node" = some (.word node)) (hkeyv : s.locals "key" = some (.word key))
    (hklen : s.locals "klen" = some (.word klen))
    (hlevel : s.locals "level" = some (.word level))
    (hW : WorldTJ Rg s.globals s.memory) (hnd : node = 0#64 ∨ ∃ k, Rg.Kd node k)
    (hLn : node ≠ 0#64 → Rg.Lv node level.toNat) (hlv : level.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 141 := by
  have hbody := (fun_of_index 278 hE.functions (by guest_decl_at 278) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at hrun
  have hloop1 : Triple E (fun a => DlI Rg s.globals s.memory s.ffi fv sp0 level.toNat key klen a ∧
        insMu a ≤ 2 ^ 64)
      (.while DGUARD DBODY) ((2 ^ 64 + 1) * (expCost DGUARD + 10 ^ 120 + 1))
      (fun r => match r with
        | .normal l g m f => UwI Rg s.globals s.memory s.ffi sp0 level.toNat ⟨l, g, m, f⟩ ∧
            uwMu ⟨l, g, m, f⟩ ≤ 2 ^ 64
        | _ => True) := by
    refine Triple.while_exit (I := DlI Rg s.globals s.memory s.ffi fv sp0 level.toNat key klen)
      (μ := insMu) (Q := fun r => match r with
        | .normal l g m f => UwI Rg s.globals s.memory s.ffi sp0 level.toNat ⟨l, g, m, f⟩ ∧
            uwMu ⟨l, g, m, f⟩ ≤ 2 ^ 64
        | _ => True) (2 ^ 64) (condCost_exp _)
      (fun a hI hc => by
        obtain ⟨k, hc⟩ := hc
        exact ⟨uw_of_dl hE hF hI hc, uwMu_le _⟩) ?_
    intro k
    refine Triple.of_costs (dl_body_cost hE) ?_
    rintro fuel' a r' n' ⟨hI, hk, hct⟩ hrun' hne'
    rcases dl_body hE hF hkey hI hct r' (Runs.of_run hrun') with hst | ⟨l, g, m, f, rfl, hI', hlt⟩
    · cases r' with
      | error l g m f => cases hne'
      | raised l g m f ex val => trivial
      | finalFfi l g m f ev => trivial
      | _ => exact absurd hst (fun h => h)
    · exact ⟨hI', hk ▸ hlt⟩
  have hloop2 : Triple E (fun a => UwI Rg s.globals s.memory s.ffi sp0 level.toNat a ∧
        uwMu a ≤ 2 ^ 64)
      (.while UGUARD UBODY) ((2 ^ 64 + 1) * (expCost UGUARD + 10 ^ 120 + 1))
      (fun r => match r with
        | .normal _ _ _ _ => True
        | _ => True) := by
    refine (Triple.while_exit (I := UwI Rg s.globals s.memory s.ffi sp0 level.toNat)
      (μ := uwMu) (Q := fun _ => True) (2 ^ 64) (condCost_exp _) (fun _ _ _ => trivial)
      ?_).consequence (fun _ h => h) (Nat.le_refl _) (fun r _ => by cases r <;> trivial)
    intro k
    refine Triple.of_costs (uw_body_cost hE) ?_
    rintro fuel' a r' n' ⟨hI, hk, hct⟩ hrun' hne'
    rcases uw_body hE hI hct r' (Runs.of_run hrun') with hst | ⟨l, g, m, f, rfl, hI', hlt⟩
    · cases r' with
      | error l g m f => cases hne'
      | raised l g m f ex val => trivial
      | finalFfi l g m f ev => trivial
      | _ => exact absurd hst (fun h => h)
    · exact ⟨hI', hk ▸ hlt⟩
  have hall := Triple.dec (E := E) (P := fun a => a = s)
    (P' := fun a => a = ⟨updatePanValueMap s.locals "top" (.word 0#64), s.globals, s.memory,
      s.ffi⟩) "top" Shape.one (Exp.const (BitVec.ofNat 64 0)) ?_
    (Triple.dec (P' := fun a => a = ⟨updatePanValueMap (updatePanValueMap s.locals "top"
        (.word 0#64)) "res" (.word 0#64), s.globals, s.memory, s.ffi⟩) "res" Shape.one
      (Exp.const (BitVec.ofNat 64 0)) ?_
      (Triple.dec (P' := fun a => DlI Rg s.globals s.memory s.ffi fv sp0 level.toNat key klen a ∧
          insMu a ≤ 2 ^ 64) "go" Shape.one (Exp.const (BitVec.ofNat 64 1)) ?_
        (Triple.seq (Mid := fun a => UwI Rg s.globals s.memory s.ffi sp0 level.toNat a ∧
            uwMu a ≤ 2 ^ 64) (Q := fun _ => True) hloop1
          (Triple.seq (Mid := fun _ => True) (Q := fun _ => True) hloop2 (del_ret_cost hE)))))
  · have hn := (hall fuel s r n rfl hrun hne).1
    simp only [stepCost_eq] at hn
    refine Nat.le_trans hn ?_
    decide +kernel
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) a 0#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 0#64) val hval
    subst this
    rfl
  · rintro a val rfl hval -
    have := of_eval (eval_const (E := E) _ 1#64) val hval
    subst this
    exact ⟨⟨rfl, 1#64, level, Rg, 0#64, 0#64, node, sp0, level.toNat, Reg.Le.refl Rg, hW,
      fun _ _ _ => rfl, hsp, hfv, hfs, Nat.le_refl _, fun _ _ => rfl, by lk [hkeyv],
      by lk [hklen], by lk [hlevel], by lk [hnode], by lk [], by lk [], by lk [],
      DelStack.nil, fun _ => ⟨rfl, hlv, hnd, hLn⟩, fun h0 => absurd h0 (by decide)⟩, insMu_le _⟩

end InitECandidate.Solver.GuestBound
