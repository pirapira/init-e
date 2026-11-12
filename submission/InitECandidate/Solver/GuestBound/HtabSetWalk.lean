import InitECandidate.Solver.GuestBound.HtabSetLink

/-!
# Hash tables: the second descent of `htab_set`

With `d` the first bit where the new key differs from the leaf found, the
loop walks from the root along the key and stops at the first node whose bit
is not below `d`. That node is the leaf found or one of its ancestors.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem WPs.brk (h : Q (.broke s.locals s.globals s.memory s.ffi)) : WPs E s .break Q := by
  intro r hr
  rw [runs_break] at hr
  subst hr
  exact Or.inr h

local notation "WALK_COND" => ((Exp.cmp Cmp.notEqual (Exp.var VarKind.local "n") (Exp.const (BitVec.ofNat 64 0))) : Exp Word)
local notation "WALK_BODY" => ((Prog.dec "b" Shape.one (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 24))])) (Prog.seq (Prog.ite (Exp.cmp Cmp.notLower (Exp.var VarKind.local "b") (Exp.var VarKind.local "d")) Prog.break Prog.skip) (Prog.seq (Prog.assign VarKind.local "p" (Exp.var VarKind.local "n")) (Prog.ite (Exp.cmp Cmp.equal (Exp.op BinOp.and [(Exp.shift Shift.lsr (Exp.loadByte (Exp.op BinOp.add [(Exp.var VarKind.local "key"), (Exp.shift Shift.lsr (Exp.var VarKind.local "b") (Exp.const (BitVec.ofNat 64 3)))])) (Exp.op BinOp.sub [(Exp.const (BitVec.ofNat 64 7)), (Exp.op BinOp.and [(Exp.var VarKind.local "b"), (Exp.const (BitVec.ofNat 64 7))])])), (Exp.const (BitVec.ofNat 64 1))]) (Exp.const (BitVec.ofNat 64 0))) (Prog.assign VarKind.local "n" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 8))]))) (Prog.assign VarKind.local "n" (Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.local "nodes"), (Exp.panOp PanOp.mul [(Exp.var VarKind.local "n"), (Exp.const (BitVec.ofNat 64 32))]), (Exp.const (BitVec.ofNat 64 16))]))))))) : Prog Word)

/-- Locals the descent leaves alone. -/
def walkKeep : List VarName := ["t", "key", "value", "d", "nodes"]

/-- Where the descent stands: `n` is the leaf or one of its ancestors, `p` is
its parent, and `p` tests a bit below `d`. -/
def WalkFacts (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind)
    (L : Nat) (d nw pw : Word) : Prop :=
  LiveN v kind nw.toNat ∧ Anc m v nw.toNat L ∧ Rd m (nodeField v nw.toNat 0) pw ∧
    (pw ≠ 0 → ∃ bp, Rd m (nodeField v pw.toNat 24) bp ∧ bp.toNat < d.toNat)

set_option maxHeartbeats 16000000 in
theorem set_walk (hE : GuestEnv E) {t keyp d L : Word} {v : HtabV} {kind : Nat → NodeKind}
    {rep : KeyRep} {κ : Word → Bool} (hok : HtabOK s.memory t v kind rep)
    (hL : LiveN v kind L.toNat) (hLk : kind L.toNat = .leaf)
    (hpa : PathAgree s.memory v rep κ L.toNat) (hdlt : d.toNat < (v.kl * 8#64).toNat)
    (hkey : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat → KeyBitIs 8#64 s.memory keyp j (κ j))
    (hnodes : s.locals "nodes" = some (.word v.nodes)) (hkp : s.locals "key" = some (.word keyp))
    (hd : s.locals "d" = some (.word d)) (hp : s.locals "p" = some (.word 0#64))
    (hn : s.locals "n" = some (.word v.root)) :
    WPs E s (.while WALK_COND WALK_BODY) (fun r => ∃ l nw pw bn,
      r = .normal l s.globals s.memory s.ffi ∧ (∀ x, x ∈ walkKeep → l x = s.locals x) ∧
      l "n" = some (.word nw) ∧ l "p" = some (.word pw) ∧
      WalkFacts s.memory v kind L.toNat d nw pw ∧ Rd s.memory (nodeField v nw.toNat 24) bn ∧
      d.toNat ≤ bn.toNat) := by
  have hwf := hok.wf
  have hk := hok.keys
  have hlay := hwf.layout
  have hnxl := hwf.next_le
  have ofn : ∀ x : Word, BitVec.ofNat 64 x.toNat = x := fun x => by simp
  obtain ⟨bL, hbL⟩ := live_bit hwf hL
  have hra : Anc s.memory v v.root.toNat L.toNat :=
    root_anc hwf hk (bL.toNat + 1) L.toNat bL hL hbL (by omega)
  have hrl : LiveN v kind v.root.toNat := by
    by_cases hne : v.root.toNat = L.toNat
    · rw [hne]
      exact hL
    · exact (anc_internal hwf hk hra hL hne).1
  have hr0 : Rd s.memory (nodeField v v.root.toNat 0) 0#64 := by
    rcases hwf.root_ok with h | ⟨-, -, -, h⟩
    · have h1 := hrl.1
      rw [h] at h1
      exact absurd h1 (by decide)
    · exact h
  have hL24 : Rd s.memory (nodeField v L.toNat 24) (v.kl * 8#64) := by
    obtain ⟨_, _, _, -, -, -, hb, -⟩ := hwf.leaf_ok _ hL.1 hL.2.1 hLk
    exact hb
  refine WPs.loopB (I := fun a => a.globals = s.globals ∧ a.memory = s.memory ∧ a.ffi = s.ffi ∧
      (∀ x, x ∈ walkKeep → a.locals x = s.locals x) ∧ ∃ nw pw, a.locals "n" = some (.word nw) ∧
      a.locals "p" = some (.word pw) ∧ WalkFacts s.memory v kind L.toNat d nw pw)
    ⟨rfl, rfl, rfl, fun _ _ => rfl, v.root, 0#64, hn, hp, hrl, hra, hr0,
      fun h => absurd rfl h⟩ ?_ ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, hkeep, nw, pw, hn', hp', hlive, hanc, hpar, hpb⟩ -
    simp only at hg hm hf hkeep hn' hp'
    subst hg hm hf
    obtain ⟨bv, hb⟩ := live_bit hwf hlive
    have hnle : nw.toNat ≤ v.nc.toNat := by have := hlive.2.1; omega
    have hnodes' : la "nodes" = some (.word v.nodes) :=
      (hkeep "nodes" (by simp [walkKeep])).trans hnodes
    have hkp' : la "key" = some (.word keyp) := (hkeep "key" (by simp [walkKeep])).trans hkp
    have hd' : la "d" = some (.word d) := (hkeep "d" (by simp [walkKeep])).trans hd
    refine WPs.dec (eval_load_rd hE (eval_node hE hlay (idx := "n") hnle hnodes' hn' 24#64
      (by decide)) hb) ?_
    by_cases hge : d.toNat ≤ bv.toNat
    · have hnl : ¬ bv < d := by rw [BitVec.lt_def]; omega
      refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
      refine WPs.ite (w := 1#64) (fun y hy => by
        rw [eval_cmp_inv hE (of_eval (w := bv) (by lk [])) (of_eval (w := d) (by lk [hd'])) y hy]
        simp [evalPanCmp, hnl]) ?_
      split
      · rename_i h10
        exact absurd h10 (by decide)
      refine WPs.brk ?_
      simp only [restorePanValueFfiLocal]
      rw [restore_update]
      exact ⟨la, nw, pw, bv, rfl, hkeep, hn', hp', ⟨hlive, hanc, hpar, hpb⟩, hb, hge⟩
    · have hlt : bv.toNat < d.toNat := by omega
      have hlt' : bv < d := by rw [BitVec.lt_def]; exact hlt
      refine WPs.guard0 (fun y hy => by
        rw [eval_cmp_inv hE (of_eval (w := bv) (by lk [])) (of_eval (w := d) (by lk [hd'])) y hy]
        simp [evalPanCmp, hlt']) ?_
      have hne : nw.toNat ≠ L.toNat := by
        intro e
        rw [e] at hb
        have := Rd.inj hb hL24
        rw [this] at hlt
        omega
      have hkd := (anc_internal hwf hk hanc hL hne).2
      obtain ⟨p', lc, rc, b', -, hlc, hrc, hb', hbne, -, hcl, hcr, -⟩ :=
        hwf.internal_ok _ hlive.1 hlive.2.1 hkd
      have eb : bv = b' := Rd.inj hb hb'
      subst eb
      obtain ⟨-, hleft, hright⟩ := anc_child hwf hk hanc hL hne bv lc rc bL hb hlc hrc hbL
      have hrepb : rep L.toNat bv = κ bv := hpa nw.toNat hanc hne bv hb
      refine WPs.seq (fun a' => a' = ⟨updatePanValueMap (updatePanValueMap la "b" (.word bv)) "p"
        (.word nw), s.globals, s.memory, s.ffi⟩)
        (WPs.assign (old := pw) (by lk [hp']) (of_eval (w := nw) (by lk [hn']))
          ⟨_, _, _, _, rfl, rfl⟩) ?_
      rintro _ rfl
      have step : ∀ (off c : Word), off.toNat < 32 →
          Rd s.memory (nodeField v nw.toNat off.toNat) c → ChildOk s.memory v kind nw.toNat c →
          Anc s.memory v c.toNat L.toNat →
          WPs E ⟨updatePanValueMap (updatePanValueMap la "b" (.word bv)) "p" (.word nw), s.globals,
              s.memory, s.ffi⟩
            (.assign .local "n" (.load .one (.op .add [.var .local "nodes",
              .panOp .mul [.var .local "n", .const 32#64], .const off])))
            (fun r' => match restorePanValueFfiLocal "b" (la "b") r' with
              | .normal l g m f | .continued l g m f =>
                  g = s.globals ∧ m = s.memory ∧ f = s.ffi ∧
                  (∀ x, x ∈ walkKeep → l x = s.locals x) ∧ ∃ nw pw, l "n" = some (.word nw) ∧
                  l "p" = some (.word pw) ∧ WalkFacts s.memory v kind L.toNat d nw pw
              | .broke l g m f => ∃ l' nw pw bn,
                  (.normal l g m f : Result σ) = .normal l' s.globals s.memory s.ffi ∧
                  (∀ x, x ∈ walkKeep → l' x = s.locals x) ∧
                  l' "n" = some (.word nw) ∧ l' "p" = some (.word pw) ∧
                  WalkFacts s.memory v kind L.toNat d nw pw ∧
                  Rd s.memory (nodeField v nw.toNat 24) bn ∧ d.toNat ≤ bn.toNat
              | r => ∃ l' nw pw bn, r = .normal l' s.globals s.memory s.ffi ∧
                  (∀ x, x ∈ walkKeep → l' x = s.locals x) ∧
                  l' "n" = some (.word nw) ∧ l' "p" = some (.word pw) ∧
                  WalkFacts s.memory v kind L.toNat d nw pw ∧
                  Rd s.memory (nodeField v nw.toNat 24) bn ∧ d.toNat ≤ bn.toNat) := by
        intro off c hoff hc hch hca
        refine WPs.assign (old := nw) (by lk [hn'])
          (eval_load_rd hE (eval_node hE hlay (idx := "n") hnle (by lk [hnodes']) (by lk [hn'])
            off hoff) hc) ?_
        simp only [restorePanValueFfiLocal]
        refine ⟨trivial, trivial, trivial, ?_, c, nw, ?_, ?_, ⟨hch.1, hch.2.1, hch.2.2.1⟩, hca,
          (ofn nw) ▸ hch.2.2.2, fun _ => ⟨bv, hb, hlt⟩⟩
        · intro x hx
          simp only [walkKeep, List.mem_cons, List.mem_nil_iff, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;>
            simp (config := { decide := true }) [restorePanValueLocal, update_lookup] <;>
            exact hkeep _ (by simp [walkKeep])
        · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
        · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      refine WPs.ite (c := htBitZeroV "b") (fun x hx => htbit_cond_v hE "b" (kp := keyp) (bv := bv) (bit := κ bv) (by lk [hkp']) (by lk [])
        (by rw [hE.bytes]; exact hkey bv (by omega)) hx) ?_
      cases hκ : κ bv with
      | false =>
        split
        · rename_i h0
          simp at h0
        · exact step 8#64 lc (by decide) hlc hcl (hleft (hrepb.trans hκ))
      | true =>
        split
        · exact step 16#64 rc (by decide) hrc hcr (hright (hrepb.trans hκ))
        · rename_i h0
          simp at h0
  · rintro a k ⟨-, -, -, -, nw, pw, hn', -, hlive, -⟩ hcond
    rw [cond_eq] at hcond
    simp [evalF_cmp hE.word, hn', evalPanCmp] at hcond
    have h1 := hlive.1
    rw [hcond.1] at h1
    exact absurd h1 (by decide)

end InitECandidate.Solver.GuestBound
