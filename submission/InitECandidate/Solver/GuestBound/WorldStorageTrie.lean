import InitECandidate.Solver.GuestBound.WorldHtabSet
import InitECandidate.Solver.GuestBound.TrieMptNew

/-!
# `ws_storage_trie` against the world invariant

`ws_storage_trie(root)` returns the storage trie for a root hash, decoding it
from the witness on first use and remembering it in the table at `ws + 32`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- What `ws_storage_trie` guarantees. -/
def WstQ (R0 : Reg) (s : St σ) (sp0 : Word) (r : Result σ) : Prop :=
  ∃ l g m, ∃ (res : Word) (R : Reg), r = .returned l g m s.ffi [.word res] ∧ R0.Le R ∧
    WorldTJ R g m ∧ (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ sp0.toNat ≤ addr.toNat) → m addr = s.memory addr

theorem WstQ.restore {R0 : Reg} {sp0 : Word} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : WstQ R0 s sp0 r) : WstQ R0 s sp0 (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, g, m, res, R, rfl, hk⟩ := h
  exact ⟨_, g, m, res, R, rfl, hk⟩

theorem eval_gaddc (hE : GuestEnv E) {s : St σ} {x : VarName} {a : Word} (k : Word)
    (hx : s.globals x = some (.word a)) :
    E.eval s (.op .add [.var .global x, .const k]) = some (.word (a + k)) := by
  simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, eval_global, hx, wordsProj_cons,
    wordsProj_nil, wordOp]

set_option maxHeartbeats 16000000 in
theorem ws_storage_trie_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "ws_storage_trie" E.functions = some (parameters, body))
    (R0 : Reg) (s : St σ) (r : Result σ) (root wsv t dbv kl sp0 fv : Word)
    (hroot : s.locals "root" = some (.word root)) (hws : s.globals "ws" = some (.word wsv))
    (hct : R0.Cn (wsv + 32#64) t) (hcd : R0.Cn (wsv + 0#64) dbv) (hD : R0.D t kl)
    (hkey : KeyLoc R0 root kl ∨ root.toNat + kl.toNat ≤ HBASE) (hk64 : root.toNat + kl.toNat < 2 ^ 64)
    (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ WstQ R0 s sp0 r := by
  have hbody := (fun_of_index 368 hE.functions (by guest_decl_at 368) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (WstQ R0 s sp0)) r h
  have hsp0 := sp0.isLt
  refine WPs.dec (w := t) (eval_load_rd hE (eval_gaddc hE 32#64 hws) (hW.cell hct)) ?_
  refine WPs.conseq (Q' := WstQ R0 s sp0) ?_ (fun r h => h.restore)
  refine WPs.decCall_retS (fun v0 g0 m0 f0 hret hsh =>
    WPs.conseq (Q' := WstQ R0 s sp0) ?_ (fun r h => h.restore))
  obtain ⟨hg0, hm0, hf0⟩ := CalleeRet.quiet (htab_get_quiet hE) hret
  subst g0 m0 f0
  obtain ⟨o0, o1, rfl⟩ := struct2_of_shape hsh
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qt : L "t" = some (.word t) := by rw [hLL]; lk []
  have qroot : L "root" = some (.word root) := by rw [hLL]; lk [hroot]
  have qm : L "m" = some (.rStruct [.word o0, .word o1]) := by rw [hLL]; lk []
  clear hLL
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact WPs.skip rfl
    · refine WPs.ret_ev (fun v hv => ?_)
      obtain ⟨_, _, w', _, _, _, rfl⟩ := eval_op2_inv hE.word hv
      exact ⟨_, _, _, w', R0, rfl, Reg.Le.refl R0, hW, fun _ _ => rfl, fun _ _ => rfl⟩
  intro a ha
  rw [ha]
  clear ha a
  refine WPs.decCall_ret (fun vn g m ffi hret =>
    WPs.conseq (Q' := WstQ R0 s sp0) ?_ (fun r h => h.restore))
  have hdbe : E.eval (⟨L, s.globals, s.memory, s.ffi⟩ : St σ)
      (.load .one (.op .add [.var .global "ws", .const 0#64])) = some (.word dbv) := by
    obtain ⟨pw, he⟩ := calleeRet_load1 hE hret (addr := wsv + 0#64)
      (of_eval (eval_gaddc hE 0#64 hws))
    have := eval_load_rd hE (s := (⟨L, s.globals, s.memory, s.ffi⟩ : St σ))
      (eval_gaddc hE 0#64 hws) (hW.cell hcd) _ he
    rw [he, this]
  obtain ⟨res, R, rfl, rfl, hle, hW', -, hg, hm⟩ := decode_witness_to_mpt_ret hE hret
    (dbv := dbv) (rh := root) hdbe (by lk [qroot]) hW hsp hfv hfs hF
  dsimp only at hg hm
  have hD' : R.D t kl := by rw [hle.D]; exact hD
  have hkey' : KeyLoc R root kl ∨ root.toNat + kl.toNat ≤ HBASE := by
    unfold KeyLoc at hkey ⊢
    rw [hle.B]
    exact hkey
  refine WPs.seq_call_ret (fun vs g2 m2 f2 hret2 => ?_)
  obtain ⟨rfl, hW2, hg2, hm2⟩ := htab_set_retW hE hret2 (t := t) (keyp := root)
    (val := res + 1#64) (kl := kl) (by lk [qt]) (by lk [qroot])
    (eval_addc hE 1#64 (by lk [])) hD' hkey' hk64 hW'
  dsimp only at hg2 hm2
  refine WPs.ret (w := res) (of_eval (by lk [])) ?_
  exact ⟨_, g2, m2, res, R, rfl, hle, hW2, fun x hx => (hg2 x hx).trans (hg x hx),
    fun addr ha => (hm2 addr (by omega)).trans (hm addr ha)⟩

end InitECandidate.Solver.GuestBound
