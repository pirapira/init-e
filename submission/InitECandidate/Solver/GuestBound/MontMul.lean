import InitECandidate.Solver.GuestBound.MontCols
import InitECandidate.Solver.GuestBound.MontAlg

/-!
# Montgomery multiplication in the bn254 base field: `fq_mul`

After the columns, the digits are packed into four limbs and reduced once.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {Q : Result σ → Prop}

local notation "REDUCE" => ((Prog.decCall "lt" Shape.one "u256_lt" [(Exp.var VarKind.local "r"), (Exp.rStruct [(Exp.const (BitVec.ofNat 64 4332616871279656263)), (Exp.const (BitVec.ofNat 64 10917124144477883021)), (Exp.const (BitVec.ofNat 64 13281191951274694749)), (Exp.const (BitVec.ofNat 64 3486998266802970665))])] (Prog.seq (Prog.ite (Exp.cmp Cmp.equal (Exp.var VarKind.local "lt") (Exp.const (BitVec.ofNat 64 0))) (Prog.call none "u256_sub" [(Exp.var VarKind.local "r"), (Exp.rStruct [(Exp.const (BitVec.ofNat 64 4332616871279656263)), (Exp.const (BitVec.ofNat 64 10917124144477883021)), (Exp.const (BitVec.ofNat 64 13281191951274694749)), (Exp.const (BitVec.ofNat 64 3486998266802970665))])]) Prog.skip) (Prog.return (Exp.var VarKind.local "r")))) : Prog Word)
local notation "PACK" => ((Exp.rStruct [(Exp.op BinOp.or [(Exp.var VarKind.local "u0"), (Exp.shift Shift.lsl (Exp.var VarKind.local "u1") (Exp.const (BitVec.ofNat 64 32)))]), (Exp.op BinOp.or [(Exp.var VarKind.local "u2"), (Exp.shift Shift.lsl (Exp.var VarKind.local "u3") (Exp.const (BitVec.ofNat 64 32)))]), (Exp.op BinOp.or [(Exp.var VarKind.local "u4"), (Exp.shift Shift.lsl (Exp.var VarKind.local "u5") (Exp.const (BitVec.ofNat 64 32)))]), (Exp.op BinOp.or [(Exp.var VarKind.local "u6"), (Exp.shift Shift.lsl (Exp.var VarKind.local "c") (Exp.const (BitVec.ofNat 64 32)))])]) : Exp Word)

theorem shiftl32 (w : Word) : RiscV.panRiscVShift .lsl w 32#64 = some (w <<< (32 : Nat)) := by
  unfold RiscV.panRiscVShift
  rfl

set_option maxHeartbeats 8000000 in
/-- `lt = u256_lt(r, p); if lt == 0 { return u256_sub(r, p); } return r;` -/
theorem reduce_tail (hE : GuestEnv E) (s : St σ) (r : Result σ) (c0 c1 c2 c3 : Word)
    (hrl : s.locals "r" = some (.rStruct [.word c0, .word c1, .word c2, .word c3]))
    (h : Runs E s REDUCE r) :
    Stopped r ∨ ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧
      limbsVal [d0, d1, d2, d3] = if limbsVal [c0, c1, c2, c3] < bnP then limbsVal [c0, c1, c2, c3]
        else limbsVal [c0, c1, c2, c3] - bnP := by
  rcases runs_decCall_inv h with herr | ⟨ps2, cb2, vals2, cl2, rb2, hl2, hvals2, hbind2, hcal2,
    hout2⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams2 := (fun_of_index 46 hE.functions (by guest_decl_at 46) (by decide +kernel) hl2).2
  simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local, hrl,
    evalF_rStruct, eval_const, Option.map_some, Option.some.injEq] at hvals2
  subst hvals2
  rw [hparams2] at hbind2
  simp [bindPanValueParameters] at hbind2
  have hlt := u256_lt_spec hE ps2 cb2 hl2 ⟨cl2, s.globals, s.memory, s.ffi⟩ rb2 c0 c1 c2 c3
    4332616871279656263#64 10917124144477883021#64 13281191951274694749#64 3486998266802970665#64
    (by rw [← hbind2]; simp [updatePanValueMap]) (by rw [← hbind2]; simp [updatePanValueMap]) hcal2
  subst hlt
  obtain ⟨r2, -, hrun2, rfl⟩ := hout2
  obtain ⟨r3, h3, hrest⟩ := runs_seq.mp hrun2
  rw [bnP_limbs] at h3
  have hCb : limbsVal [c0, c1, c2, c3] < 2 ^ 256 := by
    have := c0.isLt; have := c1.isLt; have := c2.isLt; have := c3.isLt
    simp only [limbsVal]
    omega
  simp only [bnP] at h3 ⊢
  rw [runs_ite] at h3
  by_cases hlt : limbsVal [c0, c1, c2, c3] <
      21888242871839275222246405745257275088696311157297823662689037894645226208583
  · simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      eval_const, hlt, if_true, if_false, evalPanCmp] at h3
    rw [runs_skip] at h3
    subst h3
    simp only at hrest
    rw [runs_return] at hrest
    simp (config := { decide := true }) only [evalF_local, update_lookup, hrl, payload_words4,
      if_true, if_false] at hrest
    subst hrest
    exact Or.inr ⟨_, c0, c1, c2, c3, rfl, (if_pos hlt).symm⟩
  · simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      eval_const, hlt, if_true, if_false, evalPanCmp] at h3
    have herror : r3.isError = true → Stopped (restorePanValueFfiLocal "lt" (s.locals "lt") r2) := by
      intro herr
      have hr2 : r2.isError = true := by
        cases r3 with
        | error l g m f =>
          simp only at hrest
          subst hrest
          rfl
        | _ => cases herr
      exact Stopped.restore (Stopped.of_error hr2)
    rcases runs_call_inv none h3 with herr | ⟨ps3, cb3, vals3, cl3, rb3, hl3, hvals3, hbind3,
      hcal3, hout3⟩
    · exact Or.inl (herror herr)
    have hparams3 := (fun_of_index 57 hE.functions (by guest_decl_at 57) (by decide +kernel)
      hl3).2
    simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local,
      update_lookup, hrl, evalF_rStruct, eval_const, Option.map_some, Option.some.injEq, if_true,
      if_false] at hvals3
    subst hvals3
    rw [hparams3] at hbind3
    simp [bindPanValueParameters] at hbind3
    obtain ⟨l3, e0, e1, e2, e3, rfl, he⟩ := u256_sub_mod hE ps3 cb3 hl3
      ⟨cl3, s.globals, s.memory, s.ffi⟩ rb3 c0 c1 c2 c3 4332616871279656263#64 10917124144477883021#64 13281191951274694749#64 3486998266802970665#64
      (by rw [← hbind3]; simp [updatePanValueMap]) (by rw [← hbind3]; simp [updatePanValueMap])
      hcal3
    simp only [CallOutcome] at hout3
    rcases hout3 with herr | ⟨l', rfl⟩
    · exact Or.inl (herror herr)
    simp only at hrest
    subst hrest
    refine Or.inr ⟨_, e0, e1, e2, e3, rfl, ?_⟩
    rw [he, bnP_limbs]
    refine Eq.trans ?_ (if_neg hlt).symm
    simp only [bnP]
    omega

end InitECandidate.Solver.GuestBound
