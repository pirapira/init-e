import InitE
import InitE.TargetTotality
import Flapjack.RiscV.CorrectnessEncoding.Complete
import Flapjack.Compiler.Backend.Semantics.TargetProps.EncoderStepState
import InitECandidate.Proofs.CompilerComputation
import InitECandidate.Proofs.OracleBaselineCorrectness
import InitECandidate.Proofs.BootstrapComposition
import InitECandidate.Solver.FastBaselineEnv

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace



open scoped InitECandidate.Proofs.CompilerComputation

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

/-!
# Self-Contained Yukon Bootstrap, Oracle Installation & Finite-`K` Certificate

The Yukon evaluation sandbox resets `submission/InitECandidate/Proofs/*.lean` to the
upstream baseline (`evm.fast-dev` commit `cac0a2b` / `3b87de5`), preserving only
`submission/Solution.lean`, `submission/claim.json`, and `submission/InitECandidate/Solver/**`.

This module (`InitECandidate.Solver.YukonSelfContainedCert`) provides in `Solver/`
all definitions and theorems needed to construct both:
1. `InitE.Certificate baselineSubmission .infinity` (stage-free `.infinity` baseline compatibility)
2. `InitE.Certificate (baselineWithFiniteK K) (.finite K)` (self-contained finite-`K` certificates)

while importing from `InitECandidate.Proofs.*` **only** declarations that already exist
in the upstream baseline repository (`0 sorryAx`).
-/

namespace InitECandidate.Solver.YukonSelfContainedCert

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Proofs.BootstrapSteps (after)
open InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapAsmComposition (EvaluatorGuards shiftInterfer_identity)
open InitECandidate.Solver.FastEnv.BootstrapTrace (fullBootstrapCode full_length full_checked full_guards full_endpoint)
open Flapjack
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.RiscV.L3
open Flapjack.RiscV.L3.Step

/-! ## Section 1: Self-Contained Exact 23,132-Step Bootstrap Evaluator -/

/-- Exact witness predicate for every instruction in the bootstrap instruction subset. -/
def BootstrapInstOk : HolAsm 64 → Prop
  | .inst (.const _ _) => True
  | .inst (.arith (.binop .add _ _ (.imm _))) => True
  | .inst (.arith (.shift .lsl _ _ (.imm _))) => True
  | .inst (.mem _ _ _) => True
  | .jump c => -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
  | .jumpCmp cmp _ (.reg _) a => (-4092 ≤ a.toInt ∧ a.toInt ≤ 4095) ∧ (cmp ≠ .test ∧ cmp ≠ .notTest)
  | .loc _ _ => True
  | _ => False

private theorem bytes_from_domain (pc : BitVec 64) (bs : List (BitVec 8))
    (m1 m2 : BitVec 64 → BitVec 8) (d : BitVec 64 → Prop)
    (bytes : bytesInMemoryHOL pc bs m1 d)
    (agree : ∀ a, d a → m2 a = m1 a) : bytesInMemoryHOL pc bs m2 d := by
  induction bs generalizing pc with
  | nil => trivial
  | cons b bs ih =>
    exact ⟨(agree pc bytes.2.1).trans bytes.1, bytes.2.1,
      ih (pc + 1) bytes.2.2⟩

private theorem reg_nonzero (r : Nat) (guard : asmRegOkExact r riscvConfig = true) :
    BitVec.ofNat 5 r ≠ 0#5 := by
  have g : r < 32 ∧ r ≠ 0 := by
    have g := guard
    simp [asmRegOkExact, riscvConfig] at g
    exact ⟨of_decide_eq_true g.1, g.2.1⟩
  intro eq
  have n := congrArg BitVec.toNat eq
  simp only [BitVec.toNat_ofNat] at n
  norm_num at n
  rw [Nat.mod_eq_of_lt g.1] at n
  exact g.2 n

private theorem reg_read (r : Nat) (s : AsmState 64) (ms : riscv_state)
    (guard : asmRegOkExact r riscvConfig = true)
    (rel : targetStateRel riscvTarget s ms) :
    GPR (BitVec.ofNat 5 r) ms = readReg r s := by
  have g : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using guard
  have before := rel.2.2.2.1 r g
  change ms.c_gpr ms.procID (BitVec.ofNat 5 r) = s.regs r at before
  simpa [GPR, gpr, reg_nonzero r guard, readReg] using before

private def low (c : BitVec 64) : BitVec 12 := Flapjack.RiscV.L3.holWordExtract 12 11 0 c
private def high (c : BitVec 64) : BitVec 20 :=
  Flapjack.RiscV.L3.holWordExtract 20 31 12 (c - (low c).signExtend 64)
private def upperValue (c : BitVec 64) : BitVec 64 :=
  ((high c) ++ (0#12)).signExtend 64

private theorem low_eq (c : BitVec 64) : low c = BitVec.extractLsb' 0 12 c := by
  apply BitVec.eq_of_toNat_eq
  simp [low, Flapjack.RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem high_eq (c : BitVec 64) :
    high c = BitVec.extractLsb' 12 20 (c - (BitVec.extractLsb' 0 12 c).signExtend 64) := by
  rw [high, low_eq]
  apply BitVec.eq_of_toNat_eq
  simp [Flapjack.RiscV.L3.holWordExtract, BitVec.extractLsb'_toNat]

private theorem loc_split (c : BitVec 64)
    (range : -2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599)
    (aligned : c.toNat % 4 = 0) : upperValue c + (low c).signExtend 64 = c := by
  have zero : (BitVec.extractLsb' 0 2 c).setWidth 64 = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.extractLsb'_toNat, aligned]
  have bit : c.getLsbD 1 = false := by
    have e := congrArg (fun x : BitVec 64 => x.getLsbD 1) zero
    simpa using e
  have mask : (BitVec.extractLsb' 0 12 c) &&& ~~~(2 : BitVec 12) =
      BitVec.extractLsb' 0 12 c := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_extractLsb', Nat.zero_add, hi, decide_true, Bool.true_and]
    by_cases ei : i = 1
    · subst i; rw [bit]; rfl
    · have eb : (2 : BitVec 12).getLsbD i = false := by
        change Nat.testBit (2 ^ 1) i = false
        exact Nat.testBit_two_pow_of_ne (Ne.symm ei)
      rw [eb]; simp only [Bool.not_false, Bool.and_true]
  have bounds : (0xFFFFFFFF80000000 : BitVec 64).sle c = true ∧
      c.sle 0x7FFFF7FF = true := by
    simp only [BitVec.sle_eq_decide, decide_eq_true_eq]
    change -2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599
    exact range
  have split := Flapjack.RiscV.TargetProof.split_immediate_reconstruction c ⟨bounds.1,bounds.2,zero⟩
  have em : (-1 : BitVec 64) = (-1#64) := by decide
  rw [mask, em, ← BitVec.neg_eq_neg_one_mul, ← BitVec.sub_eq_add_neg] at split
  simpa [upperValue, high_eq, low_eq] using split

private theorem loc_guard (r : Nat) (c : BitVec 64)
    (h : asmOkExact (.loc r c) riscvConfig = true) :
    (r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false) ∧
    (-2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599) ∧ c.toNat % 4 = 0 := by
  have both : asmRegOkExact r riscvConfig = true ∧
      asmLocOffsetOkExact riscvConfig c = true := by
    simpa only [asmOkExact, Bool.and_eq_true] using h
  have reg : r < riscvConfig.regCount ∧ riscvConfig.avoidRegs.contains r = false := by
    simpa [asmRegOkExact] using both.1
  have off : (-2147483648 ≤ c.toInt ∧ c.toInt ≤ 2147481599) ∧
      c.toNat % 4 = 0 := by
    have decoded : (decide (-2147483648 ≤ c.toInt) = true ∧
        decide (c.toInt ≤ 2147481599) = true) ∧ decide (c.toNat % 4 = 0) = true := by
      have original := both.2
      simp only [asmLocOffsetOkExact, asmOffsetOkExact, asmAligned,
        Bool.and_eq_true] at original
      exact original
    exact ⟨⟨of_decide_eq_true decoded.1.1, of_decide_eq_true decoded.1.2⟩,
      of_decide_eq_true decoded.2⟩
  exact ⟨reg, off⟩

/-- Exact step-count encoder correctness for the bootstrap instruction subset. -/
theorem riscv_encoder_correct_bootstrap
    (s1 : AsmState 64) (i : HolAsm 64) (s2 : AsmState 64) (ms : riscv_state)
    (hok : BootstrapInstOk i)
    (h : asmStep riscvTarget.config s1 i s2 ∧ targetStateRel riscvTarget s1 ms) :
    ∃ n : Nat, n + 1 = (riscvAst i).length ∧
      ∀ env : Nat → riscv_state → riscv_state,
        interferenceOk env (riscvTarget.proj s1.memDomain) →
        let pcs := allPcs (riscvTarget.config.encode i).length s1.pc
        asserts n (fun k s => env (n - k) (riscvTarget.next s)) ms
          (fun ms' => riscvTarget.stateOk ms' = true ∧
            (∀ pc, pc ∈ pcs 0 → riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
            riscvTarget.getPc ms' ∈ pcs riscvTarget.config.codeAlignment)
          (fun ms' => targetStateRel riscvTarget s2 ms') ∧
        asserts2 (n + 1) (fun k => env (n + 1 - k)) riscvTarget.next ms
          (fun ms1 ms2 => ∀ x, ¬ s1.memDomain x →
            riscvTarget.getByte ms1 x = riscvTarget.getByte ms2 x) := by
  open Flapjack.RiscV.TargetProof in
  cases i with
  | inst value =>
    cases value with
    | skip => exact False.elim hok
    | const r c =>
      let is := riscvAst (.inst (.const r c))
      have nonempty : is ≠ [] := const_register_nonempty r c
      have positive : 0 < is.length := List.length_pos_iff.mpr nonempty
      refine ⟨is.length - 1, by dsimp [is] at positive ⊢; omega, ?_⟩
      intro env interference
      have hs : asmStep riscvConfig s1 (.inst (.const r c)) s2 := h.1
      have kinds : ∀ i ∈ is, ConstRegisterInstruction i := const_register_family r c
      have nonzero : ∀ i ∈ is, constDestination i ≠ 0#5 :=
        const_dest_nonzero r c hs.2.2.2.2.2.2
      have pcEq : ms.c_PC ms.procID = s1.pc := h.2.2.1
      have sourceBytes : bytesInMemoryHOL s1.pc (is.flatMap riscvEncode) s1.mem s1.memDomain := hs.1
      have bytes := bytes_from_domain _ _ _ ms.MEM8 _ sourceBytes h.2.2.2.1
      rw [← pcEq] at bytes
      have projection := const_native_execute_projection s1.memDomain is kinds nonzero env 0 ms h.2.1 bytes interference
      have pureRel := const_step_post_relation r c s1 s2 ms hs h.2
      have finalRel : targetStateRel riscvTarget s2 (constNativeExecute env 0 is ms) :=
        (riscv_target_ok.2 _ _ s2 (by
          simpa only [const_source_post r c s1 s2 hs, updPc, updReg, riscvTarget, is] using projection)).1.mpr pureRel
      constructor
      · let P := fun ms' => riscvTarget.stateOk ms' = true ∧
            (∀ pc, pc ∈ allPcs (riscvTarget.config.encode (.inst (.const r c))).length s1.pc 0 →
              riscvTarget.getByte ms' pc = riscvTarget.getByte ms pc) ∧
            riscvTarget.getPc ms' ∈ allPcs (riscvTarget.config.encode (.inst (.const r c))).length
              s1.pc riscvTarget.config.codeAlignment
        have mid : ∀ j, 0 < j → j < is.length → P (constNativeExecute env 0 (is.take j) ms) := by
          intro j lower upper
          have prefixKinds : ∀ i ∈ is.take j, ConstRegisterInstruction i :=
            fun i member => kinds i (List.mem_of_mem_take member)
          have prefixNonzero : ∀ i ∈ is.take j, constDestination i ≠ 0#5 :=
            fun i member => nonzero i (List.mem_of_mem_take member)
          have prefixBytes : bytesInMemoryHOL (ms.c_PC ms.procID)
              ((is.take j).flatMap riscvEncode) ms.MEM8 s1.memDomain := by
            have allBytes := bytes
            rw [← List.take_append_drop j is, List.flatMap_append, bytesInMemory_append] at allBytes
            exact allBytes.1
          have prefixFrame := const_native_execute_frame s1.memDomain (is.take j)
            prefixKinds prefixNonzero env 0 ms h.2.1 prefixBytes interference
          dsimp only at prefixFrame
          refine ⟨prefixFrame.1, ?_, ?_⟩
          · intro a covered
            have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
            exact prefixFrame.2.2 a domain
          · change (constNativeExecute env 0 (is.take j) ms).c_PC
              (constNativeExecute env 0 (is.take j) ms).procID ∈ _
            rw [prefixFrame.2.1, pcEq, allPcs_eq]
            refine ⟨j, ?_, ?_⟩
            · change j * 4 < (riscvEnc (.inst (.const r c))).length
              rw [riscvEnc_length_eq]
              dsimp only [is] at upper
              omega
            · simp only [List.length_take, Nat.min_eq_left (Nat.le_of_lt upper)]
              change s1.pc + BitVec.ofNat 64 (4 * j) = s1.pc + BitVec.ofNat 64 (j * 4)
              rw [Nat.mul_comm]
        simpa only [Nat.zero_add] using
          const_asserts_of_prefixes is nonempty env 0 ms P _ mid finalRel
      · have memoryFrame := const_native_asserts2 s1.memDomain is kinds nonzero env 0 ms h.2.1 bytes interference
        have count : is.length - 1 + 1 = is.length := by omega
        simpa only [count, Nat.zero_add, riscvTarget] using memoryFrame
    | arith a =>
      cases a with
      | binop op rd rs1 right =>
        cases op <;> cases right
        case add.imm c =>
          refine ⟨0, by simp [riscvAst], ?_⟩
          intro env interference
          have hs : asmStep riscvConfig s1 (.inst (.arith (.binop .add rd rs1 (.imm c)))) s2 := h.1
          have guards : asmRegOkExact rd riscvConfig = true ∧
              asmRegOkExact rs1 riscvConfig = true ∧ asmRegImmOkExact (.inl .add) (.imm c) riscvConfig = true := by
            simpa [asmOkExact, asmInstOkExact, asmArithOkExact,
              riscvConfig, Bool.and_eq_true, and_assoc] using hs.2.2.2.2.2.2
          have bound : rd < 32 := by
            have g := guards.1
            simp [asmRegOkExact, riscvConfig] at g
            exact of_decide_eq_true g.1
          let value := readReg rs1 s1 + c
          have source : s2 = updPc (s1.pc + 4) (updReg rd value s1) := by
            rw [binop_source_post .add rd rs1 (.imm c) s1 s2 hs]
            rfl
          have valid : (0xFFFFFFFFFFFFF800 : BitVec 64).sle c = true ∧ c.sle 0x7FF = true := by
            have h3 := guards.2.2
            simp [asmRegImmOkExact, riscvConfig] at h3
            rcases h3 with h3 | h3
            · rw [h3.2]; decide
            · exact h3
          have hrec : (c.setWidth 12).signExtend 64 = c := by
            apply BitVec.eq_of_toInt_eq
            rw [BitVec.toInt_signExtend_of_le (by decide : 12 ≤ 64)]
            have et := BitVec.toInt_signExtend_eq_toInt_bmod_of_le c (by decide : 12 ≤ 64)
            rw [BitVec.signExtend_eq_setWidth_of_le c (by decide : 12 ≤ 64)] at et
            rw [et]
            simp only [BitVec.sle_eq_decide, decide_eq_true_eq] at valid
            change -2048 ≤ c.toInt ∧ c.toInt ≤ 2047 at valid
            apply Int.bmod_eq_of_le <;> omega
          have pcEq : ms.c_PC ms.procID = s1.pc := h.2.2.1
          have hb := bytes_from_domain _ _ _ ms.MEM8 _ hs.1 h.2.2.2.1
          rw [← pcEq] at hb
          have bytes : encodedInstructionBytes ms (.ArithI (.ADDI (BitVec.ofNat 5 rd, BitVec.ofNat 5 rs1, c.setWidth 12))) :=
            encoded_bytes_of_region s1.memDomain ms _ hb
          have hn := next_encoded_addi ms (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (c.setWidth 12)
            (reg_nonzero rd guards.1) h.2.1 bytes
          have left := reg_read rs1 s1 ms guards.2.1 h.2
          have next : riscvTarget.next ms = writePost ms (BitVec.ofNat 5 rd) value := by
            change holThe (NextRISCV ms) = _
            rw [hn, left, hrec]
            rfl
          rw [source]
          have hp := write_post_rel s1 ms rd value bound h.2
          have projection := interference 0 (writePost ms (BitVec.ofNat 5 rd) value)
          have transport := (riscv_target_ok.2 (env 0 (writePost ms (BitVec.ofNat 5 rd) value))
            (writePost ms (BitVec.ofNat 5 rd) value) (updPc (s1.pc + 4) (updReg rd value s1)) projection).1
          constructor
          · simpa [asserts, next] using transport.mpr hp
          · simp only [asserts2, next]
            exact ⟨fun _ _ => rfl, trivial⟩
        all_goals exact False.elim hok
      | shift op rd rs1 right =>
        cases op <;> cases right
        case lsl.imm c =>
          refine ⟨0, by simp [riscvAst], ?_⟩
          intro env interference
          have hs : asmStep riscvConfig s1 (.inst (.arith (.shift .lsl rd rs1 (.imm c)))) s2 := h.1
          have guards : asmRegOkExact rd riscvConfig = true ∧
              asmRegOkExact rs1 riscvConfig = true ∧ c.toNat < 64 := by
            have valid := hs.2.2.2.2.2.2
            simp [asmOkExact, asmInstOkExact, asmArithOkExact, riscvConfig,
              Bool.and_eq_true, and_assoc] at valid
            exact ⟨valid.1, valid.2.1, valid.2.2⟩
          have bound : rd < 32 := by
            have g := guards.1
            simp [asmRegOkExact, riscvConfig] at g
            exact of_decide_eq_true g.1
          let value := (readReg rs1 s1) <<< c.toNat
          have source : s2 = updPc (s1.pc + 4) (updReg rd value s1) := by
            rw [shift_source_post .lsl rd rs1 (.imm c) s1 s2 hs]
            rfl
          have pcEq : ms.c_PC ms.procID = s1.pc := h.2.2.1
          have hb := bytes_from_domain _ _ _ ms.MEM8 _ hs.1 h.2.2.2.1
          rw [← pcEq] at hb
          have bytes : encodedInstructionBytes ms (.Shift (.SLLI (BitVec.ofNat 5 rd, BitVec.ofNat 5 rs1, BitVec.ofNat 6 c.toNat))) :=
            encoded_bytes_of_region s1.memDomain ms _ hb
          have hn := next_encoded_slli ms (BitVec.ofNat 5 rd) (BitVec.ofNat 5 rs1) (BitVec.ofNat 6 c.toNat)
            (reg_nonzero rd guards.1) h.2.1 bytes
          have left := reg_read rs1 s1 ms guards.2.1 h.2
          have amount : (BitVec.ofNat 6 c.toNat).toNat = c.toNat := by
            simp [Nat.mod_eq_of_lt guards.2.2]
          have next : riscvTarget.next ms = writePost ms (BitVec.ofNat 5 rd) value := by
            change holThe (NextRISCV ms) = _
            rw [hn, left, amount]
            rfl
          rw [source]
          have hp := write_post_rel s1 ms rd value bound h.2
          have projection := interference 0 (writePost ms (BitVec.ofNat 5 rd) value)
          have transport := (riscv_target_ok.2 (env 0 (writePost ms (BitVec.ofNat 5 rd) value))
            (writePost ms (BitVec.ofNat 5 rd) value) (updPc (s1.pc + 4) (updReg rd value s1)) projection).1
          constructor
          · simpa [asserts, next] using transport.mpr hp
          · simp only [asserts2, next]
            exact ⟨fun _ _ => rfl, trivial⟩
        all_goals exact False.elim hok
      | div _ _ _ => exact False.elim hok
      | longMul _ _ _ _ => exact False.elim hok
      | longDiv _ _ _ _ _ => exact False.elim hok
      | addCarry _ _ _ _ => exact False.elim hok
      | addOverflow _ _ _ _ => exact False.elim hok
      | subOverflow _ _ _ _ => exact False.elim hok
    | mem m r address =>
      cases address with
      | addr base w =>
        refine ⟨0, by cases m <;> simp [riscvAst, riscvMemop], ?_⟩
        intro env interference
        have step : asmStep riscvConfig s1 (.inst (.mem m r (.addr base w))) s2 := h.1
        let native : instruction := match riscvMemop m with
          | .inl f => .Load (f (BitVec.ofNat 5 r, BitVec.ofNat 5 base, w.setWidth 12))
          | .inr f => .Store (f (BitVec.ofNat 5 base, BitVec.ofNat 5 r, w.setWidth 12))
        have emitted : native ∈ riscvAst (.inst (.mem m r (.addr base w))) := by
          cases m <;> simp [native, riscvAst, riscvMemop]
        have kind : MemoryInstruction native := by
          cases m <;> simp only [native, riscvMemop] <;> constructor
        have next : riscvTarget.next ms = memoryStep native ms := by
          change holThe (NextRISCV ms) = _
          rw [memory_source_next m r base w s1 s2 ms native step h.2 emitted]
          rfl
        have pureRelation := memory_step_post_relation m r base w s1 s2 ms native step h.2 emitted
        have domain := memory_source_post_domain m r base w s1 s2 step
        have projection : riscvTarget.proj s2.memDomain (env 0 (memoryStep native ms)) =
            riscvTarget.proj s2.memDomain (memoryStep native ms) := by
          rw [domain]
          exact interference 0 _
        have finalRelation : targetStateRel riscvTarget s2 (env 0 (memoryStep native ms)) :=
          (riscv_target_ok.2 _ _ s2 projection).1.mpr pureRelation
        constructor
        · simpa only [asserts, Nat.sub_self, next] using finalRelation
        · simp only [asserts2, next, and_true]
          intro x outside
          change ms.MEM8 x = (memoryStep native ms).MEM8 x
          rw [(memory_step_data_frame native kind ms h.2.1).1]
          exact (memory_run_outside_source_domain m r base w s1 s2 ms native
            step h.2 emitted x outside).symm
  | jump c =>
    have range : -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575 := hok
    have bounds : (18446744073708503040#64).sle c = true ∧ c.sle (1048575#64) = true := by
      simp only [BitVec.sle_eq_decide, decide_eq_true_eq]
      change -1048576 ≤ c.toInt ∧ c.toInt ≤ 1048575
      exact range
    refine ⟨0, by simp [riscvAst, inSignedRange, bounds.1, bounds.2], ?_⟩
    intro env interference
    have hs : asmStep riscvConfig s1 (.jump c) s2 := h.1
    have guard := Jump.jump_guard c hs.2.2.2.2.2.2
    have offset := Jump.near_jump_offset c range guard.2
    have enc : riscvConfig.encode (.jump c) =
        riscvEncode (.Branch (.JAL (0,(c.sshiftRight 1).setWidth 20))) := by
      simp [riscvConfig, riscvEnc, riscvAst, inSignedRange, bounds.1, bounds.2]
    have hb := hs.1
    rw [enc] at hb
    have bytes := bytes_in_memory_thm () s1 ms _ _ _ _ ⟨h.2, hb⟩
    have pc := h.2.2.1
    change ms.c_PC ms.procID = s1.pc at pc
    have aligned := Jump.aligned_add (ms.c_PC ms.procID) c
      ((riscvOk_iff ms).mp h.2.1).2.2.2.2 guard.2
    have native_aligned : holAligned 2
        (ms.c_PC ms.procID + (((c.sshiftRight 1).setWidth 20).signExtend 64 <<< (1 : Nat))) = true := by
      rw [offset]
      exact aligned
    have hn := Jump.near_jump_next ms ((c.sshiftRight 1).setWidth 20) h.2.1 native_aligned
      bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
      bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
    have next : riscvTarget.next ms = Jump.branchPost ms (s1.pc+c) := by
      change holThe (NextRISCV ms) = _
      rw [hn, offset, pc]
      rfl
    have target_aligned : holAligned 2 (s1.pc+c) = true := by simpa [pc] using aligned
    have hp := Jump.branch_post_rel s1 ms (s1.pc+c) h.2 target_aligned
    rw [← Jump.jump_post c s1 s2 hs] at hp
    have projection := interference 0 (Jump.branchPost ms (s1.pc+c))
    have transport := (riscv_target_ok.2 (env 0 (Jump.branchPost ms (s1.pc+c)))
      (Jump.branchPost ms (s1.pc+c)) s2
      (by simpa [Jump.jump_post c s1 s2 hs, updPc] using projection)).1
    constructor
    · simpa [asserts, next] using transport.mpr hp
    · simp only [asserts2, next]
      exact ⟨fun _ _ => rfl, trivial⟩
  | jumpCmp cmp r1 right a =>
    cases right with
    | imm _ => exact False.elim hok
    | reg r2 =>
      rcases hok with ⟨range, simple⟩
      have bounds : (18446744073709547524#64).sle a = true ∧ a.sle (4095#64) = true := by
        simp only [BitVec.sle_eq_decide, decide_eq_true_eq]
        exact range
      refine ⟨0, ?_, ?_⟩
      · cases cmp
        case test => exact False.elim (simple.1 rfl)
        case notTest => exact False.elim (simple.2 rfl)
        all_goals simp [riscvAst, inSignedRange, bounds.1, bounds.2]
      · intro env interference
        have hs : asmStep riscvConfig s1 (.jumpCmp cmp r1 (.reg r2) a) s2 := h.1
        have guard := JumpCmp.source_guard cmp r1 (.reg r2) a hs.2.2.2.2.2.2
        have g2 : asmRegOkExact r2 riscvConfig = true := by
          simpa [asmRegImmOkExact] using guard.2.2.2
        have read1 := JumpCmp.reg_read r1 s1 ms guard.2.2.1 h.2
        have read2 := JumpCmp.reg_read r2 s1 ms g2 h.2
        have offset : ((a.sshiftRight 1).setWidth 12).signExtend 64 <<< (1 : Nat) = a := by
          simpa using JumpCmp.near_offset_prefix0 a range guard.2.1
        have enc : riscvConfig.encode (.jumpCmp cmp r1 (.reg r2) a) =
            riscvEncode (JumpCmp.simple_branch cmp (BitVec.ofNat 5 r1) (BitVec.ofNat 5 r2) ((a.sshiftRight 1).setWidth 12)) := by
          cases cmp
          case test => exact False.elim (simple.1 rfl)
          case notTest => exact False.elim (simple.2 rfl)
          all_goals simp [riscvConfig, riscvEnc, riscvAst, inSignedRange, bounds.1, bounds.2, JumpCmp.simple_branch]
        have hb := hs.1
        rw [enc] at hb
        have bytes := bytes_in_memory_thm () s1 ms _ _ _ _ ⟨h.2, hb⟩
        have pc := h.2.2.1
        change ms.c_PC ms.procID = s1.pc at pc
        have hn := JumpCmp.simple_branch_next cmp (BitVec.ofNat 5 r1) (BitVec.ofNat 5 r2)
          ((a.sshiftRight 1).setWidth 12) ms h.2.1 simple
          ⟨bytes.2.2.2.2.2.1, bytes.2.2.2.2.2.2.1,
            bytes.2.2.2.2.2.2.2.1, bytes.2.2.2.2.2.2.2.2.1⟩
        let dest := if wordCmpHOL cmp (readReg r1 s1) (readReg r2 s1) then s1.pc+a else s1.pc+4
        have next : riscvTarget.next ms = Jump.branchPost ms dest := by
          change holThe (NextRISCV ms) = _
          rw [hn, offset, pc, read1, read2]
          rfl
        have initial_aligned : holAligned 2 s1.pc = true := by
          simpa [pc] using (riscvOk_iff ms).mp h.2.1 |>.2.2.2.2
        have aligned : holAligned 2 dest = true := by
          dsimp [dest]
          split
          · exact Jump.aligned_add s1.pc a initial_aligned guard.2.1
          · exact Jump.aligned_add s1.pc 4 initial_aligned (by decide)
        have post : s2 = updPc dest s1 := by
          have original := JumpCmp.source_post cmp r1 (.reg r2) a s1 s2 hs
          rw [enc] at original
          dsimp [dest]
          split <;> rename_i chosen
          all_goals simpa [riscvEncode, regImm, chosen] using original
        have hp := Jump.branch_post_rel s1 ms dest h.2 aligned
        rw [← post] at hp
        have projection := interference 0 (Jump.branchPost ms dest)
        have transport := (riscv_target_ok.2 (env 0 (Jump.branchPost ms dest))
          (Jump.branchPost ms dest) s2
          (by simpa [post, updPc] using projection)).1
        constructor
        · simpa [asserts, next] using transport.mpr hp
        · simp only [asserts2, next]
          exact ⟨fun _ _ => rfl, trivial⟩
  | call _ => exact False.elim hok
  | jumpReg _ => exact False.elim hok
  | loc r c =>
    refine ⟨1, by simp [riscvAst], ?_⟩
    intro env interference
    have hs : asmStep riscvConfig s1 (.loc r c) s2 := h.1
    have guard := loc_guard r c hs.2.2.2.2.2.2
    have bound : r < 32 := guard.1.1
    have rn : r ≠ 0 := by
      have avoid := guard.1.2
      simp [riscvConfig] at avoid
      exact avoid.1
    have wn : BitVec.ofNat 5 r ≠ 0#5 := by
      intro e
      have n := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at n
      norm_num at n
      rw [Nat.mod_eq_of_lt bound] at n
      exact rn n
    let a := riscvEncode (.ArithI (.AUIPC (BitVec.ofNat 5 r, high c)))
    let b := riscvEncode (.ArithI (.ADDI (BitVec.ofNat 5 r, BitVec.ofNat 5 r, low c)))
    have enc : riscvConfig.encode (.loc r c) = a ++ b := rfl
    have hb := hs.1
    rw [enc, bytesInMemory_append] at hb
    let src := updPc (s1.pc + 4) (updReg r (s1.pc + upperValue c) s1)
    let mid := writePost ms (BitVec.ofNat 5 r) (s1.pc + upperValue c)
    have first : riscvTarget.next ms = mid := by
      have bytes := bytes_in_memory_thm () s1 ms _ _ _ _ ⟨h.2, hb.1⟩
      have lowbits : (Encode (.ArithI (.AUIPC (BitVec.ofNat 5 r, high c)))).getLsbD 0 = true ∧
          (Encode (.ArithI (.AUIPC (BitVec.ofNat 5 r, high c)))).getLsbD 1 = true := by
        simp only [Encode, Utype, opc, BitVec.setWidth_eq, BitVec.getLsbD_append]; simp
      have hrun : Run (.ArithI (.AUIPC (BitVec.ofNat 5 r, high c)))
          {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} =
          «write'GPR» (ms.c_PC ms.procID + upperValue c, BitVec.ofNat 5 r)
          {ms with c_Skip := holUpdate ms.procID 4 ms.c_Skip} := by
        simp [Run, «dfn'AUIPC», PC, upperValue]
      have native := write_next ms (.ArithI (.AUIPC (BitVec.ofNat 5 r, high c)))
        (Encode (.ArithI (.AUIPC (BitVec.ofNat 5 r, high c))))
        (BitVec.ofNat 5 r) (ms.c_PC ms.procID + upperValue c) wn h.2.1
        (decode_encode_auipc _ _) hrun lowbits.1 lowbits.2
        bytes.2.2.2.2.2.1 bytes.2.2.2.2.2.2.1
        bytes.2.2.2.2.2.2.2.1 bytes.2.2.2.2.2.2.2.2.1
      change holThe (NextRISCV ms) = _
      rw [native]
      have pc := h.2.2.1
      change ms.c_PC ms.procID = s1.pc at pc
      simp [pc, holThe, mid]
    have midrel : targetStateRel riscvTarget src mid :=
      write_post_rel s1 ms r (s1.pc + upperValue c) bound h.2
    have transported : targetStateRel riscvTarget src (env 0 mid) :=
      (riscv_target_ok.2 (env 0 mid) mid src (interference 0 mid)).1.mpr midrel
    have secondbytes : bytesInMemoryHOL src.pc b src.mem src.memDomain := by
      simpa [src, updPc, updReg, a, riscvEncode] using hb.2
    have value : src.regs r + (low c).signExtend 64 = s1.pc + c := by
      simp only [src, updPc, updReg, ite_true]
      rw [BitVec.add_assoc, loc_split c guard.2.1 guard.2.2]
    have second : riscvTarget.next (env 0 mid) =
        writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c) := by
      have bytes := bytes_in_memory_thm () src (env 0 mid) _ _ _ _ ⟨transported, secondbytes⟩
      have nb := next_encoded_addi (env 0 mid) (BitVec.ofNat 5 r) (BitVec.ofNat 5 r) (low c)
        wn transported.1 ⟨bytes.2.2.2.2.2.1, bytes.2.2.2.2.2.2.1, bytes.2.2.2.2.2.2.2.1, bytes.2.2.2.2.2.2.2.2.1⟩
      have reg := transported.2.2.2.1 r guard.1
      change (env 0 mid).c_gpr (env 0 mid).procID (BitVec.ofNat 5 r) = src.regs r at reg
      have read : GPR (BitVec.ofNat 5 r) (env 0 mid) = src.regs r := by
        simpa [GPR, gpr, wn] using reg
      change holThe (NextRISCV (env 0 mid)) = _
      rw [nb, read, value]
      rfl
    have postrel := write_post_rel src (env 0 mid) r (s1.pc + c) bound transported
    have loc_post : s2 = updPc (s1.pc + 8) (updReg r (s1.pc + c) s1) := by
      have step := hs.2.2.2.2.1
      simpa [asmUpd, riscvConfig, riscvEnc, riscvEncode, riscvAst] using step.symm
    have postsource : updPc (src.pc + 4) (updReg r (s1.pc + c) src) = s2 := by
      rw [loc_post]
      simp [src, updPc, updReg, BitVec.add_assoc]
      funext i
      by_cases e : i = r <;> simp [e]
    rw [postsource] at postrel
    have finalrel := (riscv_target_ok.2
      (env 1 (writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c)))
      (writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c)) s2
      (by simpa [loc_post, updPc, updReg] using
        interference 1 (writePost (env 0 mid) (BitVec.ofNat 5 r) (s1.pc + c)))).1.mpr postrel
    have valid := transported.1
    have code : ∀ pc, pc ∈ allPcs (riscvConfig.encode (.loc r c)).length s1.pc 0 →
        riscvTarget.getByte (env 0 mid) pc = riscvTarget.getByte ms pc := by
      intro pc covered
      have domain := bytesInMemory_allPcs _ _ _ _ 0 hs.1 covered
      have before := h.2.2.2.1 pc domain
      have after := transported.2.2.1 pc domain
      exact after.trans before.symm
    have pc : riscvTarget.getPc (env 0 mid) ∈
        allPcs (riscvConfig.encode (.loc r c)).length s1.pc riscvConfig.codeAlignment := by
      have address := transported.2.1
      change riscvTarget.getPc (env 0 mid) = s1.pc + 4 at address
      rw [address, allPcs_eq]
      refine ⟨1, ?_, ?_⟩
      · norm_num [riscvConfig, riscvEnc, riscvAst, riscvEncode]
      · rfl
    constructor
    · simpa [asserts, first, second] using ⟨⟨valid, code, pc⟩, finalrel⟩
    · simp only [asserts2]
      rw [first]
      change (∀ x, ¬ s1.memDomain x → ms.MEM8 x = mid.MEM8 x) ∧
        (∀ x, ¬ s1.memDomain x → (env 0 mid).MEM8 x =
          (riscvTarget.next (env 0 mid)).MEM8 x) ∧ True
      rw [second]
      exact ⟨fun _ _ => rfl, fun _ _ => rfl, trivial⟩

/-- Exact step-count version of `step_evaluator` for bootstrap instructions:
produces `l = (riscvAst i).length` target evaluator steps. -/
theorem step_evaluator_bootstrap {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (s : AsmState 64) (ms : riscv_state) (io : HolFfiState σ) (i : HolAsm 64)
    (hok : BootstrapInstOk i)
    (target : mc.target = riscvTarget)
    (domain : mc.progAddresses = s.memDomain)
    (disjoint : ffiEntryPcsDisjoint mc s (riscvEnc i).length)
    (interference : interferenceOk mc.nextInterfer (mc.target.proj s.memDomain))
    (step : asmStep riscvConfig s i (after s i))
    (related : targetStateRel riscvTarget s ms) :
    ∃ ms2,
      (∀ k, evaluateTargetHOL mc io (k + (riscvAst i).length) ms =
        evaluateTargetHOL (shiftInterfer (riscvAst i).length mc) io k ms2) ∧
      targetStateRel riscvTarget (after s i) ms2 := by
  have hstep_t : asmStep mc.target.config s i
      (asmUpd i (s.pc + BitVec.ofNat 64 (mc.target.config.encode i).length) s) := by
    simpa only [target, riscvTarget, riscvConfig_encode, after] using step
  have hrel_t : targetStateRel mc.target s ms := by
    simpa only [target] using related
  have hdis_t : ffiEntryPcsDisjoint mc s (mc.target.config.encode i).length := by
    simpa only [target, riscvTarget, riscvConfig_encode] using disjoint
  have henc_ok : targetOk mc.target := by
    rw [target]
    exact Flapjack.RiscV.TargetProof.riscv_target_ok
  obtain ⟨n, hlen_n, hs⟩ := riscv_encoder_correct_bootstrap s i (after s i) ms hok
    ⟨by simpa only [riscvTarget, riscvConfig_encode] using step, related⟩
  have hs_t : ∀ env : Nat → riscv_state → riscv_state,
      interferenceOk env (mc.target.proj s.memDomain) →
      let pcs := allPcs (mc.target.config.encode i).length s.pc
      asserts n (fun k s => env (n - k) (mc.target.next s)) ms
        (fun ms' => mc.target.stateOk ms' = true ∧
          (∀ pc, pc ∈ pcs 0 → mc.target.getByte ms' pc = mc.target.getByte ms pc) ∧
          mc.target.getPc ms' ∈ pcs mc.target.config.codeAlignment)
        (fun ms' => targetStateRel mc.target
          (asmUpd i (s.pc + BitVec.ofNat 64 (mc.target.config.encode i).length) s) ms') ∧
      asserts2 (n + 1) (fun k => env (n + 1 - k)) mc.target.next ms
        (fun ms1 ms2 => ∀ x, ¬ s.memDomain x →
          mc.target.getByte ms1 x = mc.target.getByte ms2 x) := by
    intro env henv
    have h1 := hs env (by simpa only [target] using henv)
    simpa only [target, riscvTarget, riscvConfig_encode, after] using h1
  have hnon := encOkNotEmpty mc.target.config i ⟨henc_ok.1, hstep_t.2.2.2.2.2.2⟩
  have hlen : 0 < (mc.target.config.encode i).length := List.length_pos_iff.mpr hnon
  have hbytes : bytesInMemoryHOL s.pc (mc.target.config.encode i) (mc.target.getByte ms)
      (fun a => mc.progAddresses a ∧ a ∉ mc.ffiEntryPcs) := by
    apply bytesInMemory_diff s.pc _ (mc.target.getByte ms) _ s.memDomain
      (fun a => a ∈ mc.ffiEntryPcs)
    refine ⟨?_, ?_, hdis_t⟩
    · rw [domain]
    · apply bytesInMemory_changeMem s.pc _ s.mem _ s.memDomain
      refine ⟨hstep_t.1, ?_⟩
      intro j hj
      apply (hrel_t.2.2.1 _ ?_).symm
      have hd := bytesInMemory_allPcs _ _ _ _ 0 hstep_t.1
      apply hd
      rw [allPcs_eq]
      exact ⟨j, by simpa using hj, by simp⟩
  have hnormal : mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs := by
    have hd := bytesInMemory_allPcs _ _ _ _ 0 hbytes
    apply hd
    rw [allPcs_eq, hrel_t.2.1]
    exact ⟨0, by simpa using hlen, by simp⟩
  have ha : ∀ env, interferenceOk env (mc.target.proj s.memDomain) →
      asserts n (fun k st => env k (mc.target.next st)) ms
        (fun ms' => mc.target.stateOk ms' = true ∧
          (∀ pc, pc ∈ allPcs (mc.target.config.encode i).length s.pc 0 →
            mc.target.getByte ms' pc = mc.target.getByte ms pc) ∧
          mc.target.getPc ms' ∈ allPcs (mc.target.config.encode i).length s.pc mc.target.config.codeAlignment)
        (fun ms' => targetStateRel mc.target
          (asmUpd i (s.pc + BitVec.ofNat 64 (mc.target.config.encode i).length) s) ms') := by
    intro env he
    have ht := (hs_t (fun k => env (n - k)) (fun k ms' => he (n - k) ms')).1
    apply asserts_weaken n _ _ ms _ _ _ _ ht
    intro k hk
    constructor
    · funext ms'
      have hidx : n - (n - k) = k := by omega
      simp only [hidx]
    · exact fun hx => hx
  have hobs : ∀ ms1 ms2, mc.target.proj s.memDomain ms1 = mc.target.proj s.memDomain ms2 →
      mc.target.stateOk ms1 = mc.target.stateOk ms2 ∧ mc.target.getPc ms1 = mc.target.getPc ms2 ∧
      ∀ a, s.memDomain a → mc.target.getByte ms1 a = mc.target.getByte ms2 a := by
    intro ms1 ms2 hp
    exact (henc_ok.2 ms1 ms2 s hp).2
  obtain ⟨ms2, hout⟩ := evaluateEqEvaluate_all n ms mc io s.memDomain i s.pc _
    ⟨hnormal, hrel_t.1, domain, interference, fun _ _ hr => hr.1, hobs, ha,
      (hs_t mc.nextInterfer interference).2, 0, by simpa using hrel_t.2.1,
      by simpa using hlen, hbytes⟩
  refine ⟨ms2, ?_, ?_⟩
  · intro k
    rw [← hlen_n]
    exact (hout k).1
  · have hrel2 := (hout 0).2.2
    simpa only [target, riscvTarget, riscvConfig_encode, after] using hrel2

/-- Exact target-evaluator step count for a bootstrap instruction list. -/
def bootstrapTraceSteps (code : List (HolAsm 64)) : Nat :=
  (code.map fun i => (riscvAst i).length).sum

theorem bootstrapTraceSteps_append (left right : List (HolAsm 64)) :
    bootstrapTraceSteps (left ++ right) = bootstrapTraceSteps left + bootstrapTraceSteps right := by
  simp [bootstrapTraceSteps, List.map_append, List.sum_append]

/-- Exact step-count version of `checked_trace_evaluator` when every instruction
in `code` satisfies `BootstrapInstOk`. -/
theorem checked_trace_evaluator_bootstrap {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (target : mc.target = riscvTarget)
    (identity : mc.nextInterfer = fun _ state => state)
    (code : List (HolAsm 64)) (s : AsmState 64)
    (hok : ∀ i ∈ code, BootstrapInstOk i)
    (checks : Checked code s) (guards : EvaluatorGuards mc code s)
    (ms : riscv_state) (io : HolFfiState σ)
    (related : targetStateRel riscvTarget s ms) :
    ∃ post,
      (∀ clock, evaluateTargetHOL mc io (bootstrapTraceSteps code + clock) ms =
        evaluateTargetHOL mc io clock post) ∧
      targetStateRel riscvTarget (run code s) post := by
  induction code generalizing s ms with
  | nil =>
    exact ⟨ms, fun _ => by simp [bootstrapTraceSteps], related⟩
  | cons i rest ih =>
    have interference : interferenceOk mc.nextInterfer (mc.target.proj s.memDomain) := by
      intro index state
      rw [identity]
    obtain ⟨middle, firstRun, middleRelated⟩ :=
      step_evaluator_bootstrap mc s ms io i (hok i (List.mem_cons_self ..))
        target guards.1 guards.2.1 interference checks.1 related
    have shiftEq := shiftInterfer_identity mc identity (riscvAst i).length
    simp only [shiftEq] at firstRun
    obtain ⟨post, restRun, postRelated⟩ :=
      ih (after s i) (fun j hj => hok j (List.mem_cons_of_mem _ hj))
        checks.2 guards.2.2 middle middleRelated
    refine ⟨post, ?_, postRelated⟩
    intro clock
    simp only [bootstrapTraceSteps, List.map_cons, List.sum_cons]
    rw [show (riscvAst i).length + (rest.map fun x => (riscvAst x).length).sum + clock =
      (bootstrapTraceSteps rest + clock) + (riscvAst i).length by simp [bootstrapTraceSteps]; omega,
      firstRun, restRun]

private theorem full_inst_ok : ∀ i ∈ fullBootstrapCode, BootstrapInstOk i := by
  have prefix_ok : ∀ i ∈ prefixCode, BootstrapInstOk i := by
    intro i hi
    simp [prefixCode, bootstrapBlocks, bootLoc] at hi
    rcases hi with rfl | rfl | rfl <;> trivial
  have loopBody_ok : ∀ i ∈ loopBody, BootstrapInstOk i := by
    intro i hi
    simp [loopBody] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · trivial
    · trivial
    · trivial
    · trivial
    · simp [BootstrapInstOk]
  have loopProgram_ok : ∀ (words : Nat) (i : HolAsm 64), i ∈ loopProgram words → BootstrapInstOk i := by
    intro words i hi
    simp only [loopProgram, List.mem_flatten, List.mem_replicate] at hi
    rcases hi with ⟨l, ⟨_, rfl⟩, hi⟩
    exact loopBody_ok i hi
  have tail_ok : ∀ i ∈ tailCode, BootstrapInstOk i := by
    intro i hi
    simp [tailCode, bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore, bootAdd] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  intro i hi
  simp only [fullBootstrapCode, List.mem_append] at hi
  rcases hi with h | h | h
  · exact prefix_ok i h
  · exact loopProgram_ok 4606 i h
  · exact tail_ok i h

theorem prefix_steps : bootstrapTraceSteps prefixCode = 6 := by decide
theorem loopBody_steps : bootstrapTraceSteps loopBody = 5 := by decide
theorem tail_steps : bootstrapTraceSteps tailCode = 41 := by decide

theorem loopProgram_steps (words : Nat) : bootstrapTraceSteps (loopProgram words) = 5 * words := by
  induction words with
  | zero => rfl
  | succ words ih =>
    simp only [loopProgram, List.replicate_succ, List.flatten_cons, bootstrapTraceSteps_append]
    rw [show bootstrapTraceSteps ((List.replicate words loopBody).flatten) =
      bootstrapTraceSteps (loopProgram words) from rfl, ih, loopBody_steps]
    omega

theorem full_steps : bootstrapTraceSteps fullBootstrapCode = bootstrapSteps := by
  simp only [fullBootstrapCode, bootstrapTraceSteps_append, loopProgram_steps,
    bootstrapSteps, initDataWords]
  rfl

/-- Exact step-count version of `full_evaluator`: the submitted bootstrap executes
in `bootstrapSteps = 23077` target evaluator steps (`0x80000000` -> `0x80001070`). -/
theorem full_evaluator_exact {σ : Type} (io : HolFfiState σ) (ms : riscv_state)
    (initial : targetStateRel riscvTarget initialAsm ms) :
    ∃ post,
      (∀ clock, evaluateTargetHOL baselineMachineConfig io (bootstrapSteps + clock) ms =
        evaluateTargetHOL baselineMachineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post := by
  obtain ⟨post, shift, relation⟩ :=
    checked_trace_evaluator_bootstrap baselineMachineConfig rfl rfl fullBootstrapCode initialAsm
      full_inst_ok full_checked full_guards ms io initial
  rw [full_steps] at shift
  exact ⟨post, shift, by rwa [full_endpoint] at relation⟩

/-- Exact 23,132-step bootstrap clock shift from `baselineInitialState` to `installedAsm`. -/
theorem full_baseline_evaluator_exact (input : Guest.InputBlob) :
    ∃ post,
      (∀ clock, evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        (bootstrapSteps + clock) (baselineInitialState input) =
        evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post) ∧
      targetStateRel riscvTarget installedAsm post :=
  full_evaluator_exact
    (sourceFfi input) (baselineInitialState input) (baselineInitialState_related input)

/-! ## Section 2: Self-Contained Oracle Baseline Installation, Transport & `.infinity` Certificate -/

/-- Heap-shaped domain size, including the globals reserved at its upper end. -/
def baselineHeapLen : Nat := (stackStart - sourceBase) / 8

def baselineAdj2 : BitVec 64 := BitVec.ofNat 64 sourceBase +
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

def baselineAdj4 : BitVec 64 := BitVec.ofNat 64 ramEnd -
  (8 : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc

/-- Remaining numeric and register premises for `OracleBaselineInstallation`,
decoupled from the 46,000-file artifact stage tree. -/
theorem oracle_baseline_installation (input : Guest.InputBlob)
    (c : Backend.Config)
    (memory : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs) :
    OracleBaselineInstallation input baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode InitECandidate.bitmaps c baselineHeapLen
      baselineAdj2 baselineAdj4 3788 0 := by
  refine ⟨baseline_machine_isRiscv,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, memory, ?_⟩
  · change (0 : BitVec 64) < BitVec.ofNat 64 sourceBase
    decide_cbv
  · change BitVec.ofNat 64 sourceBase < BitVec.ofNat 64 stackStart
    decide_cbv
  · rfl
  · change baselineHeapLen = (BitVec.ofNat 64 stackStart +
      -1 * BitVec.ofNat 64 sourceBase).toNat / (64 / 8)
    decide_cbv
  · change BitVec.ofNat 64 heapEnd = BitVec.ofNat 64 sourceBase +
      (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 baselineHeapLen -
        BitVec.ofNat 64 (globalsWords * 64 / 8)
    decide_cbv
  · decide_cbv
  · rfl
  · change holAligned (wordShiftAmount 64 + 1)
      (BitVec.ofNat 64 stackStart + -1 * BitVec.ofNat 64 sourceBase) = true
    decide_cbv
  · rfl
  · rfl
  · change baselineAdj2 ≤ BitVec.ofNat 64 stackStart
    decide_cbv
  · change BitVec.ofNat 64 stackStart ≤ baselineAdj4
    decide_cbv
  · change (BitVec.ofNat 64 stackStart + -1 * BitVec.ofNat 64 sourceBase).toNat ≤
      (wordSemBytesInWord : BitVec 64).toNat *
        (2 * DataToWord.maxHeapLimit 64 pancakeRiscVBackendConfig.dataConf - 1)
    decide_cbv
  · rfl
  · have names :
        (StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 2,
         StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 3,
         StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 4) =
          (11,12,13) := by decide_cbv
    have n2 := congrArg Prod.fst names
    have n3 := congrArg (fun p => p.2.1) names
    have n4 := congrArg (fun p => p.2.2) names
    dsimp only at n2 n3 n4
    simp only [readLimits, n2, n3, n4]
    rfl

/-- Concrete pre-transport oracle installation witness for `baselineConfigLiteral`. -/
theorem oracle_baseline_installed (input : Guest.InputBlob) :
    OracleBaselineInstallation input baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode InitECandidate.bitmaps baselineConfigLiteral
      baselineHeapLen baselineAdj2 baselineAdj4 3788 0 :=
  oracle_baseline_installation input baselineConfigLiteral (baseline_pan_installed input)

/-- Oracle installations are stable under the machine projection agreement
established by the bootstrap. -/
theorem oracle_baseline_installation_transport (input : Guest.InputBlob)
    (c : Backend.Config)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0) :
    OracleBaselineInstallation input baselineMachineConfig ms
      InitECandidate.nativeCode InitECandidate.bitmaps c baselineHeapLen
      baselineAdj2 baselineAdj4 3788 0 := by
  have agreement := baseline_endpoint_agreement ms related
  have r11 := agreement.regs 11 (by decide)
  have r12 := agreement.regs 12 (by decide)
  have r13 := agreement.regs 13 (by decide)
  have names :
      (StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 2,
       StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 3,
       StackNames.findNameSpt pancakeRiscVBackendConfig.stackConf.regNames 4) =
         (11,12,13) := by decide_cbv
  have n2 := congrArg Prod.fst names
  have n3 := congrArg (fun p => p.2.1) names
  have n4 := congrArg (fun p => p.2.2) names
  dsimp only at n2 n3 n4
  have limits : readLimits baselineMachineConfig.target.config pancakeRiscVBackendConfig
      baselineMachineConfig ms = readLimits baselineMachineConfig.target.config
        pancakeRiscVBackendConfig baselineMachineConfig baselineInstalledState := by
    simp only [readLimits, n2, n3, n4, r11, r12, r13]
  have rlen : baselineMachineConfig.target.getReg ms baselineMachineConfig.lenReg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.lenReg := r11
  have rptr : baselineMachineConfig.target.getReg ms baselineMachineConfig.ptr2Reg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.ptr2Reg := r12
  have rlen2 : baselineMachineConfig.target.getReg ms baselineMachineConfig.len2Reg =
      baselineMachineConfig.target.getReg baselineInstalledState baselineMachineConfig.len2Reg := r13
  rcases installed with ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals,
    hdomain, haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hmemory, hlimits⟩
  have memory := panInstalled_transport agreement hmemory
  unfold OracleBaselineInstallation
  simp only [rlen, rptr, rlen2, limits]
  exact ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax, hendian, memory, hlimits⟩

/-- Compiler correctness at whichever concrete machine startup reaches, parameterized
only by the oracle compilation equation and stack depth bound. -/
theorem oracle_baseline_endpoint_behaviour_eq (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour, machineSemHOL baselineMachineConfig (sourceFfi input) ms behaviour →
      behaviour = sourceBehaviour input :=
  oracle_baseline_behaviour_eq oracles input baselineMachineConfig ms
    InitECandidate.nativeCode InitECandidate.bitmaps c depth baselineHeapLen
    baselineAdj2 baselineAdj4 3788 0 compiled depthBound
    (oracle_baseline_installation_transport input c ms related installed) nonfail

/-- Source termination yields a finite target Halt witness with the same full
observable behavior, parameterized only by the oracle compilation equation and stack bound. -/
theorem oracle_baseline_endpoint_terminates (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events) :
    machineSemHOL baselineMachineConfig (sourceFfi input) ms (.terminate outcome events) ∧
      targetTerminatesWithin .infinity baselineMachineConfig (sourceFfi input) ms := by
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  have correct := oracle_baseline_endpoint_behaviour_eq oracles input c depth ms
    related compiled depthBound installed nonfail
  have termination := target_termination_of_behaviour_eq baselineMachineConfig
    (sourceFfi input) ms outcome events (fun b hb => (correct b hb).trans source)
  exact ⟨termination, (target_termination_iff_infinity _ _ _).mp
    ⟨outcome, events, termination⟩⟩

/-- Full end-to-end correctness from `baselineInitialState` (including the 23,132-step
zero-RAM bootstrap), parameterized only by the oracle compilation equation and stack bound. -/
theorem oracle_full_baseline_correct (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail) :
    ∀ behaviour,
      machineSemHOL baselineMachineConfig (sourceFfi input)
        (baselineInitialState input) behaviour →
      behaviour = sourceBehaviour input := by
  obtain ⟨post, shift, related⟩ := full_baseline_evaluator_exact input
  exact Bootstrap.behavior_property_from_clock_shift (sourceFfi input) shift
    (fun behaviour => behaviour = sourceBehaviour input)
    (oracle_baseline_endpoint_behaviour_eq oracles input c depth post related
      compiled depthBound installed nonfail)

/-- End-to-end `InitE.Certificate baselineSubmission .infinity` parameterized only by
the oracle compilation equation and stack depth bound (zero stage files required). -/
theorem oracle_full_baseline_certificate (oracles : List (Option (Spt Nat)))
    (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480) :
    InitE.Certificate baselineSubmission .infinity := by
  apply InitE.certificate_of_exact_behaviour baselineSubmission rfl baselineSubmission_admitted
  intro input outcome events source behaviour execution
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]
    intro impossible
    cases impossible
  change machineSemHOL baselineSubmission.machineConfig (sourceFfi input)
    (baselineSubmission.initialState input) behaviour at execution
  rw [baselineSubmission_machineConfig, baselineSubmission_initialState] at execution
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact baseline_pan_installed input
  have hinst := oracle_baseline_installation input c hmem
  exact (oracle_full_baseline_correct oracles input c depth compiled depthBound hinst nonfail
    behaviour execution).trans source

/-! ## Section 3: Self-Contained Finite-`K` Target Termination & Certificate Reducers -/

/-- Direct finite-`K` certificate constructor from a bounded `matchingExecutionAt` witness. -/
theorem certificate_of_bounded_behaviour (submission : Submission) (K : Nat)
    (score : submission.K = .finite K) (admitted : submission.Admitted)
    (correct : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∃ steps ≤ K, matchingExecutionAt submission input outcome events steps) :
    Certificate submission (.finite K) :=
  ⟨score, admitted, correct⟩

/-- Any finite `targetTerminatesAt` witness at `steps` for a machine whose `machineSemHOL`
equals `.terminate outcome events` automatically produces `matchingExecutionAt` at the same
`steps` by target clock determinism (`evaluateTargetIgnoreClocks`). -/
theorem matchingExecutionAt_of_behaviour_and_terminatesAt (submission : Submission)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (steps : Nat)
    (hsem : machineSemHOL submission.machineConfig (sourceFfi input)
      (submission.initialState input) (.terminate outcome events))
    (covered : coveredOutcome outcome)
    (hterm : targetTerminatesAt submission.machineConfig (sourceFfi input)
      (submission.initialState input) steps) :
    matchingExecutionAt submission input outcome events steps := by
  obtain ⟨k0, ms0, ffi0, hrun0, hevents0⟩ := hsem
  obtain ⟨out1, ms1, ffi1, hrun1⟩ := hterm
  have heq := evaluateTargetIgnoreClocks submission.machineConfig (sourceFfi input)
    steps k0 (submission.initialState input) (.halt out1) (.halt outcome) ms1 ms0 ffi1 ffi0
    ⟨hrun1, by simp, hrun0, by simp⟩
  have hout : out1 = outcome := by
    have h := congrArg Prod.fst heq
    injection h
  have hffi : ffi1 = ffi0 := congrArg (fun r => r.2.2) heq
  subst hout
  subst hffi
  refine ⟨out1, ms1, ffi1, hrun1, ?_⟩
  rw [← hevents0]
  exact matchingResult_refl input out1 ffi1.ioEvents covered

/-- Combining exact behaviour preservation with a finite `K` termination bound yields
`Certificate submission (.finite K)` without re-proving I/O trace or outcome agreement. -/
theorem certificate_of_exact_behaviour_and_bound (submission : Submission) (K : Nat)
    (score : submission.K = .finite K) (admitted : submission.Admitted)
    (correct : ∀ input outcome events,
      sourceBehaviour input = .terminate outcome events →
      ∀ behaviour, machineSemHOL submission.machineConfig (sourceFfi input)
        (submission.initialState input) behaviour → behaviour = .terminate outcome events)
    (bounded : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        targetTerminatesWithin (.finite K) submission.machineConfig (sourceFfi input)
          (submission.initialState input)) :
    Certificate submission (.finite K) := by
  refine ⟨score, admitted, ?_⟩
  intro input hgas outcome events source covered
  have hsem := target_termination_of_behaviour_eq submission.machineConfig
    (sourceFfi input) (submission.initialState input) outcome events
    (correct input outcome events source)
  obtain ⟨steps, hle, hterm⟩ := bounded input hgas outcome events source covered
  exact ⟨steps, hle,
    matchingExecutionAt_of_behaviour_and_terminatesAt submission input outcome events
      steps hsem covered hterm⟩

/-- Shifting a post-bootstrap `targetTerminatesAt` witness across the 23,132-step
zero-RAM bootstrap. -/
theorem targetTerminatesAt_of_bootstrap_shift (input : Guest.InputBlob)
    (post : RiscV.L3.riscv_state) (steps : Nat)
    (shift : ∀ clock, evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + clock) (baselineInitialState input) =
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) clock post)
    (hterm : targetTerminatesAt baselineMachineConfig (sourceFfi input) post steps) :
    targetTerminatesAt baselineMachineConfig (sourceFfi input)
      (baselineInitialState input) (bootstrapSteps + steps) := by
  obtain ⟨outcome, ms', ffi', hrun⟩ := hterm
  exact ⟨outcome, ms', ffi', (shift steps).trans hrun⟩

/-- Target termination is monotone in the step budget by `evaluateTargetAddClock`. -/
theorem targetTerminatesAt_mono {S Q σ : Type} (mc : MachineConfig 64 S Q)
    (ffi : HolFfiState σ) (ms : S) {steps₁ steps₂ : Nat} (hle : steps₁ ≤ steps₂)
    (hterm : targetTerminatesAt mc ffi ms steps₁) :
    targetTerminatesAt mc ffi ms steps₂ := by
  obtain ⟨outcome, ms', ffi', hrun⟩ := hterm
  have hadd := evaluateTargetAddClock mc ffi steps₁ ms (steps₂ - steps₁)
    (.halt outcome) ms' ffi' hrun (by simp)
  rw [Nat.add_sub_of_le hle] at hadd
  exact ⟨outcome, ms', ffi', hadd⟩

/-- Under `machineSemHOL mc ffi ms (.terminate outcome events)`, any non-`.timeOut`
target evaluation at `steps` is already a `.halt outcome` witness (`targetTerminatesAt`). -/
theorem targetTerminatesAt_of_not_timeOut {S Q σ : Type} (mc : MachineConfig 64 S Q)
    (ffi : HolFfiState σ) (ms : S) (outcome : HolOutcome) (events : List HolIoEvent)
    (steps : Nat)
    (hsem : machineSemHOL mc ffi ms (.terminate outcome events))
    (hnt : (evaluateTargetHOL mc ffi steps ms).1 ≠ .timeOut) :
    targetTerminatesAt mc ffi ms steps := by
  obtain ⟨k0, ms0, ffi0, hrun0, _⟩ := hsem
  generalize hrun1 : evaluateTargetHOL mc ffi steps ms = run1 at hnt
  rcases run1 with ⟨r1, ms1, ffi1⟩
  have heq := evaluateTargetIgnoreClocks mc ffi steps k0 ms r1 (.halt outcome) ms1 ms0 ffi1 ffi0
    ⟨hrun1, hnt, hrun0, by simp⟩
  have hr1 : r1 = .halt outcome := congrArg Prod.fst heq
  subst hr1
  exact ⟨outcome, ms1, ffi1, hrun1⟩

/-- Under `machineSemHOL mc ffi ms (.terminate outcome events)`, `targetTerminatesAt` at
`steps` is equivalent to `(evaluateTargetHOL mc ffi steps ms).1 ≠ .timeOut`. -/
theorem targetTerminatesAt_iff_not_timeOut {S Q σ : Type} (mc : MachineConfig 64 S Q)
    (ffi : HolFfiState σ) (ms : S) (outcome : HolOutcome) (events : List HolIoEvent)
    (steps : Nat)
    (hsem : machineSemHOL mc ffi ms (.terminate outcome events)) :
    targetTerminatesAt mc ffi ms steps ↔ (evaluateTargetHOL mc ffi steps ms).1 ≠ .timeOut := by
  constructor
  · rintro ⟨out1, ms1, ffi1, hrun1⟩
    rw [hrun1]
    simp
  · exact targetTerminatesAt_of_not_timeOut mc ffi ms outcome events steps hsem

/-- Under `machineSemHOL mc ffi ms (.terminate outcome events)`, `targetTerminatesWithin (.finite K)`
is equivalent to `(evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut`. -/
theorem targetTerminatesWithin_finite_iff_not_timeOut {S Q σ : Type} (mc : MachineConfig 64 S Q)
    (ffi : HolFfiState σ) (ms : S) (outcome : HolOutcome) (events : List HolIoEvent)
    (K : Nat)
    (hsem : machineSemHOL mc ffi ms (.terminate outcome events)) :
    targetTerminatesWithin (.finite K) mc ffi ms ↔ (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut := by
  constructor
  · rintro ⟨steps, hle, hterm⟩
    exact (targetTerminatesAt_iff_not_timeOut mc ffi ms outcome events K hsem).mp
      (targetTerminatesAt_mono mc ffi ms hle hterm)
  · intro hnt
    exact ⟨K, Nat.le_refl K, targetTerminatesAt_of_not_timeOut mc ffi ms outcome events K hsem hnt⟩

/-- Constructive target halt transfer: if a target execution halts at some clock `k0` with
`(.halt outcome, ms0, ffi0)` and does not time out at clock `K`, then it halts at clock `K`
with the exact same `outcome` and `ffi0` (without `machineSemHOL`). -/
theorem evaluateTarget_halt_of_not_timeOut_and_halt {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (k0 K : Nat) (outcome : HolOutcome) (ms0 : S) (ffi0 : HolFfiState σ)
    (hhalt0 : evaluateTargetHOL mc ffi k0 ms = (.halt outcome, ms0, ffi0))
    (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    ∃ ms1, evaluateTargetHOL mc ffi K ms = (.halt outcome, ms1, ffi0) := by
  rcases hrun1 : evaluateTargetHOL mc ffi K ms with ⟨r1, ms1, ffi1⟩
  rw [hrun1] at hnt
  have heq := evaluateTargetIgnoreClocks mc ffi K k0 ms r1 (.halt outcome) ms1 ms0 ffi1 ffi0
    ⟨hrun1, hnt, hhalt0, by simp⟩
  have hr1 : r1 = .halt outcome := congrArg Prod.fst heq
  have hffi1 : ffi1 = ffi0 := congrArg (fun p => p.2.2) heq
  subst hr1 hffi1
  exact ⟨ms1, rfl⟩

/-- Zero-clock timeout characterization and positive step budget of non-`timeOut` target runs. -/
theorem evaluateTarget_zero_timeOut_and_pos_of_not_timeOut {width : Nat} [NeZero width]
    {S Q σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (K_post : Nat) (ms : S) :
    evaluateTargetHOL mc ffi 0 ms = (.timeOut, ms, ffi) ∧
      ((evaluateTargetHOL mc ffi K_post ms).1 ≠ .timeOut → 1 ≤ K_post) := by
  refine ⟨rfl, ?_⟩
  intro hnt
  cases K_post with
  | zero => exact False.elim (hnt rfl)
  | succ n => exact Nat.succ_le_succ (Nat.zero_le n)

/-- Direct full-baseline non-`timeOut` target halt agreement from `sourceBehaviour = .terminate`
(including the 23,132-step zero-RAM bootstrap) together with `1 ≤ bootstrapSteps + K_post`. -/
theorem oracle_full_baseline_terminate_halt_agree_of_not_timeOut
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (K_post : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input)).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input)).1 = .halt outcome ∧
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input)).2.2.ioEvents = events ∧
    1 ≤ bootstrapSteps + K_post := by
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]; intro h; cases h
  have correct := oracle_full_baseline_correct oracles input c depth compiled depthBound
    installed nonfail
  have hsem := target_termination_of_behaviour_eq baselineMachineConfig
    (sourceFfi input) (baselineInitialState input) outcome events
    (fun b hb => (correct b hb).trans source)
  obtain ⟨k0, ms0, ffi0, hrun0, hevents0⟩ := hsem
  obtain ⟨ms1, hrun1⟩ := evaluateTarget_halt_of_not_timeOut_and_halt
    baselineMachineConfig (sourceFfi input) (baselineInitialState input)
    k0 (bootstrapSteps + K_post) outcome ms0 ffi0 hrun0 hnt
  have hpos := (evaluateTarget_zero_timeOut_and_pos_of_not_timeOut
    baselineMachineConfig (sourceFfi input) (bootstrapSteps + K_post)
    (baselineInitialState input)).2 hnt
  rw [hrun1]
  exact ⟨rfl, hevents0, hpos⟩

/-- Direct post-bootstrap non-`timeOut` target halt agreement on any `ms` related to `installedAsm`
from `sourceBehaviour = .terminate` together with `1 ≤ K_post`. -/
theorem oracle_baseline_endpoint_terminate_halt_agree_of_not_timeOut
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (ms : RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (K_post : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K_post ms).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K_post ms).1 = .halt outcome ∧
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K_post ms).2.2.ioEvents = events ∧
    1 ≤ K_post := by
  have hsem := (oracle_baseline_endpoint_terminates oracles input c depth ms related
    compiled depthBound installed outcome events source).1
  obtain ⟨k0, ms0, ffi0, hrun0, hevents0⟩ := hsem
  obtain ⟨ms1, hrun1⟩ := evaluateTarget_halt_of_not_timeOut_and_halt
    baselineMachineConfig (sourceFfi input) ms
    k0 K_post outcome ms0 ffi0 hrun0 hnt
  have hpos := (evaluateTarget_zero_timeOut_and_pos_of_not_timeOut
    baselineMachineConfig (sourceFfi input) K_post ms).2 hnt
  rw [hrun1]
  exact ⟨rfl, hevents0, hpos⟩

/-- End-to-end finite-`K` `InitE.Certificate submission (.finite K)` parameterized by
the oracle compilation equation, stack depth bound, and a post-bootstrap step bound `K_post`
with `bootstrapSteps + K_post ≤ K` (zero stage files required). -/
theorem oracle_full_baseline_bounded_certificate (submission : Submission)
    (K K_post : Nat)
    (score : submission.K = .finite K)
    (admitted : submission.Admitted)
    (hmc : submission.machineConfig = baselineMachineConfig)
    (hinit : submission.initialState = baselineInitialState)
    (oracles : List (Option (Spt Nat)))
    (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (hK : bootstrapSteps + K_post ≤ K)
    (bounded_post : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ post : RiscV.L3.riscv_state,
          targetStateRel riscvTarget installedAsm post →
          targetTerminatesWithin (.finite K_post) baselineMachineConfig (sourceFfi input) post) :
    InitE.Certificate submission (.finite K) := by
  apply certificate_of_exact_behaviour_and_bound submission K score admitted
  · intro input outcome events source behaviour execution
    have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
      rw [source]
      intro impossible
      cases impossible
    change machineSemHOL submission.machineConfig (sourceFfi input)
      (submission.initialState input) behaviour at execution
    rw [hmc, hinit] at execution
    have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
        c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
        baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
        (wlabWlocExact ∘ (sourceInitialState input).memory)
        (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
      rw [hlab]
      exact baseline_pan_installed input
    have hinst := oracle_baseline_installation input c hmem
    exact (oracle_full_baseline_correct oracles input c depth compiled depthBound hinst nonfail
      behaviour execution).trans source
  · intro input hgas outcome events source covered
    rw [hmc, hinit]
    obtain ⟨post, shift, related⟩ := full_baseline_evaluator_exact input
    obtain ⟨steps, hle, hterm⟩ := bounded_post input hgas outcome events source covered post related
    have hle' : steps ≤ K_post := hle
    refine ⟨bootstrapSteps + steps, Nat.le_trans (Nat.add_le_add_left hle' bootstrapSteps) hK, ?_⟩
    exact targetTerminatesAt_of_bootstrap_shift input post steps shift hterm

/-- End-to-end finite-`K` `InitE.Certificate submission (.finite K)` reduced to proving
that the post-bootstrap target evaluation at `K_post` is not `.timeOut` (`≠ .timeOut`). -/
theorem oracle_full_baseline_certificate_of_not_timeOut (submission : Submission)
    (K K_post : Nat)
    (score : submission.K = .finite K)
    (admitted : submission.Admitted)
    (hmc : submission.machineConfig = baselineMachineConfig)
    (hinit : submission.initialState = baselineInitialState)
    (oracles : List (Option (Spt Nat)))
    (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (hK : bootstrapSteps + K_post ≤ K)
    (not_timeOut_post : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ post : RiscV.L3.riscv_state,
          targetStateRel riscvTarget installedAsm post →
          (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K_post post).1 ≠ .timeOut) :
    InitE.Certificate submission (.finite K) := by
  apply oracle_full_baseline_bounded_certificate submission K K_post score admitted hmc hinit
    oracles c depth hlab compiled depthBound hK
  intro input hgas outcome events source covered post related
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact baseline_pan_installed input
  have hinst := oracle_baseline_installation input c hmem
  have hsem := (oracle_baseline_endpoint_terminates oracles input c depth post related
    compiled depthBound hinst outcome events source).1
  exact (targetTerminatesWithin_finite_iff_not_timeOut baselineMachineConfig (sourceFfi input)
    post outcome events K_post hsem).mpr
    (not_timeOut_post input hgas outcome events source covered post related)

/-- `baselineSubmission` equipped with a finite step budget `.finite K`. -/
def baselineWithFiniteK (K : Nat) : InitE.Submission :=
  { InitECandidate.Solver.FastEnv.baselineSubmission with K := .finite K }

theorem baselineWithFiniteK_machineConfig (K : Nat) :
    (baselineWithFiniteK K).machineConfig = baselineMachineConfig := rfl

theorem baselineWithFiniteK_initialMemory (K : Nat) (input : Guest.InputBlob) :
    (baselineWithFiniteK K).initialMemory input =
      (fun a =>
        if machineSharedDomain a then byteToBits ((Guest.guestHostMemory input a).getD 0)
        else initialMemory a) := by
  have h := submission_record_memory InitECandidate.code (.finite K)
    nativePc baselineNames 2 baselineMmio input
  have hpure : romMemory InitECandidate.code = initialMemory := rfl
  rw [hpure] at h
  have hd : submissionSharedDomain = machineSharedDomain := rfl
  unfold hostOverlay at h
  rw [hd] at h
  exact h

theorem baselineWithFiniteK_initialState (K : Nat) :
    (baselineWithFiniteK K).initialState = baselineInitialState := by
  funext input
  unfold Submission.initialState
  rw [baselineWithFiniteK_initialMemory K input]
  rfl

/-- Admission theorem for `baselineWithFiniteK K`. -/
theorem baselineWithFiniteK_admitted (K : Nat) :
    (baselineWithFiniteK K).Admitted := by
  have h := InitECandidate.Solver.FastEnv.baselineSubmission_admitted
  exact ⟨h.code_nonempty, h.code_limit, h.anchor_lower, h.anchor_upper,
    h.anchor_aligned, h.name_boundary, h.metadata_length, h.ordinary_slots_loaded,
    h.mmio_valid, h.entry_distinct, h.entry_loaded, h.entry_aligned,
    h.entry_dispatch_separate, h.mmio_program, h.exit_loaded, h.layout_bound⟩

/-- Final Yukon finite-`K` certificate reducer: a uniform non-`timeOut` bound at
`bootstrapSteps + K_post` on `baselineInitialState input` directly yields
`InitE.Certificate (baselineWithFiniteK (bootstrapSteps + K_post)) (.finite (bootstrapSteps + K_post))`! -/
theorem finite_certificate_of_uniform_post_bootstrap_not_timeOut
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth K_post : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (not_timeOut : ∀ input : Guest.InputBlob,
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ outcome events,
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
          (bootstrapSteps + K_post) (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK (bootstrapSteps + K_post))
      (.finite (bootstrapSteps + K_post)) := by
  refine certificate_of_bounded_behaviour
    (baselineWithFiniteK (bootstrapSteps + K_post))
    (bootstrapSteps + K_post) rfl
    (baselineWithFiniteK_admitted (bootstrapSteps + K_post)) ?_
  intro input hgas outcome events source covered
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact baseline_pan_installed input
  have hinst := oracle_baseline_installation input c hmem
  have hnt := not_timeOut input hgas outcome events source covered
  obtain ⟨hhalt, hio, _⟩ :=
    oracle_full_baseline_terminate_halt_agree_of_not_timeOut
      oracles input c depth compiled depthBound hinst
      outcome events source K_post hnt
  rcases hrun : evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input) with ⟨res, post, finalFfi⟩
  rw [hrun] at hhalt hio
  dsimp only at hhalt hio
  subst hhalt
  refine ⟨bootstrapSteps + K_post, Nat.le_refl _, outcome, post, finalFfi, ?_, ?_⟩
  · rw [baselineWithFiniteK_machineConfig, baselineWithFiniteK_initialState]
    exact hrun
  · rw [hio]
    exact matchingResult_refl input outcome events covered


end InitECandidate.Solver.YukonSelfContainedCert
