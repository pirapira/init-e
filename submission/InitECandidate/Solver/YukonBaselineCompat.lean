import InitECandidate.Solver.FastBaselineEnv
import InitECandidate.Proofs.CompilerOracles

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace



/-! Yukon compatibility copies: all new exact-clock proofs live in Solver.
The imported module paths already exist in the pinned initial submission.
No post-baseline Proofs declaration is used as a proof of an exact-clock fact. -/
set_option maxRecDepth 10000
set_option maxHeartbeats 0
set_option autoImplicit false
namespace InitECandidate.Solver.YukonBaselineCompat
open InitE
open Flapjack.Misc
open Flapjack Flapjack.RiscV.L3 Flapjack.RiscV.L3.Step
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapAsmComposition
open InitECandidate.Solver.FastEnv.BootstrapStraightLine InitECandidate.Solver.FastEnv.BootstrapTrace
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.BackendProof Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Pancake.Proofs.PanToTarget

/-- Explicit allocation tape avoids importing the generated WordBackend stage tree. -/
def baselineCompilerConfig (oracles : List (Option (Spt Nat))) : Backend.Config :=
  InitE.oracleCompilerConfig oracles

def baselineConfigLiteralWithOracles (oracles : List (Option (Spt Nat))) : Backend.Config :=
  { InitE.baselineConfigLiteral with wordToWordConf := (baselineCompilerConfig oracles).wordToWordConf }

def baselineConfig (oracles : List (Option (Spt Nat))) : Backend.Config :=
  baselineConfigLiteralWithOracles oracles

def baselineNames : List HolFfiName := baselineLabConfig.ffiNames.getD []

def baselineMmio : List ShmemInfoNum := baselineLabConfig.shmemExtra

def dispatchAddress (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((1+i)*ffiOffset)

def baselineEntryPcs : List (BitVec 64) :=
  ((List.range 2).map fun i => BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((3+i)*ffiOffset)) ++
    (baselineMmio.map fun rec => BitVec.ofNat 64 nativePc + BitVec.ofNat 64 rec.entryPc)

theorem baseline_finite_facts :
    ffiNameBoundaryValid baselineNames 2 ∧
    (∀ i : Fin baselineNames.length, 2 ≤ i.val →
      mmioRecordValid (BitVec.ofNat 64 nativePc) 2 baselineMmio i.val = true) ∧
    (∀ i : Fin 2, findIndex
      (BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((3+i.val)*ffiOffset))
      baselineEntryPcs 0 = some i.val) ∧
    (∀ i : Fin baselineEntryPcs.length, 2 ≤ i.val →
      dispatchAddress 0 ≠ baselineEntryPcs[i] ∧ dispatchAddress 1 ≠ baselineEntryPcs[i]) ∧
    baselineNames.length = baselineEntryPcs.length := by
  have h := InitECandidate.Solver.FastEnv.baseline_finite_facts
  unfold InitECandidate.Solver.FastEnv.baselineEntryPcs InitECandidate.Solver.FastEnv.dispatchAddress at h
  unfold InitECandidate.Solver.FastEnv.baselineNames InitECandidate.Solver.FastEnv.baselineMmio at h
  unfold baselineEntryPcs dispatchAddress baselineNames baselineMmio
  exact h

theorem baseline_config_literal_compat (oracles : List (Option (Spt Nat))) :
    (baselineConfig oracles).wordToWordConf = (InitE.oracleCompilerConfig oracles).wordToWordConf := rfl

theorem baseline_config_lab_compat (oracles : List (Option (Spt Nat))) :
    (baselineConfig oracles).labConf = baselineLabConfig := rfl

theorem baseline_pan_installed (input : Guest.InputBlob) :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineLabConfig.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineLabConfig.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs :=
  InitECandidate.Solver.FastEnv.baseline_pan_installed input

/-- Exact witness count for every instruction in the bootstrap instruction subset. -/
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

theorem prefix_inst_ok : ∀ i ∈ prefixCode, BootstrapInstOk i := by
  intro i hi
  simp [prefixCode, bootstrapBlocks, bootLoc] at hi
  rcases hi with rfl | rfl | rfl <;> trivial

theorem loopBody_inst_ok : ∀ i ∈ loopBody, BootstrapInstOk i := by
  intro i hi
  simp [loopBody] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · trivial
  · trivial
  · simp [BootstrapInstOk]

theorem loopProgram_inst_ok (words : Nat) : ∀ i ∈ loopProgram words, BootstrapInstOk i := by
  intro i hi
  simp only [loopProgram, List.mem_flatten, List.mem_replicate] at hi
  rcases hi with ⟨l, ⟨_, rfl⟩, hi⟩
  exact loopBody_inst_ok i hi

theorem tail_inst_ok : ∀ i ∈ tailCode, BootstrapInstOk i := by
  intro i hi
  simp [tailCode, bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore, bootAdd] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem full_inst_ok : ∀ i ∈ fullBootstrapCode, BootstrapInstOk i := by
  intro i hi
  simp only [fullBootstrapCode, List.mem_append] at hi
  rcases hi with h | h | h
  · exact prefix_inst_ok i h
  · exact loopProgram_inst_ok 4606 i h
  · exact tail_inst_ok i h

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
  simp only [fullBootstrapCode, bootstrapTraceSteps_append, prefix_steps, loopProgram_steps, tail_steps,
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


end InitECandidate.Solver.YukonBaselineCompat
