import InitE.Challenge
import InitE.SubmissionAdmission
import Flapjack.RiscV.CorrectnessEncoding.Jump.Native


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.FastHalt

open Classical
open InitE
open Flapjack
open Flapjack.RiscV.L3
open Flapjack.RiscV.L3.Step
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.RiscV.TargetProof.Jump

private structure OrdinaryStep (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : riscv_state) : Prop where
  program : mc.progAddresses (mc.target.getPc before)
  nonFfi : mc.target.getPc before ∉ mc.ffiEntryPcs
  encoded : encodedBytesInMemHOL mc.target.config (mc.target.getPc before)
    (mc.target.getByte before) mc.progAddresses
  beforeOk : mc.target.stateOk before = true
  afterOk : mc.target.stateOk (mc.target.next before) = true
  outside : ∀ address, ¬ mc.progAddresses address →
    mc.target.getByte (mc.target.next before) address = mc.target.getByte before address

private theorem ordinary_step_evaluate
    {mc : MachineConfig 64 riscv_state RiscVProjection}
    (identity : mc.nextInterfer = fun _ state => state)
    {σ : Type} (ffi : HolFfiState σ) (clock : Nat)
    {before : riscv_state} (step : OrdinaryStep mc before) :
    evaluateTargetHOL mc ffi (clock + 1) before =
      evaluateTargetHOL mc ffi clock (mc.target.next before) := by
  have hshift : holShiftSeq 1 mc.nextInterfer = mc.nextInterfer := by rw [identity]; rfl
  have hnext : mc.nextInterfer 0 (mc.target.next before) = mc.target.next before := by
    rw [identity]
  have hprogram : mc.progAddresses (mc.target.getPc before) ∧
      mc.target.getPc before ∉ mc.ffiEntryPcs := ⟨step.program, step.nonFfi⟩
  have hok : mc.target.stateOk before = true ∧
      mc.target.stateOk (mc.target.next before) = true ∧
      mc.target.stateOk (mc.target.next before) = true ∧
      (∀ x, ¬ mc.progAddresses x →
        mc.target.getByte (mc.target.next before) x = mc.target.getByte before x) :=
    ⟨step.beforeOk, step.afterOk, step.afterOk, step.outside⟩
  simp only [evaluateTargetHOL, if_pos hprogram,
    if_pos step.encoded, applyOracleHOL, hshift, hnext]
  simp only [if_pos hok]

/-- The 4-byte RISC-V encoding of `jal x0, 20` (`HolAsm.jump 20#64`), followed by
36 zero padding bytes so that `anchorPc = 0x80000024` lies strictly inside the image. -/
def minHaltingCode : List (BitVec 8) :=
  [0x6f#8, 0x00#8, 0x40#8, 0x01#8] ++ List.replicate 36 0#8

/-- Minimum 40-byte `Submission` that jumps directly from `initialPc = 0x80000000`
to `haltPc = 0x80000014` (`anchorPc - 16`) on step 1 and halts with `.success` on step 2. -/
def minHaltingSubmission (K : NatE) : Submission where
  code := minHaltingCode
  K := K
  anchorPc := 0x80000024
  names := []
  first := 0
  extra := []

private theorem minHalting_ffiEntryPcs (K : NatE) :
    (minHaltingSubmission K).machineConfig.ffiEntryPcs = [] := rfl

private theorem minHalting_ffiEntryPcs_raw (K : NatE) :
    (Submission.machineConfig ⟨minHaltingCode, K, 0x80000024, [], 0, []⟩).ffiEntryPcs = [] := rfl

/-- 1. Admission proof for `minHaltingSubmission K`. -/
theorem minHaltingSubmission_admitted (K : NatE) :
    (minHaltingSubmission K).Admitted := by
  refine Submission.admitted_literal minHaltingCode K 0x80000024 [] 0 []
    (by decide) (by decide) (by decide) (by decide) (by decide)
    ⟨by decide, fun i => Fin.elim0 i⟩ rfl (by decide) (fun i => Fin.elim0 i)
    ?_ ?_ ?_ ?_ ?_ ?_ (by decide)
  · rw [minHalting_ffiEntryPcs_raw K]
    exact List.Pairwise.nil
  · intro a ha
    rw [minHalting_ffiEntryPcs_raw K] at ha
    cases ha
  · intro a ha
    rw [minHalting_ffiEntryPcs_raw K] at ha
    cases ha
  · intro a ha
    rw [minHalting_ffiEntryPcs_raw K] at ha
    cases ha
  · intro rec hrec
    cases hrec
  · intro rec hrec
    cases hrec

private theorem minHalting_initialMemory_byte (K : NatE) (input : Guest.InputBlob)
    (a : BitVec 64) (hnotShared : ¬ submissionSharedDomain a) :
    ((minHaltingSubmission K).initialState input).MEM8 a =
      if initialPc ≤ a.toNat ∧ a.toNat < initialPc + minHaltingCode.length then
        minHaltingCode[a.toNat - initialPc]?.getD 0
      else 0 := by
  change (if submissionSharedDomain a then _ else _) = _
  exact if_neg hnotShared

private theorem minHalting_anchor_sub_0 (K : NatE) :
    BitVec.ofNat 64 (minHaltingSubmission K).anchorPc - BitVec.ofNat 64 (ffiOffset * (0 + 1)) =
      0x80000014#64 := by
  change 0x80000024#64 - 16#64 = 0x80000014#64
  decide

private theorem minHalting_anchor_sub_1 (K : NatE) :
    BitVec.ofNat 64 (minHaltingSubmission K).anchorPc - BitVec.ofNat 64 (ffiOffset * (1 + 1)) =
      0x80000004#64 := by
  change 0x80000024#64 - 32#64 = 0x80000004#64
  decide

private theorem minHalting_programDomain_of_ne (K : NatE) (a : BitVec 64)
    (hmem : submissionMemoryDomain a)
    (h0 : a ≠ 0x80000014#64) (h1 : a ≠ 0x80000004#64) :
    (minHaltingSubmission K).programDomain a := by
  refine ⟨hmem, ?_⟩
  intro i hi
  change i < 2 at hi
  have hi2 : i = 0 ∨ i = 1 := by omega
  rcases hi2 with rfl | rfl
  · rw [minHalting_anchor_sub_0 K]
    exact h0
  · rw [minHalting_anchor_sub_1 K]
    exact h1

private theorem minHalting_haltPc_not_program (K : NatE) :
    ¬ (minHaltingSubmission K).programDomain 0x80000014#64 := by
  intro h
  have h2 : (0 : Nat) < (minHaltingSubmission K).first + 2 := by
    change (0 : Nat) < 2
    decide
  exact h.2 0 h2 (minHalting_anchor_sub_0 K).symm

private theorem minHalting_byte0 (K : NatE) (input : Guest.InputBlob) :
    ((minHaltingSubmission K).initialState input).MEM8 0x80000000#64 = 0x6f#8 := by
  rw [minHalting_initialMemory_byte K input 0x80000000#64 (by unfold submissionSharedDomain; decide)]
  decide

private theorem minHalting_byte1 (K : NatE) (input : Guest.InputBlob) :
    ((minHaltingSubmission K).initialState input).MEM8 0x80000001#64 = 0x00#8 := by
  rw [minHalting_initialMemory_byte K input 0x80000001#64 (by unfold submissionSharedDomain; decide)]
  decide

private theorem minHalting_byte2 (K : NatE) (input : Guest.InputBlob) :
    ((minHaltingSubmission K).initialState input).MEM8 0x80000002#64 = 0x40#8 := by
  rw [minHalting_initialMemory_byte K input 0x80000002#64 (by unfold submissionSharedDomain; decide)]
  decide

private theorem minHalting_byte3 (K : NatE) (input : Guest.InputBlob) :
    ((minHaltingSubmission K).initialState input).MEM8 0x80000003#64 = 0x01#8 := by
  rw [minHalting_initialMemory_byte K input 0x80000003#64 (by unfold submissionSharedDomain; decide)]
  decide

private theorem minHalting_dom0 (K : NatE) :
    (minHaltingSubmission K).programDomain 0x80000000#64 :=
  minHalting_programDomain_of_ne K 0x80000000#64
    (by unfold submissionMemoryDomain submissionSharedDomain; decide) (by decide) (by decide)

private theorem minHalting_dom1 (K : NatE) :
    (minHaltingSubmission K).programDomain 0x80000001#64 :=
  minHalting_programDomain_of_ne K 0x80000001#64
    (by unfold submissionMemoryDomain submissionSharedDomain; decide) (by decide) (by decide)

private theorem minHalting_dom2 (K : NatE) :
    (minHaltingSubmission K).programDomain 0x80000002#64 :=
  minHalting_programDomain_of_ne K 0x80000002#64
    (by unfold submissionMemoryDomain submissionSharedDomain; decide) (by decide) (by decide)

private theorem minHalting_dom3 (K : NatE) :
    (minHaltingSubmission K).programDomain 0x80000003#64 :=
  minHalting_programDomain_of_ne K 0x80000003#64
    (by unfold submissionMemoryDomain submissionSharedDomain; decide) (by decide) (by decide)

private theorem minHalting_encodedBytes (K : NatE) (input : Guest.InputBlob) :
    encodedBytesInMemHOL (minHaltingSubmission K).machineConfig.target.config
      ((minHaltingSubmission K).machineConfig.target.getPc ((minHaltingSubmission K).initialState input))
      ((minHaltingSubmission K).machineConfig.target.getByte ((minHaltingSubmission K).initialState input))
      (minHaltingSubmission K).machineConfig.progAddresses := by
  have hlen : 0 * 2 ^ riscvTarget.config.codeAlignment <
      (riscvTarget.config.encode (HolAsm.jump 20#64)).length := by decide
  refine ⟨.jump 20#64, 0, hlen, ?_⟩
  have henc : (riscvTarget.config.encode (.jump 20#64)).drop
      (0 * 2 ^ riscvTarget.config.codeAlignment) =
      [0x6f#8, 0x00#8, 0x40#8, 0x01#8] := by decide
  change bytesInMemoryHOL 0x80000000#64
    ((riscvTarget.config.encode (.jump 20#64)).drop (0 * 2 ^ riscvTarget.config.codeAlignment))
    ((minHaltingSubmission K).initialState input).MEM8 (minHaltingSubmission K).programDomain
  rw [henc]
  exact ⟨minHalting_byte0 K input, minHalting_dom0 K,
    minHalting_byte1 K input, minHalting_dom1 K,
    minHalting_byte2 K input, minHalting_dom2 K,
    minHalting_byte3 K input, minHalting_dom3 K,
    trivial⟩

private theorem minHalting_next (K : NatE) (input : Guest.InputBlob) :
    (minHaltingSubmission K).machineConfig.target.next
      ((minHaltingSubmission K).initialState input) =
      branchPost ((minHaltingSubmission K).initialState input) 0x80000014#64 := by
  let ms := (minHaltingSubmission K).initialState input
  have hpc : ms.c_PC ms.procID = 0x80000000#64 := rfl
  have hal : holAligned 2
      (ms.c_PC ms.procID + (((10#20 : BitVec 20).signExtend 64) <<< (1 : Nat))) = true := by
    rw [hpc]
    decide
  have hjal0 : RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.JAL (0, 10#20)))) = 0x6f#8 := by
    decide
  have hjal1 : RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.JAL (0, 10#20)))) = 0x00#8 := by
    decide
  have hjal2 : RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.JAL (0, 10#20)))) = 0x40#8 := by
    decide
  have hjal3 : RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.JAL (0, 10#20)))) = 0x01#8 := by
    decide
  have hb0 : ms.MEM8 (ms.c_PC ms.procID) =
      RiscV.L3.holWordExtract 8 7 0 (Encode (.Branch (.JAL (0, 10#20)))) := by
    rw [hpc, hjal0]
    exact minHalting_byte0 K input
  have hb1 : ms.MEM8 (ms.c_PC ms.procID + 1) =
      RiscV.L3.holWordExtract 8 15 8 (Encode (.Branch (.JAL (0, 10#20)))) := by
    change ms.MEM8 (ms.c_PC ms.procID + 1#64) = _
    rw [hpc, hjal1]
    exact minHalting_byte1 K input
  have hb2 : ms.MEM8 (ms.c_PC ms.procID + 2) =
      RiscV.L3.holWordExtract 8 23 16 (Encode (.Branch (.JAL (0, 10#20)))) := by
    change ms.MEM8 (ms.c_PC ms.procID + 2#64) = _
    rw [hpc, hjal2]
    exact minHalting_byte2 K input
  have hb3 : ms.MEM8 (ms.c_PC ms.procID + 3) =
      RiscV.L3.holWordExtract 8 31 24 (Encode (.Branch (.JAL (0, 10#20)))) := by
    change ms.MEM8 (ms.c_PC ms.procID + 3#64) = _
    rw [hpc, hjal3]
    exact minHalting_byte3 K input
  have hn := near_jump_next ms 10#20
    ((minHaltingSubmission K).initialState_ok input) hal hb0 hb1 hb2 hb3
  change holThe (NextRISCV ms) = branchPost ms 0x80000014#64
  rw [hn, hpc]
  rfl

private theorem minHalting_branchPost_ok (K : NatE) (input : Guest.InputBlob) :
    riscvOk (branchPost ((minHaltingSubmission K).initialState input) 0x80000014#64) = true := by
  let ms := (minHaltingSubmission K).initialState input
  have hok := (riscvOk_iff ms).mp ((minHaltingSubmission K).initialState_ok input)
  apply (riscvOk_iff (branchPost ms 0x80000014#64)).mpr
  have hpc : (branchPost ms 0x80000014#64).c_PC (branchPost ms 0x80000014#64).procID =
      0x80000014#64 := by
    simp [branchPost, holUpdate]
  refine ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, ?_⟩
  rw [hpc]
  decide

private theorem minHalting_ordinaryStep (K : NatE) (input : Guest.InputBlob) :
    OrdinaryStep (minHaltingSubmission K).machineConfig
      ((minHaltingSubmission K).initialState input) where
  program := minHalting_dom0 K
  nonFfi := by
    rw [minHalting_ffiEntryPcs]
    intro h
    cases h
  encoded := minHalting_encodedBytes K input
  beforeOk := (minHaltingSubmission K).initialState_ok input
  afterOk := by
    change riscvOk ((minHaltingSubmission K).machineConfig.target.next
      ((minHaltingSubmission K).initialState input)) = true
    rw [minHalting_next K input]
    exact minHalting_branchPost_ok K input
  outside := by
    intro address _
    change ((minHaltingSubmission K).machineConfig.target.next
      ((minHaltingSubmission K).initialState input)).MEM8 address = _
    rw [minHalting_next K input]
    rfl

private theorem minHalting_eval_one_post (K : NatE) (input : Guest.InputBlob) :
    evaluateTargetHOL (minHaltingSubmission K).machineConfig (sourceFfi input) 1
      (branchPost ((minHaltingSubmission K).initialState input) 0x80000014#64) =
      (.halt .success, branchPost ((minHaltingSubmission K).initialState input) 0x80000014#64,
        sourceFfi input) := by
  let mc := (minHaltingSubmission K).machineConfig
  let post := branchPost ((minHaltingSubmission K).initialState input) 0x80000014#64
  have hpc : mc.target.getPc post = mc.haltPc := by
    change 0x80000014#64 = 0x80000024#64 - 16#64
    decide
  have hnot : ¬ (mc.progAddresses mc.haltPc ∧ mc.haltPc ∉ mc.ffiEntryPcs) := by
    intro h
    have hhalt : mc.haltPc = 0x80000014#64 := by
      change 0x80000024#64 - 16#64 = 0x80000014#64
      decide
    rw [hhalt] at h
    exact minHalting_haltPc_not_program K h.1
  have hreg : mc.target.getReg post mc.ptrReg = 0 := rfl
  change evaluateTargetHOL mc (sourceFfi input) (0 + 1) post = (.halt .success, post, sourceFfi input)
  simp only [evaluateTargetHOL, hpc, if_neg hnot, hreg, ↓reduceIte]

/-- 2. Exact 2-step evaluation of `minHaltingSubmission K` on any `input`. -/
theorem minHaltingSubmission_eval_two (K : NatE) (input : Guest.InputBlob) :
    evaluateTargetHOL (minHaltingSubmission K).machineConfig (sourceFfi input) 2
      ((minHaltingSubmission K).initialState input) =
      (.halt .success, branchPost ((minHaltingSubmission K).initialState input) 0x80000014#64,
        sourceFfi input) := by
  have hstep := ordinary_step_evaluate
    (mc := (minHaltingSubmission K).machineConfig) rfl (sourceFfi input) 1
    (minHalting_ordinaryStep K input)
  rw [hstep, minHalting_next K input]
  exact minHalting_eval_one_post K input

private theorem hostInputBytes_length_eq (input : Guest.InputBlob) :
    (Guest.hostInputBytes input).length =
      8 + 8 + input.length + (8 - input.length % 8) % 8 := by
  unfold Guest.hostInputBytes Guest.leBytes
  simp [List.length_append, List.length_replicate, List.length_map, List.length_range]
  omega

private theorem outputByte_nil_32_eq_zero (input : Guest.InputBlob)
    (hlen : input.length ≤ Guest.maxInputBytes) :
    outputByte input [] ⟨32, by decide⟩ = 0 := by
  unfold outputByte observedHost replayOracle List.foldl Guest.guestHostMemory
  have hlen_bound : (Guest.hostInputBytes input).length ≤ 1073741824 := by
    rw [hostInputBytes_length_eq]
    unfold Guest.maxInputBytes at hlen
    omega
  have hnotIn : ¬ (Guest.inputAddr ≤ BitVec.ofNat 64 outputStart + BitVec.ofNat 64 32 ∧
      BitVec.ofNat 64 outputStart + BitVec.ofNat 64 32 <
        Guest.inputAddr + BitVec.ofNat 64 (Guest.hostInputBytes input).length) := by
    intro h
    have hlt := h.2
    change (2688614432 : BitVec 64) < (1073741824 : BitVec 64) + BitVec.ofNat 64 (Guest.hostInputBytes input).length at hlt
    rw [BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_ofNat] at hlt
    have hmod : (Guest.hostInputBytes input).length % 2 ^ 64 = (Guest.hostInputBytes input).length :=
      Nat.mod_eq_of_lt (by omega)
    rw [hmod] at hlt
    change 2688614432 < (1073741824 + (Guest.hostInputBytes input).length) % 18446744073709551616 at hlt
    omega
  have hOut : Guest.outputAddr ≤ BitVec.ofNat 64 outputStart + BitVec.ofNat 64 32 ∧
      BitVec.ofNat 64 outputStart + BitVec.ofNat 64 32 < Guest.scratchBase := by
    decide
  simp only [if_neg hnotIn, if_pos hOut, Option.getD_some]

private theorem not_acceptedOutput_success_nil (input : Guest.InputBlob)
    (hlen : input.length ≤ Guest.maxInputBytes) :
    ¬ acceptedOutput input .success [] := by
  intro h
  have hbyte := h.2
  rw [outputByte_nil_32_eq_zero input hlen] at hbyte
  revert hbyte
  decide

/-- 3. `minHaltingSubmission K` matches at step 2 on every input where `¬ acceptedOutput`. -/
theorem minHaltingSubmission_matches_unaccepted (K : NatE) (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hlen : input.length ≤ Guest.maxInputBytes)
    (hnot : ¬ acceptedOutput input outcome events) :
    matchingExecutionAt (minHaltingSubmission K) input outcome events 2 := by
  refine ⟨.success, branchPost ((minHaltingSubmission K).initialState input) 0x80000014#64,
    sourceFfi input, minHaltingSubmission_eval_two K input, ?_⟩
  unfold matchingResult
  rw [if_neg hnot]
  exact ⟨trivial, not_acceptedOutput_success_nil input hlen⟩

end InitECandidate.Solver.FastHalt
