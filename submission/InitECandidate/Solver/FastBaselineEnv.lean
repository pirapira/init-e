import InitECandidate.Proofs.CompilerComputation
import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.CompilerConfigLiteral
import InitECandidate.Proofs.BootstrapMemory
import InitECandidate.Proofs.LiteralFacts
import InitECandidate.Proofs.MachineWordMemory
import InitECandidate.Proofs.BitmapImageFacts
import InitECandidate.Proofs.MachineConfigurationFields
import InitECandidate.Proofs.BootstrapCopyTrace
import InitECandidate.Proofs.BootstrapAsmComposition
import InitECandidate.Proofs.BootstrapStraightLine
import InitECandidate.Proofs.BootstrapTailMemory
import InitECandidate.Proofs.PanInstallationConstructor
import InitECandidate.Proofs.BitmapSeparation
import InitECandidate.Proofs.SourceMemoryInstallation
import InitE.MachineInitialization
import InitE.SubmissionInitialization
import InitE.SubmissionAdmission
import Flapjack.Compiler.Backend.Semantics.TargetSem.InitializationContracts
import Flapjack.Pancake.Proofs.PanToTarget.PanInstalled

/-!
# InitECandidate.Solver.FastBaselineEnv — Self-Contained Baseline Installation & Bootstrap Environment

Decoupled inside submission/InitECandidate/Solver/ so that Solution.lean and Solver/
depend ONLY on the 33 upstream-clean modules of InitECandidate.Proofs.* (which never import
ArtifactFacts, BaselineArtifact, or Stages in a267157e2).
-/


open scoped InitECandidate.Proofs.CompilerComputation

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
set_option linter.unusedSimpArgs false
set_option autoImplicit false


/-! ## Section BaselineMetadata -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Misc

@[irreducible] def baselineNames : List HolFfiName := baselineLabConfig.ffiNames.getD []
@[irreducible] def baselineMmio : List ShmemInfoNum := baselineLabConfig.shmemExtra

def dispatchAddress (i : Nat) : BitVec 64 :=
  BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((1+i)*ffiOffset)

def baselineEntryPcs : List (BitVec 64) :=
  ((List.range 2).map fun i => BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((3+i)*ffiOffset)) ++
    (baselineMmio.map fun rec => BitVec.ofNat 64 nativePc + BitVec.ofNat 64 rec.entryPc)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
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
  unfold ffiNameBoundaryValid baselineEntryPcs baselineNames baselineMmio baselineLabConfig
  exact of_decide_eq_true (by kernel_rfl)

end InitECandidate.Solver.FastEnv

/-! ## Section BaselineInstallationFacts -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
open InitECandidate.Proofs
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Misc

/-- Only ordinary dispatch addresses are removed. Native MMIO instructions
remain loaded program bytes and are intercepted through ffiEntryPcs. -/
def programDomain (a : BitVec 64) : Prop :=
  bootstrapDomain a

noncomputable def baselineMachineConfig : MachineConfig 64 riscv_state RiscVProjection :=
  challengeMachineConfig (BitVec.ofNat 64 nativePc) programDomain machineSharedDomain
    baselineNames 2 baselineMmio

/-- Explicit reduced integer RISC-V machine: machine privilege, identity
translation, no pending transfer and no exception. -/
def machineStateOfAsm (t : AsmState 64) : riscv_state :=
  { (default : riscv_state) with
    MEM8 := t.mem
    c_MCSR := fun _ => { (default : MachineCSR) with
      mstatus := { (default : mstatus) with MPRV := 3, VM := 0 }
      mcpuid := { (default : mcpuid) with ArchBase := 2 } }
    c_PC := fun _ => t.pc
    c_gpr := fun _ r => t.regs r.toNat
    c_NextFetch := fun _ => none
    exception := .NoException }

theorem machineStateOfAsm_mode (t : AsmState 64) :
    ((machineStateOfAsm t).c_MCSR (machineStateOfAsm t).procID).mstatus.MPRV = 3 ∧
    ((machineStateOfAsm t).c_MCSR (machineStateOfAsm t).procID).mstatus.VM = 0 :=
  ⟨rfl,rfl⟩

theorem machineStateOfAsm_ok (t : AsmState 64) (hpc : holAligned 2 t.pc = true) :
    riscvOk (machineStateOfAsm t) = true := by
  exact (riscvOk_iff _).mpr ⟨rfl,rfl,rfl,rfl,hpc⟩

theorem machineStateOfAsm_relation (t : AsmState 64) (hpc : holAligned 2 t.pc = true) :
    targetStateRel riscvTarget t (machineStateOfAsm t) := by
  refine ⟨machineStateOfAsm_ok t hpc, rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro i hi
    have hilt : i < 32 := hi.1
    change t.regs (BitVec.ofNat 5 i).toNat = t.regs i
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hilt]
  · intro i hi
    have : i < 0 := hi
    omega

theorem baseline_ffi_boundary : mmioPcsMinIndex baselineNames = some 2 :=
  ffiNameBoundaryValid_sound _ _ baseline_finite_facts.1

theorem baseline_ffi_interference :
    ffiInterferOkHOL (BitVec.ofNat 64 nativePc) baselineMachineConfig :=
  challengeMachineConfig_ffiOk_checked _ _ _ _ _ _ baseline_ffi_boundary
    baseline_finite_facts.2.1

theorem baseline_cache_interference :
    ccacheInterferOkHOL (BitVec.ofNat 64 nativePc) baselineMachineConfig :=
  challengeMachineConfig_cacheOk _ _ _ _ _ _

theorem baseline_machine_isRiscv :
    Flapjack.Compiler.Backend.RiscVConfig.isRiscvMachineConfig baselineMachineConfig :=
  challengeMachineConfig_isRiscv _ _ _ _ _ _

theorem baseline_machine_noInterference :
    interferenceOk baselineMachineConfig.nextInterfer
      (baselineMachineConfig.target.proj programDomain) :=
  challengeMachineConfig_noInterference _ _ _ _ _ _

private theorem dispatch_not_program (i : Fin 4) : ¬ programDomain (dispatchAddress i.val) := by
  intro h
  exact h.2 i.val i.isLt (by simpa [dispatchAddress, ffiOffset, Nat.mul_comm, Nat.add_comm] using (rfl : dispatchAddress i.val = dispatchAddress i.val))

private theorem dispatch_not_shared (i : Fin 4) :
    ¬ machineSharedDomain (dispatchAddress i.val) := by
  have bounds : 0x80001000 ≤ (dispatchAddress i.val).toNat ∧
      (dispatchAddress i.val).toNat < 0x80002000 := by
    have h : ∀ j : Fin 4, 0x80001000 ≤ (dispatchAddress j.val).toNat ∧
        (dispatchAddress j.val).toNat < 0x80002000 := by decide
    exact h i
  simp only [machineSharedDomain, inputStart, inputEnd, inputSize, outputStart, outputEnd]
  omega

theorem baseline_start_pc : startPcOk baselineMachineConfig (BitVec.ofNat 64 nativePc) := by
  refine ⟨dispatch_not_program ⟨0,by decide⟩,
    dispatch_not_program ⟨1,by decide⟩,
    dispatch_not_shared ⟨0,by decide⟩,
    dispatch_not_shared ⟨1,by decide⟩, rfl, rfl, by decide,
    2, baseline_ffi_boundary, ?_, ?_, baseline_finite_facts.2.2.2.2⟩
  · intro index hi
    have heq : BitVec.ofNat 64 nativePc - BitVec.ofNat 64 ((3+index)*ffiOffset) =
        dispatchAddress (index+2) := by
      simp only [dispatchAddress]
      rw [show 3+index = 1+(index+2) by omega]
    refine ⟨?_, ?_, ?_, ?_, baseline_finite_facts.2.2.1 ⟨index,hi⟩⟩
    · rw [heq]; exact dispatch_not_program ⟨index+2,by omega⟩
    · rw [heq]; exact dispatch_not_shared ⟨index+2,by omega⟩
    · have h : ∀ j : Fin 2, dispatchAddress (j.val+2) ≠ dispatchAddress 0 := by decide
      simpa [heq, baselineMachineConfig, challengeMachineConfig, dispatchAddress] using h ⟨index,hi⟩
    · have h : ∀ j : Fin 2, dispatchAddress (j.val+2) ≠ dispatchAddress 1 := by decide
      simpa [heq, baselineMachineConfig, challengeMachineConfig, dispatchAddress] using h ⟨index,hi⟩
  · intro index hi
    have hlen : index < baselineEntryPcs.length := by
      rw [←baseline_finite_facts.2.2.2.2]; exact hi.1
    change dispatchAddress 0 ≠ holEl index baselineEntryPcs ∧ dispatchAddress 1 ≠ holEl index baselineEntryPcs
    rw [holEl_eq_getElem index baselineEntryPcs hlen]
    exact baseline_finite_facts.2.2.2.1 ⟨index,hlen⟩ hi.2

theorem baseline_literal_layout : InitECandidate.bootPrefix.length = 4208 ∧
    InitECandidate.nativeCode.length = 979140 ∧ InitECandidate.code.length = 1028080 :=
  ⟨LiteralFacts.bootPrefix_length, LiteralFacts.nativeCode_length, LiteralFacts.code_length⟩

private theorem literal_append_byte (leadingBytes bytes trailingBytes : List (BitVec 8))
    (i : Fin bytes.length) :
    ((leadingBytes ++ bytes ++ trailingBytes)[leadingBytes.length+i.val]?.getD 0) = bytes[i] := by
  rw [List.append_assoc]
  simp [List.getElem?_append, show ¬ leadingBytes.length+i.val < leadingBytes.length by omega,
    Nat.add_sub_cancel_left, i.isLt]

private theorem initialMemory_of_lt (a : BitVec 64) (k : Nat) (ha : a.toNat = initialPc + k)
    (hk : k < InitECandidate.code.length) :
    initialMemory a = InitECandidate.code[k]?.getD 0 := by
  unfold initialMemory
  rw [if_pos (by omega)]
  have hsub : a.toNat - initialPc = k := by omega
  rw [hsub]

theorem baseline_native_loaded_byte (i : Fin InitECandidate.nativeCode.length) :
    installedMemory (BitVec.ofNat 64 nativePc + BitVec.ofNat 64 i.val) =
      InitECandidate.nativeCode[i] := by
  have hi : i.val < 979140 := by simpa only [baseline_literal_layout.2.1] using i.isLt
  have ha : (BitVec.ofNat 64 nativePc + BitVec.ofNat 64 i.val).toNat = nativePc+i.val := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hn : nativePc < 2^64 := by decide
    rw [Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt (by omega : i.val < 2^64),
      Nat.mod_eq_of_lt (by simp only [nativePc]; omega : nativePc+i.val < 2^64)]
  have hsource : ¬ (sourceBase ≤ nativePc+i.val ∧ nativePc+i.val < sourceBase+40) := by
    simp only [sourceBase, nativePc]; omega
  have hdata : ¬ (initDataRam ≤ nativePc+i.val ∧ nativePc+i.val < initDataRam+24) := by
    simp only [initDataRam, nativePc]; omega
  have hbitmap : ¬ (initDataRam+24 ≤ nativePc+i.val ∧ nativePc+i.val < initDataEnd) := by
    simp only [initDataRam, nativePc]; omega
  simp only [installedMemory, ha, if_neg hsource, if_neg hdata, if_neg hbitmap]
  rw [initialMemory_of_lt (BitVec.ofNat 64 nativePc + BitVec.ofNat 64 i.val)
    (InitECandidate.bootPrefix.length + i.val)
    (by rw [ha]; simp only [nativePc, initialPc, baseline_literal_layout.1]; omega)
    (by simp only [baseline_literal_layout.1, baseline_literal_layout.2.2]; omega)]
  unfold InitECandidate.code
  exact literal_append_byte InitECandidate.bootPrefix InitECandidate.nativeCode InitECandidate.suffix i

theorem baseline_native_program_byte (i : Fin InitECandidate.nativeCode.length) :
    programDomain (BitVec.ofNat 64 nativePc + BitVec.ofNat 64 i.val) := by
  have hi : i.val < 979140 := by simpa only [baseline_literal_layout.2.1] using i.isLt
  have ha : (BitVec.ofNat 64 nativePc + BitVec.ofNat 64 i.val).toNat = nativePc+i.val := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by decide : nativePc < 2^64),
      Nat.mod_eq_of_lt (by omega : i.val < 2^64),
      Nat.mod_eq_of_lt (by simp only [nativePc]; omega : nativePc+i.val < 2^64)]
  refine ⟨?_, ?_⟩
  · simp only [memoryDomain, machineSharedDomain]
    rw [ha]
    simp only [initialPc, nativePc,
      codeSizeLimit, inputStart,inputEnd,inputSize,outputStart,outputEnd]
    constructor
    · left; omega
    · omega
  · intro j hj heq
    have hlow : (dispatchAddress j).toNat < nativePc := by
      have hh : ∀ k : Fin 4, (dispatchAddress k.val).toNat < nativePc := by decide
      exact hh ⟨j,hj⟩
    have haddr := congrArg BitVec.toNat heq
    have hd : BitVec.ofNat 64 nativePc - BitVec.ofNat 64 (16*(j+1)) = dispatchAddress j := by
      simp [dispatchAddress,ffiOffset,Nat.add_comm,Nat.mul_comm]
    rw [hd,ha] at haddr
    omega

noncomputable def baselineInstalledState : riscv_state := machineStateOfAsm installedAsm

theorem baseline_native_codeLoaded :
    codeLoaded InitECandidate.nativeCode baselineMachineConfig baselineInstalledState := by
  apply readBytearray_literal
  intro i
  have hprog : baselineMachineConfig.progAddresses
      (baselineMachineConfig.target.getPc baselineInstalledState + BitVec.ofNat 64 i.val) :=
    baseline_native_program_byte i
  rw [if_pos hprog]
  exact congrArg some (baseline_native_loaded_byte i)

end InitECandidate.Solver.FastEnv

/-! ## Section BaselineMemoryDomains -/

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackRemove

/-- Compiler data consists of accessible sourceRAM and copied bitmap bytes. -/
def baselineBitmapDm (a : BitVec 64) : Bool :=
  decide (initDataRam + 24 ≤ a.toNat ∧ a.toNat < initDataEnd)
def baselineDataDm (a : BitVec 64) : Bool :=
  decide (sourceBase ≤ a.toNat ∧ a.toNat < ramEnd) || baselineBitmapDm a
def baselineSharedDm (a : BitVec 64) : Bool :=
  decide ((inputStart ≤ a.toNat ∧ a.toNat < inputEnd) ∨
    (outputStart ≤ a.toNat ∧ a.toNat < outputEnd))

theorem baseline_shared_domain : (fun a => baselineSharedDm a = true) =
    baselineMachineConfig.sharedAddresses := by
  funext a
  simp [baselineSharedDm, baselineMachineConfig, challengeMachineConfig, machineSharedDomain]

theorem baseline_data_aligned_closed (a : BitVec 64)
    (h : baselineDataDm (holByteAlign a) = true) : baselineDataDm a = true := by
  simp only [baselineDataDm, baselineBitmapDm, Bool.or_eq_true, decide_eq_true_eq] at h ⊢
  rw [holByteAlign_toNat (Or.inr rfl)] at h
  norm_num [sourceBase, ramEnd, ramStart, ramSize, initDataRam, initDataEnd] at h ⊢
  have modBound := Nat.mod_lt a.toNat (by decide : 0 < 8)
  have division := Nat.div_add_mod a.toNat 8
  omega

theorem baseline_shared_aligned_closed (a : BitVec 64)
    (h : baselineSharedDm (holByteAlign a) = true) : baselineSharedDm a = true := by
  simp only [baselineSharedDm, decide_eq_true_eq] at h ⊢
  rw [holByteAlign_toNat (Or.inr rfl)] at h
  norm_num [inputStart, inputEnd, inputSize, outputStart, outputEnd, outputSize] at h ⊢
  have modBound := Nat.mod_lt a.toNat (by decide : 0 < 8)
  have division := Nat.div_add_mod a.toNat 8
  omega

private theorem native_dispatch_below (i : Nat) (hi : i < 4) :
    (BitVec.ofNat 64 nativePc - BitVec.ofNat 64 (16 * (i + 1))).toNat < nativePc := by
  have offNat : (BitVec.ofNat 64 (16 * (i + 1))).toNat = 16 * (i + 1) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have pcNat : (BitVec.ofNat 64 nativePc).toNat = nativePc := by decide
  have less : BitVec.ofNat 64 (16 * (i + 1)) ≤ BitVec.ofNat 64 nativePc := by
    apply BitVec.le_def.mpr
    rw [offNat, pcNat]
    norm_num [nativePc]
    omega
  rw [BitVec.toNat_sub_of_le less, pcNat, offNat]
  norm_num [nativePc]

theorem baseline_data_program (a : BitVec 64) (h : baselineDataDm a = true) :
    programDomain a := by
  simp only [baselineDataDm, baselineBitmapDm, Bool.or_eq_true, decide_eq_true_eq] at h
  constructor
  · unfold memoryDomain machineSharedDomain
    norm_num [initialPc, codeSizeLimit, ramStart, ramEnd, ramSize,
      inputStart, inputEnd, inputSize, outputStart, outputEnd, outputSize,
      sourceBase, initDataRam, initDataEnd] at h ⊢
    omega
  · intro i hi eq
    have low := native_dispatch_below i hi
    have value := congrArg BitVec.toNat eq
    have alow : a.toNat < nativePc := by rw [value]; exact low
    norm_num [sourceBase, ramEnd, ramStart, ramSize, initDataRam, initDataEnd, nativePc] at h alow
    omega

theorem baseline_program_shared_disjoint :
    Disjoint (α := Set (BitVec 64)) (Set.ofPred baselineMachineConfig.progAddresses)
      (Set.ofPred baselineMachineConfig.sharedAddresses) := by
  apply Set.disjoint_left.mpr
  intro a prog shared
  exact prog.1.2 shared

private theorem native_address_nat (offset : Nat) (bound : offset < 982928) :
    (BitVec.ofNat 64 nativePc + BitVec.ofNat 64 offset).toNat = nativePc + offset := by
  rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  norm_num [nativePc]
  omega

private theorem native_data_excluded (offset : Nat) (bound : offset < 982928) :
    baselineDataDm (BitVec.ofNat 64 nativePc + BitVec.ofNat 64 offset) ≠ true := by
  rw [baselineDataDm, baselineBitmapDm, native_address_nat offset bound]
  norm_num [sourceBase, ramEnd, ramStart, ramSize, initDataRam, initDataEnd, nativePc]
  omega

theorem baseline_code_bytes :
    bytesInMemHOL installedAsm.pc InitECandidate.nativeCode installedAsm.mem
      installedAsm.memDomain (fun a => baselineDataDm a = true) := by
  apply bytesInMem_literal
  intro i
  have bound : i.val < 982928 := by
    have hi : i.val < 979140 := by simpa only [baseline_literal_layout.2.1] using i.isLt
    omega
  exact ⟨baseline_native_program_byte i, native_data_excluded i.val bound,
    baseline_native_loaded_byte i⟩

theorem baseline_code_buffer (n : Nat) (hn : n < 3788) :
    installedAsm.memDomain (BitVec.ofNat 64 (n + InitECandidate.nativeCode.length) + installedAsm.pc) ∧
    baselineDataDm (BitVec.ofNat 64 (n + InitECandidate.nativeCode.length) + installedAsm.pc) ≠ true := by
  have count := baseline_literal_layout.2.1
  have offset : n + InitECandidate.nativeCode.length < 982928 := by rw [count]; omega
  have addr : BitVec.ofNat 64 (n + InitECandidate.nativeCode.length) + installedAsm.pc =
      BitVec.ofNat 64 nativePc + BitVec.ofNat 64 (n + InitECandidate.nativeCode.length) :=
    BitVec.add_comm _ _
  rw [addr]
  refine ⟨?_, native_data_excluded _ offset⟩
  constructor
  · unfold memoryDomain machineSharedDomain
    rw [native_address_nat _ offset]
    norm_num [initialPc, codeSizeLimit, ramStart, ramEnd, ramSize, nativePc,
      inputStart, inputEnd, inputSize, outputStart, outputEnd, outputSize]
    omega
  · intro i hi eq
    have low := native_dispatch_below i hi
    have value := congrArg BitVec.toNat eq
    rw [native_address_nat _ offset] at value
    omega

theorem baseline_code_size_bound : 3788 + InitECandidate.nativeCode.length < 2 ^ 64 := by
  rw [baseline_literal_layout.2.1]
  decide

private theorem bitmap_index_address (i : Nat) (hi : i < 4603) :
    (BitVec.ofNat 64 (initDataRam + 24) + BitVec.ofNat 64 i * (8 : BitVec 64)).toNat =
      0xa0020018 + 8 * i := by
  have sum : BitVec.ofNat 64 (initDataRam + 24) + BitVec.ofNat 64 i * (8 : BitVec 64) =
      BitVec.ofNat 64 (0xa0020018 + 8 * i) := by
    simp [initDataRam, BitVec.ofNat_add, BitVec.ofNat_mul, Nat.mul_comm]
  rw [sum, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

/-- The compiler bitmap Boolean byte region yields precisely its4613aligned
word cells. This identifies its separation-logic domain with the logical
compiler's original `addresses` predicate. -/
theorem baseline_bitmap_aligned_domain :
    (fun a : BitVec 64 => holByteAligned a = true ∧ baselineBitmapDm a = true) =
      addresses (BitVec.ofNat 64 (initDataRam + 24)) InitECandidate.bitmaps.length := by
  funext a
  apply propext
  rw [mem_addresses, bitmap_count]
  have aligned : holByteAligned a = true ↔ a.toNat % 8 = 0 := by
    have log : holLOG2 (64 / 8) = 3 := by simp [holLOG2_eq_log2]
    simpa only [holByteAligned, log] using Flapjack.holAligned_iff 3 a
  rw [aligned]
  simp only [baselineBitmapDm, decide_eq_true_eq]
  norm_num [initDataRam, initDataEnd]
  constructor
  · rintro ⟨align, lower, upper⟩
    let i := (a.toNat - 0xa0020018) / 8
    have remainder : (a.toNat - 0xa0020018) % 8 = 0 := by omega
    have division := Nat.div_add_mod (a.toNat - 0xa0020018) 8
    have ibound : i < 4603 := by dsimp [i]; omega
    refine ⟨i, ibound, ?_⟩
    apply BitVec.eq_of_toNat_eq
    have addr := bitmap_index_address i ibound
    have addr' : (2684485656#64 + BitVec.ofNat 64 i * bytesInWord 64).toNat =
        0xa0020018 + 8 * i := by exact addr
    rw [addr']
    dsimp [i]
    omega
  · rintro ⟨i, hi, equality⟩
    have address := bitmap_index_address i hi
    have numeric : a.toNat = 0xa0020018 + 8 * i := by
      rw [equality]
      exact address
    rw [numeric]
    constructor
    · omega
    · omega

theorem baseline_heap_bitmap_disjoint (a : BitVec 64) :
    ¬ (decide (BitVec.ofNat 64 sourceBase ≤ a ∧ a < BitVec.ofNat 64 ramEnd) = true ∧
      baselineBitmapDm a = true) := by
  simp only [decide_eq_true_eq, BitVec.le_def, BitVec.lt_def, baselineBitmapDm]
  norm_num [sourceBase, ramEnd, ramStart, ramSize, initDataRam, initDataEnd]
  omega

end InitECandidate.Solver.FastEnv

/-! ## Section StartupEnvironment -/

set_option maxRecDepth 10000

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
open Classical
open Flapjack Flapjack.RiscV.L3 Flapjack.Compiler.Encoders.RiscV.Target

/-- The fixed startup environment: submitted ROM, zero ordinary RAM/registers,
and public input/output bytes supplied by the common host oracle. -/
noncomputable def baselineInitialState (input : Guest.InputBlob) : riscv_state :=
  { (machineStateOfAsm initialAsm) with MEM8 := (fun a =>
      if (machineSharedDomain a) then byteToBits ((Guest.guestHostMemory input a).getD 0)
      else initialMemory a) }

theorem baselineInitialState_mode (input : Guest.InputBlob) :
    ((baselineInitialState input).c_MCSR (baselineInitialState input).procID).mstatus.MPRV = 3 ∧
    ((baselineInitialState input).c_MCSR (baselineInitialState input).procID).mstatus.VM = 0 :=
  ⟨rfl,rfl⟩

theorem baselineInitialState_related (input : Guest.InputBlob) :
    targetStateRel riscvTarget initialAsm (baselineInitialState input) := by
  have canonical := machineStateOfAsm_relation initialAsm (by decide)
  refine ⟨?_,canonical.2.1,?_,canonical.2.2.2.1,?_⟩
  · exact (riscvOk_iff (baselineInitialState input)).mpr ⟨rfl,rfl,rfl,rfl,by change holAligned 2 (BitVec.ofNat 64 initialPc) = true; decide⟩
  · intro a domain
    change (if (machineSharedDomain a) then byteToBits ((Guest.guestHostMemory input a).getD 0)
      else initialMemory a) = initialMemory a
    exact if_neg domain.1.2
  · intro r hr
    have : r < 0 := hr
    omega

theorem baselineInitialState_ram_zero (input : Guest.InputBlob) (a : BitVec 64)
    (ram : ramStart ≤ a.toNat) (ordinary : ¬ machineSharedDomain a) :
    (baselineInitialState input).MEM8 a = 0 := by
  change (if (machineSharedDomain a) then _ else initialMemory a) = 0
  rw [if_neg ordinary]
  exact initial_ram_zero a ram

theorem baselineInitialState_registers_zero (input : Guest.InputBlob) (r : BitVec 5) :
    (baselineInitialState input).c_gpr (baselineInitialState input).procID r = 0 := rfl

end InitECandidate.Solver.FastEnv

/-! ## Section BaselineSubmissionDefinition -/

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
open Classical
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend.LabToTarget

def baselineSubmission : Submission :=
  { code := InitECandidate.code, K := .infinity
    anchorPc := nativePc, names := baselineNames, first := 2, extra := baselineMmio }

theorem baselineSubmission_machineConfig : baselineSubmission.machineConfig = baselineMachineConfig := rfl

private theorem baseline_pureMemory : romMemory InitECandidate.code = initialMemory := rfl

private theorem baselineSubmission_memory (input : Guest.InputBlob) :
    baselineSubmission.initialMemory input = (fun a =>
      if machineSharedDomain a then byteToBits ((Guest.guestHostMemory input a).getD 0)
      else initialMemory a) := by
  have h := submission_record_memory InitECandidate.code .infinity nativePc baselineNames 2 baselineMmio input
  rw [baseline_pureMemory] at h
  have hd : submissionSharedDomain = machineSharedDomain := rfl
  unfold hostOverlay at h
  rw [hd] at h
  exact h

theorem baselineSubmission_initialState (input : Guest.InputBlob) :
    baselineSubmission.initialState input = baselineInitialState input := by
  unfold Submission.initialState
  rw [baselineSubmission_memory]
  rfl



end InitECandidate.Solver.FastEnv

/-! ## Section BaselineSubmissionFacts -/

/- Small metadata literals are checked against the compiler configuration once.
The predicates keep finite-index bound proofs independent of that large
configuration; ordinary decide checks the resulting small literal goals. -/
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
open Flapjack

private def admissionMmio : List Compiler.Backend.LabToTarget.ShmemInfoNum :=
  [{ entryPc := 4744, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 11, exitPc := 4748 },
   { entryPc := 4788, nbytes := BitVec.ofNat 8 0, addrReg := 13, addrOff := 0, reg := 12, exitPc := 4792 },
   { entryPc := 4820, nbytes := BitVec.ofNat 8 0, addrReg := 12, addrOff := 0, reg := 10, exitPc := 4824 },
   { entryPc := 9396, nbytes := BitVec.ofNat 8 0, addrReg := 10, addrOff := 0, reg := 11, exitPc := 9400 },
   { entryPc := 9692, nbytes := BitVec.ofNat 8 0, addrReg := 12, addrOff := 0, reg := 12, exitPc := 9696 },
   { entryPc := 9776, nbytes := BitVec.ofNat 8 1, addrReg := 5, addrOff := 0, reg := 13, exitPc := 9780 },
   { entryPc := 179152, nbytes := BitVec.ofNat 8 0, addrReg := 11, addrOff := 0, reg := 11, exitPc := 179156 },
   { entryPc := 179760, nbytes := BitVec.ofNat 8 0, addrReg := 10, addrOff := 0, reg := 11, exitPc := 179764 },
   { entryPc := 977604, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 977608 },
   { entryPc := 977820, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 977824 },
   { entryPc := 978036, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 978040 },
   { entryPc := 978252, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 978256 },
   { entryPc := 978468, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 978472 },
   { entryPc := 978684, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 978688 },
   { entryPc := 978900, nbytes := BitVec.ofNat 8 1, addrReg := 10, addrOff := 0, reg := 1, exitPc := 978904 }]

-- Reduce the large configuration projection once, before finite checks.
private theorem admission_mmio_eq : baselineMmio = admissionMmio := by
  unfold baselineMmio
  change baselineLabConfig.shmemExtra = admissionMmio
  rfl

private def admissionEntryPcs : List (BitVec 64) :=
  [BitVec.ofNat 64 2147487808,
   BitVec.ofNat 64 2147487792,
   BitVec.ofNat 64 2147492600,
   BitVec.ofNat 64 2147492644,
   BitVec.ofNat 64 2147492676,
   BitVec.ofNat 64 2147497252,
   BitVec.ofNat 64 2147497548,
   BitVec.ofNat 64 2147497632,
   BitVec.ofNat 64 2147667008,
   BitVec.ofNat 64 2147667616,
   BitVec.ofNat 64 2148465460,
   BitVec.ofNat 64 2148465676,
   BitVec.ofNat 64 2148465892,
   BitVec.ofNat 64 2148466108,
   BitVec.ofNat 64 2148466324,
   BitVec.ofNat 64 2148466540,
   BitVec.ofNat 64 2148466756]

private theorem admission_entry_pcs_eq : baselineEntryPcs = admissionEntryPcs := by
  unfold baselineEntryPcs
  rw [admission_mmio_eq]
  rfl

private theorem admission_names_length :
    baselineNames.length = 2 + baselineMmio.length := by
  calc
    baselineNames.length = baselineEntryPcs.length :=
      baseline_finite_facts.2.2.2.2
    _ = 2 + baselineMmio.length := by
      simp only [baselineEntryPcs, List.length_append, List.length_map, List.length_range]

private theorem admission_entry_nodup : baselineEntryPcs.Nodup := by
  simp only [admission_entry_pcs_eq]
  decide

private def admissionEntryConditions (pcs : List (BitVec 64)) : Prop :=
  ∀ i : Fin pcs.length,
    initialPc < pcs[i].toNat ∧ pcs[i].toNat < initialPc + 1028080 ∧
    holAligned 2 pcs[i] = true ∧
    pcs[i] ≠ BitVec.ofNat 64 nativePc - 16 ∧
    pcs[i] ≠ BitVec.ofNat 64 nativePc - 32

private def admissionMmioBounds
    (mmio : List Compiler.Backend.LabToTarget.ShmemInfoNum) : Prop :=
  ∀ i : Fin mmio.length,
    mmio[i].entryPc < 979140 ∧ nativePc + mmio[i].exitPc < initialPc + 1028080


private theorem admission_entry_conditions :
    (∀ i : Fin baselineEntryPcs.length,
      initialPc < baselineEntryPcs[i].toNat ∧
      baselineEntryPcs[i].toNat < initialPc + 1028080 ∧
      holAligned 2 baselineEntryPcs[i] = true ∧
      baselineEntryPcs[i] ≠ BitVec.ofNat 64 nativePc - 16 ∧
      baselineEntryPcs[i] ≠ BitVec.ofNat 64 nativePc - 32) := by
  change admissionEntryConditions baselineEntryPcs
  rw [admission_entry_pcs_eq]
  unfold admissionEntryConditions
  decide


private theorem admission_mmio_bounds :
    (∀ i : Fin baselineMmio.length,
      baselineMmio[i].entryPc < 979140 ∧
      nativePc + baselineMmio[i].exitPc < initialPc + 1028080) := by
  change admissionMmioBounds baselineMmio
  rw [admission_mmio_eq]
  unfold admissionMmioBounds
  decide


-- Preserve the exported contract and all downstream projection selectors.
theorem baseline_submission_finite :
    baselineNames.length = 2 + baselineMmio.length ∧
    baselineEntryPcs.Nodup ∧
    (∀ i : Fin baselineEntryPcs.length,
      initialPc < baselineEntryPcs[i].toNat ∧
      baselineEntryPcs[i].toNat < initialPc + 1028080 ∧
      holAligned 2 baselineEntryPcs[i] = true ∧
      baselineEntryPcs[i] ≠ BitVec.ofNat 64 nativePc - 16 ∧
      baselineEntryPcs[i] ≠ BitVec.ofNat 64 nativePc - 32) ∧
    (∀ i : Fin baselineMmio.length,
      baselineMmio[i].entryPc < 979140 ∧
      nativePc + baselineMmio[i].exitPc < initialPc + 1028080) := by
  exact ⟨admission_names_length, admission_entry_nodup,
    admission_entry_conditions, admission_mmio_bounds⟩

end InitECandidate.Solver.FastEnv

/-! ## Section BaselineSubmission -/

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend.LabToTarget
private theorem entryPc_model :
    (⟨InitECandidate.code,.infinity,nativePc,baselineNames,2,baselineMmio⟩ : Submission).machineConfig.ffiEntryPcs = baselineEntryPcs := by
  change baselineSubmission.machineConfig.ffiEntryPcs = baselineEntryPcs
  rw [baselineSubmission_machineConfig]
  exact challengeMachineConfig_entries (BitVec.ofNat 64 nativePc) programDomain
    machineSharedDomain baselineNames 2 baselineMmio
private theorem program_model :
    (⟨InitECandidate.code,.infinity,nativePc,baselineNames,2,baselineMmio⟩ : Submission).programDomain = programDomain := rfl

private theorem baselineSubmission_code : baselineSubmission.code = InitECandidate.code := rfl

theorem baselineSubmission_admitted : baselineSubmission.Admitted := by
  have hsize : InitECandidate.code.length = 1028080 := baseline_literal_layout.2.2
  refine Submission.admitted_literal InitECandidate.code .infinity nativePc baselineNames 2 baselineMmio
    ?_ ?_ (by decide) ?_ (by decide) baseline_finite_facts.1
    baseline_submission_finite.1 ?_ baseline_finite_facts.2.1 ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hsize]; decide
  · rw [hsize]; decide
  · rw [hsize]; change nativePc < initialPc + 1028080; decide
  · have h : ∀ i : Fin 4,
        let a := BitVec.ofNat 64 nativePc - BitVec.ofNat 64 (ffiOffset * (i.val+1))
        initialPc < a.toNat ∧ a.toNat < initialPc + 1028080 := by decide
    simpa only [baseline_literal_layout.2.2] using h
  · rw [entryPc_model]; exact baseline_submission_finite.2.1
  · intro a ha
    rw [entryPc_model] at ha
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem ha
    subst a
    have hh := baseline_submission_finite.2.2.1 ⟨i,hi⟩
    simp only [Fin.getElem_fin] at hh
    simpa only [baseline_literal_layout.2.2] using ⟨hh.1,hh.2.1⟩
  · intro a ha
    rw [entryPc_model] at ha
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem ha
    subst a
    have hh := baseline_submission_finite.2.2.1 ⟨i,hi⟩
    simp only [Fin.getElem_fin] at hh
    exact hh.2.2.1
  · intro a ha
    rw [entryPc_model] at ha
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem ha
    subst a
    have hh := baseline_submission_finite.2.2.1 ⟨i,hi⟩
    simp only [Fin.getElem_fin] at hh
    exact hh.2.2.2
  · intro rec hr
    change rec ∈ baselineMmio at hr
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem hr
    subst rec
    have hlt := (baseline_submission_finite.2.2.2 ⟨i,hi⟩).1
    simp only [Fin.getElem_fin] at hlt
    rw [program_model]
    exact baseline_native_program_byte ⟨baselineMmio[i].entryPc,
      by simpa only [baseline_literal_layout.2.1] using hlt⟩
  · intro rec hr
    change rec ∈ baselineMmio at hr
    obtain ⟨i,hi,heq⟩ := List.getElem_of_mem hr
    subst rec
    have h := (baseline_submission_finite.2.2.2 ⟨i,hi⟩).2
    simp only [Fin.getElem_fin] at h
    simpa only [baseline_literal_layout.2.2] using h
  · rw [hsize]; decide

end InitECandidate.Solver.FastEnv

/-! ## Section BootstrapCopyGuards -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

set_option autoImplicit false

namespace InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitE InitECandidate.Proofs InitECandidate.Solver.FastEnv
open InitE
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy InitECandidate.Proofs.BootstrapAsmComposition

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The fixed compiler dispatch list is above everybootstrapinstruction. -/
theorem baseline_ffi_entries_above_boot :
    baselineEntryPcs.all (fun pc => decide (0x80001030 ≤ pc.toNat)) = true := by
  decide_cbv

/-- Any instruction within the208byte bootstrap code region is ordinary
execution rather than an FFI dispatch entry. -/
theorem bootstrap_ffi_disjoint (s : AsmState 64) (length : Nat)
    (lower : initialPc ≤ s.pc.toNat)
    (upper : s.pc.toNat + length ≤ initialPc + 208) :
    ffiEntryPcsDisjoint baselineMachineConfig s length := by
  intro address both
  obtain ⟨member, offset, ho, equation⟩ := both
  have member' : address ∈ baselineEntryPcs := member
  have far := of_decide_eq_true ((List.all_eq_true.mp baseline_ffi_entries_above_boot) address member')
  rw [equation] at far
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show offset < 2 ^ 64 by norm_num [initialPc] at upper; omega),
    Nat.mod_eq_of_lt (show s.pc.toNat + offset < 2 ^ 64 by norm_num [initialPc] at upper; omega)] at far
  norm_num [initialPc] at lower upper
  omega

private theorem loop_instruction_length (stage : Nat) (hs : stage < 5) :
    (riscvEnc loopBody[stage]).length = 4 := by interval_cases stage <;> decide +revert

theorem copyBody_guard_step (k stage : Nat) (hk : k < 4606) (hs : stage < 5) :
    baselineMachineConfig.progAddresses = (bodyState (copyState k) stage).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (bodyState (copyState k) stage)
      (riscvEnc loopBody[stage]).length := by
  refine ⟨?_, ?_⟩
  · rw [(bodyState_config _ _ (by omega)).2.1, (copyState_fields k).2.1]
    rfl
  · rw [loop_instruction_length stage hs]
    apply bootstrap_ffi_disjoint
    · rw [bodyState_pc _ _ hs, copyState_pc k (by omega)]
      simp only [hk, reduceIte]
      change initialPc ≤ (BitVec.ofNat 64 (0x80000018) + BitVec.ofNat 64 (4 * stage)).toNat
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      norm_num [initialPc]; omega
    · rw [bodyState_pc _ _ hs, copyState_pc k (by omega)]
      simp only [hk, reduceIte]
      change (BitVec.ofNat 64 (0x80000018) + BitVec.ofNat 64 (4 * stage)).toNat + 4 ≤ initialPc + 208
      rw [← BitVec.ofNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      norm_num [initialPc]; omega

theorem copyBody_guards (k : Nat) (hk : k < 4606) :
    EvaluatorGuards baselineMachineConfig loopBody (copyState k) := by
  have h0 := copyBody_guard_step k 0 hk (by decide)
  have h1 := copyBody_guard_step k 1 hk (by decide)
  have h2 := copyBody_guard_step k 2 hk (by decide)
  have h3 := copyBody_guard_step k 3 hk (by decide)
  have h4 := copyBody_guard_step k 4 hk (by decide)
  simpa [EvaluatorGuards, loopBody, bodyState, run] using
    And.intro h0.1 (And.intro h0.2
      (And.intro h1.1 (And.intro h1.2
        (And.intro h2.1 (And.intro h2.2
          (And.intro h3.1 (And.intro h3.2
            (And.intro h4.1 (And.intro h4.2 True.intro)))))))))

private theorem guards_append (left right : List (HolAsm 64)) (s : AsmState 64) :
    EvaluatorGuards baselineMachineConfig (left ++ right) s ↔
      EvaluatorGuards baselineMachineConfig left s ∧
        EvaluatorGuards baselineMachineConfig right (run left s) := by
  induction left generalizing s with
  | nil => simp [EvaluatorGuards, run]
  | cons i rest ih => simp only [List.cons_append, EvaluatorGuards, run, ih, and_assoc]

theorem copyLoop_guards_from (count start : Nat) (bound : start + count ≤ 4606) :
    EvaluatorGuards baselineMachineConfig (loopProgram count) (copyState start) := by
  induction count generalizing start with
  | zero => trivial
  | succ count ih =>
    have program : loopProgram (count + 1) = loopBody ++ loopProgram count := by
      simp [loopProgram, List.replicate_succ]
    rw [program, guards_append]
    refine ⟨copyBody_guards start (by omega), ?_⟩
    have next : run loopBody (copyState start) = copyState (start + 1) := by
      simp only [copyState, Function.iterate_succ_apply']
    rw [next]
    exact ih (start + 1) (by omega)

theorem copyLoop_guards :
    EvaluatorGuards baselineMachineConfig (loopProgram 4606) copyEntryAsm :=
  copyLoop_guards_from 4606 0 (by decide)

end InitECandidate.Solver.FastEnv.BootstrapCopyGuards

/-! ## Section BootstrapTailChecks -/

set_option maxRecDepth 32768
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitE InitECandidate.Proofs InitECandidate.Solver.FastEnv InitECandidate.Proofs.BootstrapStraightLine InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitE
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.RiscV.TargetProof
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Proofs.BootstrapAsmComposition

private theorem input_pc : (copyState 4606).pc = 0x8000002c := by
  simpa only [show ¬ (4606 < 4606) by omega, if_false] using copyState_pc 4606 (Nat.le_refl _)

/-- All bytes written by the tail lie in available RAM. -/
theorem tail_store_domain (base : Nat)
    (region : (initDataRam ≤ base ∧ base+8 ≤ initDataRam+24) ∨
      (sourceBase ≤ base ∧ base+8 ≤ sourceBase+40)) (j : Nat) (hj : j < 8) :
    bootstrapDomain (BitVec.ofNat 64 base + BitVec.ofNat 64 j) := by
  have numbers : (BitVec.ofNat 64 base + BitVec.ofNat 64 j).toNat = base+j := by
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    simp only [initDataRam, sourceBase] at region
    omega
  constructor
  · constructor
    · right
      simp only [numbers, ramStart, ramEnd, ramSize, initDataRam, sourceBase] at region ⊢
      omega
    · unfold machineSharedDomain
      simp only [numbers, inputStart, inputEnd, inputSize, outputSize, outputStart,
        outputEnd, initDataRam, sourceBase] at region ⊢
      omega
  · intro i hi equal
    have rightNat : (BitVec.ofNat 64 nativePc - BitVec.ofNat 64 (16*(i+1))).toNat < initDataRam := by
      rw [BitVec.toNat_sub_of_le (by
        change (BitVec.ofNat 64 (16*(i+1))).toNat ≤ (BitVec.ofNat 64 nativePc).toNat
        simp only [BitVec.toNat_ofNat, nativePc, Nat.mod_eq_of_lt (by omega : 16*(i+1) < 2^64)]
        omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by norm_num [nativePc]), Nat.mod_eq_of_lt (by omega : 16*(i+1) < 2^64)]
      norm_num [nativePc, initDataRam]; omega
    have same := congrArg BitVec.toNat equal
    rw [numbers] at same
    simp only [initDataRam, sourceBase] at region rightNat
    omega

private theorem asm_store_failed {w : Nat} [NeZero w] (s : AsmState w)
    (r b : Nat) (off next : BitVec w) :
    (asmUpd (.inst (.mem .store r (.addr b off))) next s).failed =
      (memStore (w/8) r (.addr b off) s).failed := rfl

private theorem after_store_failed (s : AsmState 64) (r b : Nat) (off : BitVec 64) :
    (after s (.inst (.mem .store r (.addr b off)))).failed =
      (memStore 8 r (.addr b off) s).failed := asm_store_failed s r b off _

private theorem store_success (s : AsmState 64) (r b : Nat) (off : BitVec 64)
    (little : s.be = false) (failed : s.failed = false)
    (domain : s.memDomain = bootstrapDomain) (base : Nat)
    (address : s.regs b + off = BitVec.ofNat 64 base)
    (region : (initDataRam ≤ base ∧ base+8 ≤ initDataRam+24) ∨
      (sourceBase ≤ base ∧ base+8 ≤ sourceBase+40))
    (aligned : holAligned 3 (BitVec.ofNat 64 base) = true) :
    (after s (.inst (.mem .store r (.addr b off)))).failed = false := by
  rw [after_store_failed]
  apply (source_memstore_success 8 r (.addr b off) s).mpr
  simp only [little, Bool.false_eq_true, reduceIte, addrHOL, readReg,
    address, domain, source_memory_domain_little,
    show holLOG2 8 = 3 by simp [holLOG2_eq_log2]]
  exact ⟨failed, tail_store_domain base region, aligned⟩

private theorem store_frame (s : AsmState 64) (r b : Nat) (off : BitVec 64)
    (little : s.be = false) (base : Nat)
    (address : s.regs b + off = BitVec.ofNat 64 base)
    (region : (initDataRam ≤ base ∧ base+8 ≤ initDataRam+24) ∨
      (sourceBase ≤ base ∧ base+8 ≤ sourceBase+40))
    (x : BitVec 64) (lo : initialPc ≤ x.toNat) (hi : x.toNat < initialPc+208) :
    (after s (.inst (.mem .store r (.addr b off)))).mem x = s.mem x := by
  rw [after_store_mem, little, if_neg Bool.false_ne_true, address]
  apply wmwMem_other
  intro j hj equal
  have numbers := congrArg BitVec.toNat equal
  simp only [stepAddr, Bool.false_eq_true, reduceIte, BitVec.toNat_add, BitVec.toNat_ofNat] at numbers
  rw [Nat.mod_eq_of_lt (by simp only [initDataRam,sourceBase] at region; omega : base < 2^64),
    Nat.mod_eq_of_lt (by omega : j < 2^64),
    Nat.mod_eq_of_lt (by simp only [initDataRam,sourceBase] at region; omega : base+j < 2^64)] at numbers
  simp only [initialPc,initDataRam,sourceBase] at lo hi region
  omega

private theorem after_loc_failed (s : AsmState 64) (r : Nat) (off : BitVec 64) :
    (after s (.loc r off)).failed = s.failed := rfl
private theorem after_const_failed (s : AsmState 64) (r : Nat) (v : BitVec 64) :
    (after s (.inst (.const r v))).failed = s.failed := rfl
private theorem after_shift_failed (s : AsmState 64) (r : Nat) (v : BitVec 64) :
    (after s (.inst (.arith (.shift .lsl r r (.imm v))))).failed = s.failed := rfl
private theorem after_jump_failed (s : AsmState 64) (v : BitVec 64) :
    (after s (.jump v)).failed = s.failed := rfl

private theorem tailState0_eq (s : AsmState 64) : tailState0 s = s := rfl

private theorem tailState0_success : (tailState0 (copyState 4606)).failed = false :=
  (congrArg AsmState.failed (tailState0_eq (copyState 4606))).trans
    (copyState_success 4606 (Nat.le_refl _))

private theorem tailState0_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState0 (copyState 4606)).mem x = initialMemory x := by
  have prior : (copyState 4606).mem x = initialMemory x := by
    apply copyState_frame 4606 (Nat.le_refl _) x
    intro word hw byte hb eq
    have numbers := congrArg BitVec.toNat eq
    rw [wordAddress_toNat _ _ _ (by simp; omega)] at numbers
    rw [show (0xa0020000 : BitVec 64).toNat = 0xa0020000 by decide] at numbers
    norm_num [initialPc] at lo hi numbers
    omega

  exact (congrArg (fun t : AsmState 64 => t.mem x) (tailState0_eq (copyState 4606))).trans prior

private theorem tailState1_success : (tailState1 (copyState 4606)).failed = false :=
  (after_loc_failed (tailState0 (copyState 4606)) _ _).trans tailState0_success

private theorem tailState1_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState1 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_loc_mem (tailState0 (copyState 4606)) _ _) x).trans (tailState0_frame x lo hi)

private theorem tailState2_success : (tailState2 (copyState 4606)).failed = false :=
  (after_const_failed (tailState1 (copyState 4606)) _ _).trans tailState1_success

private theorem tailState2_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState2 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_const_mem (tailState1 (copyState 4606)) _ _) x).trans (tailState1_frame x lo hi)

private theorem tailState3_success : (tailState3 (copyState 4606)).failed = false :=
  (after_shift_failed (tailState2 (copyState 4606)) _ _).trans tailState2_success

private theorem tailState3_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState3 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_shift_mem (tailState2 (copyState 4606)) _ _) x).trans (tailState2_frame x lo hi)

private theorem tailState4_success : (tailState4 (copyState 4606)).failed = false :=
  store_success (tailState3 (copyState 4606)) 6 5 0 ((tailState3_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) tailState3_success ((tailState3_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) 2684485632 (by rw [(tailState3_control (copyState 4606) input_pc).2.1]; decide) (by decide) (by decide)

private theorem tailState4_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState4 (copyState 4606)).mem x = initialMemory x :=
  (store_frame (tailState3 (copyState 4606)) 6 5 0 ((tailState3_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) 2684485632 (by rw [(tailState3_control (copyState 4606) input_pc).2.1]; decide) (by decide) x lo hi).trans (tailState3_frame x lo hi)

private theorem tailState5_success : (tailState5 (copyState 4606)).failed = false :=
  (after_loc_failed (tailState4 (copyState 4606)) _ _).trans tailState4_success

private theorem tailState5_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState5 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_loc_mem (tailState4 (copyState 4606)) _ _) x).trans (tailState4_frame x lo hi)

private theorem tailState6_success : (tailState6 (copyState 4606)).failed = false :=
  (after_const_failed (tailState5 (copyState 4606)) _ _).trans tailState5_success

private theorem tailState6_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState6 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_const_mem (tailState5 (copyState 4606)) _ _) x).trans (tailState5_frame x lo hi)

private theorem tailState7_success : (tailState7 (copyState 4606)).failed = false :=
  (after_shift_failed (tailState6 (copyState 4606)) _ _).trans tailState6_success

private theorem tailState7_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState7 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_shift_mem (tailState6 (copyState 4606)) _ _) x).trans (tailState6_frame x lo hi)

private theorem tailState8_success : (tailState8 (copyState 4606)).failed = false :=
  store_success (tailState7 (copyState 4606)) 6 5 0 ((tailState7_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) tailState7_success ((tailState7_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) 2684485640 (by rw [(tailState7_control (copyState 4606) input_pc).2.1]; decide) (by decide) (by decide)

private theorem tailState8_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState8 (copyState 4606)).mem x = initialMemory x :=
  (store_frame (tailState7 (copyState 4606)) 6 5 0 ((tailState7_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) 2684485640 (by rw [(tailState7_control (copyState 4606) input_pc).2.1]; decide) (by decide) x lo hi).trans (tailState7_frame x lo hi)

private theorem tailState9_success : (tailState9 (copyState 4606)).failed = false :=
  (after_loc_failed (tailState8 (copyState 4606)) _ _).trans tailState8_success

private theorem tailState9_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState9 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_loc_mem (tailState8 (copyState 4606)) _ _) x).trans (tailState8_frame x lo hi)

private theorem tailState10_success : (tailState10 (copyState 4606)).failed = false :=
  (after_const_failed (tailState9 (copyState 4606)) _ _).trans tailState9_success

private theorem tailState10_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState10 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_const_mem (tailState9 (copyState 4606)) _ _) x).trans (tailState9_frame x lo hi)

private theorem tailState11_success : (tailState11 (copyState 4606)).failed = false :=
  (after_shift_failed (tailState10 (copyState 4606)) _ _).trans tailState10_success

private theorem tailState11_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState11 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_shift_mem (tailState10 (copyState 4606)) _ _) x).trans (tailState10_frame x lo hi)

private theorem tailState12_success : (tailState12 (copyState 4606)).failed = false :=
  store_success (tailState11 (copyState 4606)) 6 5 0 ((tailState11_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) tailState11_success ((tailState11_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) 2684485648 (by rw [(tailState11_control (copyState 4606) input_pc).2.1]; decide) (by decide) (by decide)

private theorem tailState12_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState12 (copyState 4606)).mem x = initialMemory x :=
  (store_frame (tailState11 (copyState 4606)) 6 5 0 ((tailState11_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) 2684485648 (by rw [(tailState11_control (copyState 4606) input_pc).2.1]; decide) (by decide) x lo hi).trans (tailState11_frame x lo hi)

private theorem tailState13_success : (tailState13 (copyState 4606)).failed = false :=
  (after_const_failed (tailState12 (copyState 4606)) _ _).trans tailState12_success

private theorem tailState13_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState13 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_const_mem (tailState12 (copyState 4606)) _ _) x).trans (tailState12_frame x lo hi)

private theorem tailState14_success : (tailState14 (copyState 4606)).failed = false :=
  (after_shift_failed (tailState13 (copyState 4606)) _ _).trans tailState13_success

private theorem tailState14_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState14 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_shift_mem (tailState13 (copyState 4606)) _ _) x).trans (tailState13_frame x lo hi)

private theorem tailState15_success : (tailState15 (copyState 4606)).failed = false :=
  (after_loc_failed (tailState14 (copyState 4606)) _ _).trans tailState14_success

private theorem tailState15_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState15 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_loc_mem (tailState14 (copyState 4606)) _ _) x).trans (tailState14_frame x lo hi)

private theorem tailState16_success : (tailState16 (copyState 4606)).failed = false :=
  store_success (tailState15 (copyState 4606)) 6 5 0 ((tailState15_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) tailState15_success ((tailState15_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) 2701131776 (by rw [(tailState15_control (copyState 4606) input_pc).2.1]; decide) (by decide) (by decide)

private theorem tailState16_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState16 (copyState 4606)).mem x = initialMemory x :=
  (store_frame (tailState15 (copyState 4606)) 6 5 0 ((tailState15_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) 2701131776 (by rw [(tailState15_control (copyState 4606) input_pc).2.1]; decide) (by decide) x lo hi).trans (tailState15_frame x lo hi)

private theorem tailState17_success : (tailState17 (copyState 4606)).failed = false :=
  (after_loc_failed (tailState16 (copyState 4606)) _ _).trans tailState16_success

private theorem tailState17_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState17 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_loc_mem (tailState16 (copyState 4606)) _ _) x).trans (tailState16_frame x lo hi)

private theorem tailState18_success : (tailState18 (copyState 4606)).failed = false :=
  store_success (tailState17 (copyState 4606)) 6 5 8 ((tailState17_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) tailState17_success ((tailState17_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) 2701131784 (by rw [(tailState17_control (copyState 4606) input_pc).2.1]; decide) (by decide) (by decide)

private theorem tailState18_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState18 (copyState 4606)).mem x = initialMemory x :=
  (store_frame (tailState17 (copyState 4606)) 6 5 8 ((tailState17_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) 2701131784 (by rw [(tailState17_control (copyState 4606) input_pc).2.1]; decide) (by decide) x lo hi).trans (tailState17_frame x lo hi)

private theorem tailState19_success : (tailState19 (copyState 4606)).failed = false :=
  (after_loc_failed (tailState18 (copyState 4606)) _ _).trans tailState18_success

private theorem tailState19_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState19 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_loc_mem (tailState18 (copyState 4606)) _ _) x).trans (tailState18_frame x lo hi)

private theorem tailState20_success : (tailState20 (copyState 4606)).failed = false :=
  store_success (tailState19 (copyState 4606)) 6 5 16 ((tailState19_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) tailState19_success ((tailState19_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) 2701131792 (by rw [(tailState19_control (copyState 4606) input_pc).2.1]; decide) (by decide) (by decide)

private theorem tailState20_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState20 (copyState 4606)).mem x = initialMemory x :=
  (store_frame (tailState19 (copyState 4606)) 6 5 16 ((tailState19_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) 2701131792 (by rw [(tailState19_control (copyState 4606) input_pc).2.1]; decide) (by decide) x lo hi).trans (tailState19_frame x lo hi)

private theorem tailState21_success : (tailState21 (copyState 4606)).failed = false :=
  (after_loc_failed (tailState20 (copyState 4606)) _ _).trans tailState20_success

private theorem tailState21_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState21 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_loc_mem (tailState20 (copyState 4606)) _ _) x).trans (tailState20_frame x lo hi)

private theorem tailState22_success : (tailState22 (copyState 4606)).failed = false :=
  store_success (tailState21 (copyState 4606)) 6 5 24 ((tailState21_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) tailState21_success ((tailState21_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) 2701131800 (by rw [(tailState21_control (copyState 4606) input_pc).2.1]; decide) (by decide) (by decide)

private theorem tailState22_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState22 (copyState 4606)).mem x = initialMemory x :=
  (store_frame (tailState21 (copyState 4606)) 6 5 24 ((tailState21_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) 2701131800 (by rw [(tailState21_control (copyState 4606) input_pc).2.1]; decide) (by decide) x lo hi).trans (tailState21_frame x lo hi)

private theorem tailState23_success : (tailState23 (copyState 4606)).failed = false :=
  (after_loc_failed (tailState22 (copyState 4606)) _ _).trans tailState22_success

private theorem tailState23_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState23 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_loc_mem (tailState22 (copyState 4606)) _ _) x).trans (tailState22_frame x lo hi)

private theorem tailState24_success : (tailState24 (copyState 4606)).failed = false :=
  store_success (tailState23 (copyState 4606)) 6 5 32 ((tailState23_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) tailState23_success ((tailState23_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) 2701131808 (by rw [(tailState23_control (copyState 4606) input_pc).2.1]; decide) (by decide) (by decide)

private theorem tailState24_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState24 (copyState 4606)).mem x = initialMemory x :=
  (store_frame (tailState23 (copyState 4606)) 6 5 32 ((tailState23_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1) 2701131808 (by rw [(tailState23_control (copyState 4606) input_pc).2.1]; decide) (by decide) x lo hi).trans (tailState23_frame x lo hi)

private theorem tailState25_success : (tailState25 (copyState 4606)).failed = false :=
  (after_const_failed (tailState24 (copyState 4606)) _ _).trans tailState24_success

private theorem tailState25_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState25 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_const_mem (tailState24 (copyState 4606)) _ _) x).trans (tailState24_frame x lo hi)

private theorem tailState26_success : (tailState26 (copyState 4606)).failed = false :=
  (after_shift_failed (tailState25 (copyState 4606)) _ _).trans tailState25_success

private theorem tailState26_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState26 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_shift_mem (tailState25 (copyState 4606)) _ _) x).trans (tailState25_frame x lo hi)

private theorem tailState27_success : (tailState27 (copyState 4606)).failed = false :=
  (after_const_failed (tailState26 (copyState 4606)) _ _).trans tailState26_success

private theorem tailState27_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState27 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_const_mem (tailState26 (copyState 4606)) _ _) x).trans (tailState26_frame x lo hi)

private theorem tailState28_success : (tailState28 (copyState 4606)).failed = false :=
  (after_shift_failed (tailState27 (copyState 4606)) _ _).trans tailState27_success

private theorem tailState28_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState28 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_shift_mem (tailState27 (copyState 4606)) _ _) x).trans (tailState27_frame x lo hi)

private theorem tailState29_success : (tailState29 (copyState 4606)).failed = false :=
  (after_const_failed (tailState28 (copyState 4606)) _ _).trans tailState28_success

private theorem tailState29_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState29 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_const_mem (tailState28 (copyState 4606)) _ _) x).trans (tailState28_frame x lo hi)

private theorem tailState30_success : (tailState30 (copyState 4606)).failed = false :=
  (after_shift_failed (tailState29 (copyState 4606)) _ _).trans tailState29_success

private theorem tailState30_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState30 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_shift_mem (tailState29 (copyState 4606)) _ _) x).trans (tailState29_frame x lo hi)

private theorem tailState31_success : (tailState31 (copyState 4606)).failed = false :=
  (after_loc_failed (tailState30 (copyState 4606)) _ _).trans tailState30_success

private theorem tailState31_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState31 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_loc_mem (tailState30 (copyState 4606)) _ _) x).trans (tailState30_frame x lo hi)

private theorem tailState32_success : (tailState32 (copyState 4606)).failed = false :=
  (after_jump_failed (tailState31 (copyState 4606)) _).trans tailState31_success

private theorem tailState32_frame (x : BitVec 64) (lo : initialPc ≤ x.toNat)
    (hi : x.toNat < initialPc+208) :
    (tailState32 (copyState 4606)).mem x = initialMemory x :=
  (congrFun (after_jump_mem (tailState31 (copyState 4606)) _) x).trans (tailState31_frame x lo hi)

private theorem zero_pc : (tailState0 (copyState 4606)).pc = 0x8000002c :=
  (congrArg AsmState.pc (tailState0_eq (copyState 4606))).trans input_pc

private theorem zero_memDomain : (tailState0 (copyState 4606)).memDomain = bootstrapDomain :=
  (congrArg AsmState.memDomain (tailState0_eq (copyState 4606))).trans (copyState_fields 4606).2.1

private theorem zero_be : (tailState0 (copyState 4606)).be = false :=
  (congrArg AsmState.be (tailState0_eq (copyState 4606))).trans (copyState_fields 4606).1

private theorem zero_lr : (tailState0 (copyState 4606)).lr = 1 :=
  (congrArg AsmState.lr (tailState0_eq (copyState 4606))).trans (copyState_fields 4606).2.2.2.1

private theorem zero_align : (tailState0 (copyState 4606)).align = 2 :=
  (congrArg AsmState.align (tailState0_eq (copyState 4606))).trans (copyState_fields 4606).2.2.2.2

private theorem checked_step_to (s t : AsmState 64) (i : HolAsm 64)
    (endpoint : after s i = t)
    (bytes : bytesInMemoryHOL s.pc (riscvEnc i) s.mem s.memDomain)
    (link : s.lr = 1) (endian : s.be = false) (alignment : s.align = 2)
    (nonfailed : ¬ t.failed) (admitted : asmOkExact i riscvConfig = true) :
    asmStep riscvConfig s i t := ⟨bytes, link, endian, alignment, endpoint, nonfailed, admitted⟩

private theorem installed_tail_instruction (state : AsmState 64) (pc : Nat)
    (instruction : HolAsm 64) (member : (pc,instruction) ∈ bootstrapBlocks)
    (position : state.pc = BitVec.ofNat 64 pc) (domain : state.memDomain = bootstrapDomain)
    (frame : ∀ x, initialPc ≤ x.toNat → x.toNat < initialPc+208 → state.mem x = initialMemory x)
    (lo : initialPc ≤ pc) (hi : pc+(riscvEnc instruction).length ≤ initialPc+208) :
    bytesInMemoryHOL state.pc (riscvEnc instruction) state.mem state.memDomain := by
  rw [position, domain]
  apply bytesInMemory_changeMem _ _ initialMemory _ bootstrapDomain
  refine ⟨block_bytes (pc,instruction) member, ?_⟩
  intro offset ho
  apply Eq.symm
  apply frame
  all_goals
    rw [← BitVec.ofNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by norm_num [initialPc] at hi; omega : pc+offset < 2^64)]
    omega

private theorem tail_step0 : asmStep riscvConfig (tailState0 (copyState 4606)) (bootLoc 5 0x8000002c initDataRam) (tailState1 (copyState 4606)) := by
  apply checked_step_to (tailState0 (copyState 4606)) (tailState1 (copyState 4606)) (bootLoc 5 0x8000002c initDataRam) rfl
  · exact installed_tail_instruction (tailState0 (copyState 4606)) 2147483692 (bootLoc 5 0x8000002c initDataRam)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      (zero_pc) (zero_memDomain) tailState0_frame (by decide) (by decide)
  · exact zero_lr
  · exact zero_be
  · exact zero_align
  · simpa only [Bool.not_eq_true] using tailState1_success
  · decide

private theorem tail_guard0 : baselineMachineConfig.progAddresses = (tailState0 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState0 (copyState 4606)) (riscvEnc (bootLoc 5 0x8000002c initDataRam)).length := by
  refine ⟨(zero_memDomain).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [(zero_pc)]; decide
  · rw [(zero_pc)]; decide

private theorem tail_step1 : asmStep riscvConfig (tailState1 (copyState 4606)) (bootConst 6 161) (tailState2 (copyState 4606)) := by
  apply checked_step_to (tailState1 (copyState 4606)) (tailState2 (copyState 4606)) (bootConst 6 161) rfl
  · exact installed_tail_instruction (tailState1 (copyState 4606)) 2147483700 (bootConst 6 161)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState1_control (copyState 4606) input_pc).1) ((tailState1_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState1_frame (by decide) (by decide)
  · exact (tailState1_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState1_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState1_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState2_success
  · decide

private theorem tail_guard1 : baselineMachineConfig.progAddresses = (tailState1 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState1 (copyState 4606)) (riscvEnc (bootConst 6 161)).length := by
  refine ⟨((tailState1_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState1_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState1_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step2 : asmStep riscvConfig (tailState2 (copyState 4606)) (bootShift 6 24) (tailState3 (copyState 4606)) := by
  apply checked_step_to (tailState2 (copyState 4606)) (tailState3 (copyState 4606)) (bootShift 6 24) rfl
  · exact installed_tail_instruction (tailState2 (copyState 4606)) 2147483704 (bootShift 6 24)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState2_control (copyState 4606) input_pc).1) ((tailState2_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState2_frame (by decide) (by decide)
  · exact (tailState2_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState2_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState2_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState3_success
  · decide

private theorem tail_guard2 : baselineMachineConfig.progAddresses = (tailState2 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState2 (copyState 4606)) (riscvEnc (bootShift 6 24)).length := by
  refine ⟨((tailState2_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState2_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState2_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step3 : asmStep riscvConfig (tailState3 (copyState 4606)) (bootStore 6 5 0) (tailState4 (copyState 4606)) := by
  apply checked_step_to (tailState3 (copyState 4606)) (tailState4 (copyState 4606)) (bootStore 6 5 0) rfl
  · exact installed_tail_instruction (tailState3 (copyState 4606)) 2147483708 (bootStore 6 5 0)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState3_control (copyState 4606) input_pc).1) ((tailState3_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState3_frame (by decide) (by decide)
  · exact (tailState3_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState3_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState3_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState4_success
  · decide

private theorem tail_guard3 : baselineMachineConfig.progAddresses = (tailState3 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState3 (copyState 4606)) (riscvEnc (bootStore 6 5 0)).length := by
  refine ⟨((tailState3_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState3_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState3_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step4 : asmStep riscvConfig (tailState4 (copyState 4606)) (bootLoc 5 0x80000040 (initDataRam+8)) (tailState5 (copyState 4606)) := by
  apply checked_step_to (tailState4 (copyState 4606)) (tailState5 (copyState 4606)) (bootLoc 5 0x80000040 (initDataRam+8)) rfl
  · exact installed_tail_instruction (tailState4 (copyState 4606)) 2147483712 (bootLoc 5 0x80000040 (initDataRam+8))
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState4_control (copyState 4606) input_pc).1) ((tailState4_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState4_frame (by decide) (by decide)
  · exact (tailState4_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState4_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState4_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState5_success
  · decide

private theorem tail_guard4 : baselineMachineConfig.progAddresses = (tailState4 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState4 (copyState 4606)) (riscvEnc (bootLoc 5 0x80000040 (initDataRam+8))).length := by
  refine ⟨((tailState4_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState4_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState4_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step5 : asmStep riscvConfig (tailState5 (copyState 4606)) (bootConst 6 2015) (tailState6 (copyState 4606)) := by
  apply checked_step_to (tailState5 (copyState 4606)) (tailState6 (copyState 4606)) (bootConst 6 2015) rfl
  · exact installed_tail_instruction (tailState5 (copyState 4606)) 2147483720 (bootConst 6 2015)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState5_control (copyState 4606) input_pc).1) ((tailState5_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState5_frame (by decide) (by decide)
  · exact (tailState5_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState5_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState5_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState6_success
  · decide

private theorem tail_guard5 : baselineMachineConfig.progAddresses = (tailState5 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState5 (copyState 4606)) (riscvEnc (bootConst 6 2015)).length := by
  refine ⟨((tailState5_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState5_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState5_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step6 : asmStep riscvConfig (tailState6 (copyState 4606)) (bootShift 6 24) (tailState7 (copyState 4606)) := by
  apply checked_step_to (tailState6 (copyState 4606)) (tailState7 (copyState 4606)) (bootShift 6 24) rfl
  · exact installed_tail_instruction (tailState6 (copyState 4606)) 2147483724 (bootShift 6 24)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState6_control (copyState 4606) input_pc).1) ((tailState6_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState6_frame (by decide) (by decide)
  · exact (tailState6_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState6_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState6_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState7_success
  · decide

private theorem tail_guard6 : baselineMachineConfig.progAddresses = (tailState6 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState6 (copyState 4606)) (riscvEnc (bootShift 6 24)).length := by
  refine ⟨((tailState6_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState6_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState6_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step7 : asmStep riscvConfig (tailState7 (copyState 4606)) (bootStore 6 5 0) (tailState8 (copyState 4606)) := by
  apply checked_step_to (tailState7 (copyState 4606)) (tailState8 (copyState 4606)) (bootStore 6 5 0) rfl
  · exact installed_tail_instruction (tailState7 (copyState 4606)) 2147483728 (bootStore 6 5 0)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState7_control (copyState 4606) input_pc).1) ((tailState7_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState7_frame (by decide) (by decide)
  · exact (tailState7_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState7_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState7_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState8_success
  · decide

private theorem tail_guard7 : baselineMachineConfig.progAddresses = (tailState7 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState7 (copyState 4606)) (riscvEnc (bootStore 6 5 0)).length := by
  refine ⟨((tailState7_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState7_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState7_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step8 : asmStep riscvConfig (tailState8 (copyState 4606)) (bootLoc 5 0x80000054 (initDataRam+16)) (tailState9 (copyState 4606)) := by
  apply checked_step_to (tailState8 (copyState 4606)) (tailState9 (copyState 4606)) (bootLoc 5 0x80000054 (initDataRam+16)) rfl
  · exact installed_tail_instruction (tailState8 (copyState 4606)) 2147483732 (bootLoc 5 0x80000054 (initDataRam+16))
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState8_control (copyState 4606) input_pc).1) ((tailState8_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState8_frame (by decide) (by decide)
  · exact (tailState8_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState8_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState8_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState9_success
  · decide

private theorem tail_guard8 : baselineMachineConfig.progAddresses = (tailState8 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState8 (copyState 4606)) (riscvEnc (bootLoc 5 0x80000054 (initDataRam+16))).length := by
  refine ⟨((tailState8_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState8_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState8_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step9 : asmStep riscvConfig (tailState9 (copyState 4606)) (bootConst 6 63) (tailState10 (copyState 4606)) := by
  apply checked_step_to (tailState9 (copyState 4606)) (tailState10 (copyState 4606)) (bootConst 6 63) rfl
  · exact installed_tail_instruction (tailState9 (copyState 4606)) 2147483740 (bootConst 6 63)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState9_control (copyState 4606) input_pc).1) ((tailState9_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState9_frame (by decide) (by decide)
  · exact (tailState9_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState9_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState9_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState10_success
  · decide

private theorem tail_guard9 : baselineMachineConfig.progAddresses = (tailState9 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState9 (copyState 4606)) (riscvEnc (bootConst 6 63)).length := by
  refine ⟨((tailState9_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState9_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState9_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step10 : asmStep riscvConfig (tailState10 (copyState 4606)) (bootShift 6 29) (tailState11 (copyState 4606)) := by
  apply checked_step_to (tailState10 (copyState 4606)) (tailState11 (copyState 4606)) (bootShift 6 29) rfl
  · exact installed_tail_instruction (tailState10 (copyState 4606)) 2147483744 (bootShift 6 29)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState10_control (copyState 4606) input_pc).1) ((tailState10_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState10_frame (by decide) (by decide)
  · exact (tailState10_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState10_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState10_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState11_success
  · decide

private theorem tail_guard10 : baselineMachineConfig.progAddresses = (tailState10 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState10 (copyState 4606)) (riscvEnc (bootShift 6 29)).length := by
  refine ⟨((tailState10_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState10_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState10_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step11 : asmStep riscvConfig (tailState11 (copyState 4606)) (bootStore 6 5 0) (tailState12 (copyState 4606)) := by
  apply checked_step_to (tailState11 (copyState 4606)) (tailState12 (copyState 4606)) (bootStore 6 5 0) rfl
  · exact installed_tail_instruction (tailState11 (copyState 4606)) 2147483748 (bootStore 6 5 0)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState11_control (copyState 4606) input_pc).1) ((tailState11_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState11_frame (by decide) (by decide)
  · exact (tailState11_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState11_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState11_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState12_success
  · decide

private theorem tail_guard11 : baselineMachineConfig.progAddresses = (tailState11 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState11 (copyState 4606)) (riscvEnc (bootStore 6 5 0)).length := by
  refine ⟨((tailState11_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState11_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState11_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step12 : asmStep riscvConfig (tailState12 (copyState 4606)) (bootConst 5 161) (tailState13 (copyState 4606)) := by
  apply checked_step_to (tailState12 (copyState 4606)) (tailState13 (copyState 4606)) (bootConst 5 161) rfl
  · exact installed_tail_instruction (tailState12 (copyState 4606)) 2147483752 (bootConst 5 161)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState12_control (copyState 4606) input_pc).1) ((tailState12_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState12_frame (by decide) (by decide)
  · exact (tailState12_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState12_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState12_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState13_success
  · decide

private theorem tail_guard12 : baselineMachineConfig.progAddresses = (tailState12 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState12 (copyState 4606)) (riscvEnc (bootConst 5 161)).length := by
  refine ⟨((tailState12_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState12_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState12_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step13 : asmStep riscvConfig (tailState13 (copyState 4606)) (bootShift 5 24) (tailState14 (copyState 4606)) := by
  apply checked_step_to (tailState13 (copyState 4606)) (tailState14 (copyState 4606)) (bootShift 5 24) rfl
  · exact installed_tail_instruction (tailState13 (copyState 4606)) 2147483756 (bootShift 5 24)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState13_control (copyState 4606) input_pc).1) ((tailState13_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState13_frame (by decide) (by decide)
  · exact (tailState13_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState13_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState13_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState14_success
  · decide

private theorem tail_guard13 : baselineMachineConfig.progAddresses = (tailState13 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState13 (copyState 4606)) (riscvEnc (bootShift 5 24)).length := by
  refine ⟨((tailState13_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState13_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState13_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step14 : asmStep riscvConfig (tailState14 (copyState 4606)) (bootLoc 6 0x80000070 (initDataRam+24)) (tailState15 (copyState 4606)) := by
  apply checked_step_to (tailState14 (copyState 4606)) (tailState15 (copyState 4606)) (bootLoc 6 0x80000070 (initDataRam+24)) rfl
  · exact installed_tail_instruction (tailState14 (copyState 4606)) 2147483760 (bootLoc 6 0x80000070 (initDataRam+24))
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState14_control (copyState 4606) input_pc).1) ((tailState14_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState14_frame (by decide) (by decide)
  · exact (tailState14_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState14_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState14_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState15_success
  · decide

private theorem tail_guard14 : baselineMachineConfig.progAddresses = (tailState14 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState14 (copyState 4606)) (riscvEnc (bootLoc 6 0x80000070 (initDataRam+24))).length := by
  refine ⟨((tailState14_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState14_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState14_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step15 : asmStep riscvConfig (tailState15 (copyState 4606)) (bootStore 6 5 0) (tailState16 (copyState 4606)) := by
  apply checked_step_to (tailState15 (copyState 4606)) (tailState16 (copyState 4606)) (bootStore 6 5 0) rfl
  · exact installed_tail_instruction (tailState15 (copyState 4606)) 2147483768 (bootStore 6 5 0)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState15_control (copyState 4606) input_pc).1) ((tailState15_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState15_frame (by decide) (by decide)
  · exact (tailState15_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState15_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState15_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState16_success
  · decide

private theorem tail_guard15 : baselineMachineConfig.progAddresses = (tailState15 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState15 (copyState 4606)) (riscvEnc (bootStore 6 5 0)).length := by
  refine ⟨((tailState15_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState15_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState15_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step16 : asmStep riscvConfig (tailState16 (copyState 4606)) (bootLoc 6 0x8000007c initDataEnd) (tailState17 (copyState 4606)) := by
  apply checked_step_to (tailState16 (copyState 4606)) (tailState17 (copyState 4606)) (bootLoc 6 0x8000007c initDataEnd) rfl
  · exact installed_tail_instruction (tailState16 (copyState 4606)) 2147483772 (bootLoc 6 0x8000007c initDataEnd)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState16_control (copyState 4606) input_pc).1) ((tailState16_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState16_frame (by decide) (by decide)
  · exact (tailState16_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState16_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState16_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState17_success
  · decide

private theorem tail_guard16 : baselineMachineConfig.progAddresses = (tailState16 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState16 (copyState 4606)) (riscvEnc (bootLoc 6 0x8000007c initDataEnd)).length := by
  refine ⟨((tailState16_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState16_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState16_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step17 : asmStep riscvConfig (tailState17 (copyState 4606)) (bootStore 6 5 8) (tailState18 (copyState 4606)) := by
  apply checked_step_to (tailState17 (copyState 4606)) (tailState18 (copyState 4606)) (bootStore 6 5 8) rfl
  · exact installed_tail_instruction (tailState17 (copyState 4606)) 2147483780 (bootStore 6 5 8)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState17_control (copyState 4606) input_pc).1) ((tailState17_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState17_frame (by decide) (by decide)
  · exact (tailState17_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState17_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState17_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState18_success
  · decide

private theorem tail_guard17 : baselineMachineConfig.progAddresses = (tailState17 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState17 (copyState 4606)) (riscvEnc (bootStore 6 5 8)).length := by
  refine ⟨((tailState17_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState17_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState17_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step18 : asmStep riscvConfig (tailState18 (copyState 4606)) (bootLoc 6 0x80000088 initDataEnd) (tailState19 (copyState 4606)) := by
  apply checked_step_to (tailState18 (copyState 4606)) (tailState19 (copyState 4606)) (bootLoc 6 0x80000088 initDataEnd) rfl
  · exact installed_tail_instruction (tailState18 (copyState 4606)) 2147483784 (bootLoc 6 0x80000088 initDataEnd)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState18_control (copyState 4606) input_pc).1) ((tailState18_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState18_frame (by decide) (by decide)
  · exact (tailState18_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState18_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState18_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState19_success
  · decide

private theorem tail_guard18 : baselineMachineConfig.progAddresses = (tailState18 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState18 (copyState 4606)) (riscvEnc (bootLoc 6 0x80000088 initDataEnd)).length := by
  refine ⟨((tailState18_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState18_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState18_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step19 : asmStep riscvConfig (tailState19 (copyState 4606)) (bootStore 6 5 16) (tailState20 (copyState 4606)) := by
  apply checked_step_to (tailState19 (copyState 4606)) (tailState20 (copyState 4606)) (bootStore 6 5 16) rfl
  · exact installed_tail_instruction (tailState19 (copyState 4606)) 2147483792 (bootStore 6 5 16)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState19_control (copyState 4606) input_pc).1) ((tailState19_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState19_frame (by decide) (by decide)
  · exact (tailState19_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState19_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState19_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState20_success
  · decide

private theorem tail_guard19 : baselineMachineConfig.progAddresses = (tailState19 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState19 (copyState 4606)) (riscvEnc (bootStore 6 5 16)).length := by
  refine ⟨((tailState19_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState19_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState19_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step20 : asmStep riscvConfig (tailState20 (copyState 4606)) (bootLoc 6 0x80000094 0x800f0134) (tailState21 (copyState 4606)) := by
  apply checked_step_to (tailState20 (copyState 4606)) (tailState21 (copyState 4606)) (bootLoc 6 0x80000094 0x800f0134) rfl
  · exact installed_tail_instruction (tailState20 (copyState 4606)) 2147483796 (bootLoc 6 0x80000094 0x800f0134)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState20_control (copyState 4606) input_pc).1) ((tailState20_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState20_frame (by decide) (by decide)
  · exact (tailState20_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState20_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState20_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState21_success
  · decide

private theorem tail_guard20 : baselineMachineConfig.progAddresses = (tailState20 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState20 (copyState 4606)) (riscvEnc (bootLoc 6 0x80000094 0x800f0134)).length := by
  refine ⟨((tailState20_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState20_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState20_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step21 : asmStep riscvConfig (tailState21 (copyState 4606)) (bootStore 6 5 24) (tailState22 (copyState 4606)) := by
  apply checked_step_to (tailState21 (copyState 4606)) (tailState22 (copyState 4606)) (bootStore 6 5 24) rfl
  · exact installed_tail_instruction (tailState21 (copyState 4606)) 2147483804 (bootStore 6 5 24)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState21_control (copyState 4606) input_pc).1) ((tailState21_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState21_frame (by decide) (by decide)
  · exact (tailState21_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState21_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState21_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState22_success
  · decide

private theorem tail_guard21 : baselineMachineConfig.progAddresses = (tailState21 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState21 (copyState 4606)) (riscvEnc (bootStore 6 5 24)).length := by
  refine ⟨((tailState21_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState21_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState21_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step22 : asmStep riscvConfig (tailState22 (copyState 4606)) (bootLoc 6 0x800000a0 0x800f1000) (tailState23 (copyState 4606)) := by
  apply checked_step_to (tailState22 (copyState 4606)) (tailState23 (copyState 4606)) (bootLoc 6 0x800000a0 0x800f1000) rfl
  · exact installed_tail_instruction (tailState22 (copyState 4606)) 2147483808 (bootLoc 6 0x800000a0 0x800f1000)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState22_control (copyState 4606) input_pc).1) ((tailState22_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState22_frame (by decide) (by decide)
  · exact (tailState22_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState22_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState22_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState23_success
  · decide

private theorem tail_guard22 : baselineMachineConfig.progAddresses = (tailState22 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState22 (copyState 4606)) (riscvEnc (bootLoc 6 0x800000a0 0x800f1000)).length := by
  refine ⟨((tailState22_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState22_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState22_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step23 : asmStep riscvConfig (tailState23 (copyState 4606)) (bootStore 6 5 32) (tailState24 (copyState 4606)) := by
  apply checked_step_to (tailState23 (copyState 4606)) (tailState24 (copyState 4606)) (bootStore 6 5 32) rfl
  · exact installed_tail_instruction (tailState23 (copyState 4606)) 2147483816 (bootStore 6 5 32)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState23_control (copyState 4606) input_pc).1) ((tailState23_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState23_frame (by decide) (by decide)
  · exact (tailState23_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState23_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState23_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState24_success
  · decide

private theorem tail_guard23 : baselineMachineConfig.progAddresses = (tailState23 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState23 (copyState 4606)) (riscvEnc (bootStore 6 5 32)).length := by
  refine ⟨((tailState23_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState23_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState23_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step24 : asmStep riscvConfig (tailState24 (copyState 4606)) (bootConst 11 161) (tailState25 (copyState 4606)) := by
  apply checked_step_to (tailState24 (copyState 4606)) (tailState25 (copyState 4606)) (bootConst 11 161) rfl
  · exact installed_tail_instruction (tailState24 (copyState 4606)) 2147483820 (bootConst 11 161)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState24_control (copyState 4606) input_pc).1) ((tailState24_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState24_frame (by decide) (by decide)
  · exact (tailState24_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState24_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState24_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState25_success
  · decide

private theorem tail_guard24 : baselineMachineConfig.progAddresses = (tailState24 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState24 (copyState 4606)) (riscvEnc (bootConst 11 161)).length := by
  refine ⟨((tailState24_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState24_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState24_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step25 : asmStep riscvConfig (tailState25 (copyState 4606)) (bootShift 11 24) (tailState26 (copyState 4606)) := by
  apply checked_step_to (tailState25 (copyState 4606)) (tailState26 (copyState 4606)) (bootShift 11 24) rfl
  · exact installed_tail_instruction (tailState25 (copyState 4606)) 2147483824 (bootShift 11 24)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState25_control (copyState 4606) input_pc).1) ((tailState25_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState25_frame (by decide) (by decide)
  · exact (tailState25_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState25_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState25_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState26_success
  · decide

private theorem tail_guard25 : baselineMachineConfig.progAddresses = (tailState25 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState25 (copyState 4606)) (riscvEnc (bootShift 11 24)).length := by
  refine ⟨((tailState25_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState25_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState25_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step26 : asmStep riscvConfig (tailState26 (copyState 4606)) (bootConst 12 2015) (tailState27 (copyState 4606)) := by
  apply checked_step_to (tailState26 (copyState 4606)) (tailState27 (copyState 4606)) (bootConst 12 2015) rfl
  · exact installed_tail_instruction (tailState26 (copyState 4606)) 2147483828 (bootConst 12 2015)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState26_control (copyState 4606) input_pc).1) ((tailState26_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState26_frame (by decide) (by decide)
  · exact (tailState26_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState26_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState26_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState27_success
  · decide

private theorem tail_guard26 : baselineMachineConfig.progAddresses = (tailState26 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState26 (copyState 4606)) (riscvEnc (bootConst 12 2015)).length := by
  refine ⟨((tailState26_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState26_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState26_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step27 : asmStep riscvConfig (tailState27 (copyState 4606)) (bootShift 12 24) (tailState28 (copyState 4606)) := by
  apply checked_step_to (tailState27 (copyState 4606)) (tailState28 (copyState 4606)) (bootShift 12 24) rfl
  · exact installed_tail_instruction (tailState27 (copyState 4606)) 2147483832 (bootShift 12 24)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState27_control (copyState 4606) input_pc).1) ((tailState27_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState27_frame (by decide) (by decide)
  · exact (tailState27_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState27_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState27_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState28_success
  · decide

private theorem tail_guard27 : baselineMachineConfig.progAddresses = (tailState27 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState27 (copyState 4606)) (riscvEnc (bootShift 12 24)).length := by
  refine ⟨((tailState27_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState27_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState27_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step28 : asmStep riscvConfig (tailState28 (copyState 4606)) (bootConst 13 63) (tailState29 (copyState 4606)) := by
  apply checked_step_to (tailState28 (copyState 4606)) (tailState29 (copyState 4606)) (bootConst 13 63) rfl
  · exact installed_tail_instruction (tailState28 (copyState 4606)) 2147483836 (bootConst 13 63)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState28_control (copyState 4606) input_pc).1) ((tailState28_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState28_frame (by decide) (by decide)
  · exact (tailState28_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState28_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState28_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState29_success
  · decide

private theorem tail_guard28 : baselineMachineConfig.progAddresses = (tailState28 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState28 (copyState 4606)) (riscvEnc (bootConst 13 63)).length := by
  refine ⟨((tailState28_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState28_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState28_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step29 : asmStep riscvConfig (tailState29 (copyState 4606)) (bootShift 13 29) (tailState30 (copyState 4606)) := by
  apply checked_step_to (tailState29 (copyState 4606)) (tailState30 (copyState 4606)) (bootShift 13 29) rfl
  · exact installed_tail_instruction (tailState29 (copyState 4606)) 2147483840 (bootShift 13 29)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState29_control (copyState 4606) input_pc).1) ((tailState29_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState29_frame (by decide) (by decide)
  · exact (tailState29_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState29_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState29_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState30_success
  · decide

private theorem tail_guard29 : baselineMachineConfig.progAddresses = (tailState29 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState29 (copyState 4606)) (riscvEnc (bootShift 13 29)).length := by
  refine ⟨((tailState29_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState29_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState29_control (copyState 4606) input_pc).1)]; decide

private theorem tail_step30 : asmStep riscvConfig (tailState30 (copyState 4606)) (bootLoc 10 0x800000c4 nativePc) (tailState31 (copyState 4606)) := by
  apply checked_step_to (tailState30 (copyState 4606)) (tailState31 (copyState 4606)) (bootLoc 10 0x800000c4 nativePc) rfl
  · exact installed_tail_instruction (tailState30 (copyState 4606)) 2147483844 (bootLoc 10 0x800000c4 nativePc)
      (by simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore])
      ((tailState30_control (copyState 4606) input_pc).1) ((tailState30_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1) tailState30_frame (by decide) (by decide)
  · exact (tailState30_control (copyState 4606) input_pc).2.2.2.1.trans (copyState_fields 4606).2.2.2.1
  · exact (tailState30_control (copyState 4606) input_pc).2.2.2.2.2.trans (copyState_fields 4606).1
  · exact (tailState30_control (copyState 4606) input_pc).2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2
  · simpa only [Bool.not_eq_true] using tailState31_success
  · decide

private theorem tail_guard30 : baselineMachineConfig.progAddresses = (tailState30 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState30 (copyState 4606)) (riscvEnc (bootLoc 10 0x800000c4 nativePc)).length := by
  refine ⟨((tailState30_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState30_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState30_control (copyState 4606) input_pc).1)]; decide

private theorem final_jump_step (state next : AsmState 64)
    (endpoint : after state (.jump (BitVec.ofNat 64 nativePc - 0x800000cc)) = next)
    (position : state.pc = 0x800000cc) (domain : state.memDomain = bootstrapDomain)
    (frame : ∀ x, initialPc ≤ x.toNat → x.toNat < initialPc+208 → state.mem x = initialMemory x)
    (lr : state.lr = 1) (be : state.be = false) (align : state.align = 2)
    (success : next.failed = false) :
    asmStep riscvConfig state (.jump (BitVec.ofNat 64 nativePc - 0x800000cc)) next := by
  have member : (2147483852, (HolAsm.jump (BitVec.ofNat 64 nativePc - 0x800000cc))) ∈ bootstrapBlocks := by
    simp [bootstrapBlocks, bootLoc, bootConst, bootShift, bootStore]
  have jumpOffset : BitVec.ofNat 64 nativePc - 0x800000cc = 4004#64 := by decide
  have literalMember : (2147483852, (HolAsm.jump 4004#64)) ∈ bootstrapBlocks := by
    simpa only [jumpOffset] using member
  have literalBytes : bytesInMemoryHOL state.pc (riscvEnc (HolAsm.jump 4004#64))
      state.mem state.memDomain :=
    installed_tail_instruction state 2147483852 (.jump 4004#64) literalMember
      position domain frame (by decide) (by decide)
  have bytes : bytesInMemoryHOL state.pc
      (riscvEnc (HolAsm.jump (BitVec.ofNat 64 nativePc - 0x800000cc)))
      state.mem state.memDomain := by
    simpa only [jumpOffset] using literalBytes
  exact checked_step_to state next (.jump (BitVec.ofNat 64 nativePc - 0x800000cc))
    endpoint bytes lr be align (by simpa only [Bool.not_eq_true] using success) (by decide)

private theorem tail_step31 : asmStep riscvConfig (tailState31 (copyState 4606))
    (.jump (BitVec.ofNat 64 nativePc - 0x800000cc)) (tailState32 (copyState 4606)) := by
  have c := tailState31_control (copyState 4606) input_pc
  exact final_jump_step (tailState31 (copyState 4606)) (tailState32 (copyState 4606))
    rfl c.1 (c.2.2.1.trans (copyState_fields 4606).2.1) tailState31_frame
    (c.2.2.2.1.trans (copyState_fields 4606).2.2.2.1)
    (c.2.2.2.2.2.trans (copyState_fields 4606).1)
    (c.2.2.2.2.1.trans (copyState_fields 4606).2.2.2.2) tailState32_success

private theorem tail_guard31 : baselineMachineConfig.progAddresses = (tailState31 (copyState 4606)).memDomain ∧
    ffiEntryPcsDisjoint baselineMachineConfig (tailState31 (copyState 4606)) (riscvEnc (.jump (BitVec.ofNat 64 nativePc - 0x800000cc))).length := by
  refine ⟨((tailState31_control (copyState 4606) input_pc).2.2.1.trans (copyState_fields 4606).2.1).symm, ?_⟩
  apply bootstrap_ffi_disjoint
  · rw [((tailState31_control (copyState 4606) input_pc).1)]; decide
  · rw [((tailState31_control (copyState 4606) input_pc).1)]; decide

/-- A source trace carrying all ordinary evaluator guards. -/
private inductive TailCheckedTrace : List (HolAsm 64) → AsmState 64 → AsmState 64 → Prop
  | nil (s) : TailCheckedTrace [] s s
  | cons {s next final code i}
      (step : asmStep riscvConfig s i next)
      (domain : baselineMachineConfig.progAddresses = s.memDomain)
      (ffi : ffiEntryPcsDisjoint baselineMachineConfig s (riscvEnc i).length)
      (rest : TailCheckedTrace code next final) : TailCheckedTrace (i::code) s final

private theorem trace_checked {code s t} (h : TailCheckedTrace code s t) : Checked code s := by
  induction h with
  | nil => trivial
  | @cons s next final code i step domain ffi rest ih =>
    change asmStep riscvConfig s i (after s i) ∧ Checked code (after s i)
    have endpoint : after s i = next := step.2.2.2.2.1
    rw [endpoint]
    exact ⟨step, ih⟩

private theorem trace_guards {code s t} (h : TailCheckedTrace code s t) :
    EvaluatorGuards baselineMachineConfig code s := by
  induction h with
  | nil => trivial
  | @cons s next final code i step domain ffi rest ih =>
    change baselineMachineConfig.progAddresses = s.memDomain ∧
      ffiEntryPcsDisjoint baselineMachineConfig s (riscvEnc i).length ∧
      EvaluatorGuards baselineMachineConfig code (after s i)
    have endpoint : after s i = next := step.2.2.2.2.1
    rw [endpoint]
    exact ⟨domain, ffi, ih⟩

private theorem trace_thirty_two
    (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 i18 i19 i20 i21 i22 i23 i24 i25 i26 i27 i28 i29 i30 i31 : HolAsm 64)
    (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 : AsmState 64)
    (step0 : asmStep riscvConfig s0 i0 s1)
    (guard0 : baselineMachineConfig.progAddresses = s0.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s0 (riscvEnc i0).length)
    (step1 : asmStep riscvConfig s1 i1 s2)
    (guard1 : baselineMachineConfig.progAddresses = s1.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s1 (riscvEnc i1).length)
    (step2 : asmStep riscvConfig s2 i2 s3)
    (guard2 : baselineMachineConfig.progAddresses = s2.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s2 (riscvEnc i2).length)
    (step3 : asmStep riscvConfig s3 i3 s4)
    (guard3 : baselineMachineConfig.progAddresses = s3.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s3 (riscvEnc i3).length)
    (step4 : asmStep riscvConfig s4 i4 s5)
    (guard4 : baselineMachineConfig.progAddresses = s4.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s4 (riscvEnc i4).length)
    (step5 : asmStep riscvConfig s5 i5 s6)
    (guard5 : baselineMachineConfig.progAddresses = s5.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s5 (riscvEnc i5).length)
    (step6 : asmStep riscvConfig s6 i6 s7)
    (guard6 : baselineMachineConfig.progAddresses = s6.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s6 (riscvEnc i6).length)
    (step7 : asmStep riscvConfig s7 i7 s8)
    (guard7 : baselineMachineConfig.progAddresses = s7.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s7 (riscvEnc i7).length)
    (step8 : asmStep riscvConfig s8 i8 s9)
    (guard8 : baselineMachineConfig.progAddresses = s8.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s8 (riscvEnc i8).length)
    (step9 : asmStep riscvConfig s9 i9 s10)
    (guard9 : baselineMachineConfig.progAddresses = s9.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s9 (riscvEnc i9).length)
    (step10 : asmStep riscvConfig s10 i10 s11)
    (guard10 : baselineMachineConfig.progAddresses = s10.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s10 (riscvEnc i10).length)
    (step11 : asmStep riscvConfig s11 i11 s12)
    (guard11 : baselineMachineConfig.progAddresses = s11.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s11 (riscvEnc i11).length)
    (step12 : asmStep riscvConfig s12 i12 s13)
    (guard12 : baselineMachineConfig.progAddresses = s12.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s12 (riscvEnc i12).length)
    (step13 : asmStep riscvConfig s13 i13 s14)
    (guard13 : baselineMachineConfig.progAddresses = s13.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s13 (riscvEnc i13).length)
    (step14 : asmStep riscvConfig s14 i14 s15)
    (guard14 : baselineMachineConfig.progAddresses = s14.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s14 (riscvEnc i14).length)
    (step15 : asmStep riscvConfig s15 i15 s16)
    (guard15 : baselineMachineConfig.progAddresses = s15.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s15 (riscvEnc i15).length)
    (step16 : asmStep riscvConfig s16 i16 s17)
    (guard16 : baselineMachineConfig.progAddresses = s16.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s16 (riscvEnc i16).length)
    (step17 : asmStep riscvConfig s17 i17 s18)
    (guard17 : baselineMachineConfig.progAddresses = s17.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s17 (riscvEnc i17).length)
    (step18 : asmStep riscvConfig s18 i18 s19)
    (guard18 : baselineMachineConfig.progAddresses = s18.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s18 (riscvEnc i18).length)
    (step19 : asmStep riscvConfig s19 i19 s20)
    (guard19 : baselineMachineConfig.progAddresses = s19.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s19 (riscvEnc i19).length)
    (step20 : asmStep riscvConfig s20 i20 s21)
    (guard20 : baselineMachineConfig.progAddresses = s20.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s20 (riscvEnc i20).length)
    (step21 : asmStep riscvConfig s21 i21 s22)
    (guard21 : baselineMachineConfig.progAddresses = s21.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s21 (riscvEnc i21).length)
    (step22 : asmStep riscvConfig s22 i22 s23)
    (guard22 : baselineMachineConfig.progAddresses = s22.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s22 (riscvEnc i22).length)
    (step23 : asmStep riscvConfig s23 i23 s24)
    (guard23 : baselineMachineConfig.progAddresses = s23.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s23 (riscvEnc i23).length)
    (step24 : asmStep riscvConfig s24 i24 s25)
    (guard24 : baselineMachineConfig.progAddresses = s24.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s24 (riscvEnc i24).length)
    (step25 : asmStep riscvConfig s25 i25 s26)
    (guard25 : baselineMachineConfig.progAddresses = s25.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s25 (riscvEnc i25).length)
    (step26 : asmStep riscvConfig s26 i26 s27)
    (guard26 : baselineMachineConfig.progAddresses = s26.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s26 (riscvEnc i26).length)
    (step27 : asmStep riscvConfig s27 i27 s28)
    (guard27 : baselineMachineConfig.progAddresses = s27.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s27 (riscvEnc i27).length)
    (step28 : asmStep riscvConfig s28 i28 s29)
    (guard28 : baselineMachineConfig.progAddresses = s28.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s28 (riscvEnc i28).length)
    (step29 : asmStep riscvConfig s29 i29 s30)
    (guard29 : baselineMachineConfig.progAddresses = s29.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s29 (riscvEnc i29).length)
    (step30 : asmStep riscvConfig s30 i30 s31)
    (guard30 : baselineMachineConfig.progAddresses = s30.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s30 (riscvEnc i30).length)
    (step31 : asmStep riscvConfig s31 i31 s32)
    (guard31 : baselineMachineConfig.progAddresses = s31.memDomain ∧ ffiEntryPcsDisjoint baselineMachineConfig s31 (riscvEnc i31).length)
    : TailCheckedTrace [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22, i23, i24, i25, i26, i27, i28, i29, i30, i31] s0 s32 :=
  .cons step0 guard0.1 guard0.2 (.cons step1 guard1.1 guard1.2 (.cons step2 guard2.1 guard2.2 (.cons step3 guard3.1 guard3.2 (.cons step4 guard4.1 guard4.2 (.cons step5 guard5.1 guard5.2 (.cons step6 guard6.1 guard6.2 (.cons step7 guard7.1 guard7.2 (.cons step8 guard8.1 guard8.2 (.cons step9 guard9.1 guard9.2 (.cons step10 guard10.1 guard10.2 (.cons step11 guard11.1 guard11.2 (.cons step12 guard12.1 guard12.2 (.cons step13 guard13.1 guard13.2 (.cons step14 guard14.1 guard14.2 (.cons step15 guard15.1 guard15.2 (.cons step16 guard16.1 guard16.2 (.cons step17 guard17.1 guard17.2 (.cons step18 guard18.1 guard18.2 (.cons step19 guard19.1 guard19.2 (.cons step20 guard20.1 guard20.2 (.cons step21 guard21.1 guard21.2 (.cons step22 guard22.1 guard22.2 (.cons step23 guard23.1 guard23.2 (.cons step24 guard24.1 guard24.2 (.cons step25 guard25.1 guard25.2 (.cons step26 guard26.1 guard26.2 (.cons step27 guard27.1 guard27.2 (.cons step28 guard28.1 guard28.2 (.cons step29 guard29.1 guard29.2 (.cons step30 guard30.1 guard30.2 (.cons step31 guard31.1 guard31.2 (.nil s32))))))))))))))))))))))))))))))))

private theorem tail_trace : TailCheckedTrace tailCode (tailState0 (copyState 4606)) (tailState32 (copyState 4606)) :=
  trace_thirty_two
    (bootLoc 5 0x8000002c initDataRam)
    (bootConst 6 161)
    (bootShift 6 24)
    (bootStore 6 5 0)
    (bootLoc 5 0x80000040 (initDataRam+8))
    (bootConst 6 2015)
    (bootShift 6 24)
    (bootStore 6 5 0)
    (bootLoc 5 0x80000054 (initDataRam+16))
    (bootConst 6 63)
    (bootShift 6 29)
    (bootStore 6 5 0)
    (bootConst 5 161)
    (bootShift 5 24)
    (bootLoc 6 0x80000070 (initDataRam+24))
    (bootStore 6 5 0)
    (bootLoc 6 0x8000007c initDataEnd)
    (bootStore 6 5 8)
    (bootLoc 6 0x80000088 initDataEnd)
    (bootStore 6 5 16)
    (bootLoc 6 0x80000094 0x800f0134)
    (bootStore 6 5 24)
    (bootLoc 6 0x800000a0 0x800f1000)
    (bootStore 6 5 32)
    (bootConst 11 161)
    (bootShift 11 24)
    (bootConst 12 2015)
    (bootShift 12 24)
    (bootConst 13 63)
    (bootShift 13 29)
    (bootLoc 10 0x800000c4 nativePc)
    (.jump (BitVec.ofNat 64 nativePc - 0x800000cc))
    (tailState0 (copyState 4606)) (tailState1 (copyState 4606)) (tailState2 (copyState 4606)) (tailState3 (copyState 4606)) (tailState4 (copyState 4606)) (tailState5 (copyState 4606)) (tailState6 (copyState 4606)) (tailState7 (copyState 4606)) (tailState8 (copyState 4606)) (tailState9 (copyState 4606)) (tailState10 (copyState 4606)) (tailState11 (copyState 4606)) (tailState12 (copyState 4606)) (tailState13 (copyState 4606)) (tailState14 (copyState 4606)) (tailState15 (copyState 4606)) (tailState16 (copyState 4606)) (tailState17 (copyState 4606)) (tailState18 (copyState 4606)) (tailState19 (copyState 4606)) (tailState20 (copyState 4606)) (tailState21 (copyState 4606)) (tailState22 (copyState 4606)) (tailState23 (copyState 4606)) (tailState24 (copyState 4606)) (tailState25 (copyState 4606)) (tailState26 (copyState 4606)) (tailState27 (copyState 4606)) (tailState28 (copyState 4606)) (tailState29 (copyState 4606)) (tailState30 (copyState 4606)) (tailState31 (copyState 4606)) (tailState32 (copyState 4606))
    tail_step0 tail_guard0 tail_step1 tail_guard1 tail_step2 tail_guard2 tail_step3 tail_guard3 tail_step4 tail_guard4 tail_step5 tail_guard5 tail_step6 tail_guard6 tail_step7 tail_guard7 tail_step8 tail_guard8 tail_step9 tail_guard9 tail_step10 tail_guard10 tail_step11 tail_guard11 tail_step12 tail_guard12 tail_step13 tail_guard13 tail_step14 tail_guard14 tail_step15 tail_guard15 tail_step16 tail_guard16 tail_step17 tail_guard17 tail_step18 tail_guard18 tail_step19 tail_guard19 tail_step20 tail_guard20 tail_step21 tail_guard21 tail_step22 tail_guard22 tail_step23 tail_guard23 tail_step24 tail_guard24 tail_step25 tail_guard25 tail_step26 tail_guard26 tail_step27 tail_guard27 tail_step28 tail_guard28 tail_step29 tail_guard29 tail_step30 tail_guard30 tail_step31 tail_guard31

/-- The complete real tail is checked with no supplied execution premises. -/
theorem tail_checked : Checked tailCode (copyState 4606) :=
  Eq.mp (congrArg (Checked tailCode) (tailState0_eq (copyState 4606))) (trace_checked tail_trace)

/-- All tail instructions execute ordinary target semantics in the compiler evaluator. -/
theorem tail_guards : EvaluatorGuards baselineMachineConfig tailCode (copyState 4606) :=
  Eq.mp (congrArg (EvaluatorGuards baselineMachineConfig tailCode)
    (tailState0_eq (copyState 4606))) (trace_guards tail_trace)

end InitECandidate.Solver.FastEnv.BootstrapStraightLine

/-! ## Section BootstrapTrace -/

set_option autoImplicit false

namespace InitECandidate.Solver.FastEnv.BootstrapTrace
open InitE InitECandidate.Proofs InitECandidate.Solver.FastEnv InitECandidate.Proofs.BootstrapStraightLine InitECandidate.Solver.FastEnv.BootstrapCopyGuards InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitE
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Proofs.BootstrapAsmComposition InitECandidate.Solver.FastEnv.BootstrapCopyGuards

def fullBootstrapCode : List (HolAsm 64) :=
  prefixCode ++ (loopProgram 4606 ++ tailCode)

theorem full_length : fullBootstrapCode.length = 23065 := by
  simp only [fullBootstrapCode, List.length_append, loopProgram_length]
  change 3 + (5 * 4606 + 32) = 23065
  rfl

theorem checked_append (left right : List (HolAsm 64)) (s : AsmState 64) :
    Checked (left ++ right) s ↔ Checked left s ∧ Checked right (run left s) := by
  induction left generalizing s with
  | nil => simp [Checked, run]
  | cons i rest ih => simp only [List.cons_append, Checked, run, ih, and_assoc]

theorem guards_append (left right : List (HolAsm 64)) (s : AsmState 64) :
    EvaluatorGuards baselineMachineConfig (left ++ right) s ↔
      EvaluatorGuards baselineMachineConfig left s ∧
        EvaluatorGuards baselineMachineConfig right (run left s) := by
  induction left generalizing s with
  | nil => simp [EvaluatorGuards, run]
  | cons i rest ih => simp only [List.cons_append, EvaluatorGuards, run, ih, and_assoc]

/-- The three address loads execute below every native FFI entry. -/
theorem prefix_guards : EvaluatorGuards baselineMachineConfig prefixCode initialAsm := by
  simp only [prefixCode, bootstrapBlocks, List.take, List.map, EvaluatorGuards]
  refine ⟨rfl, ?_, rfl, ?_, rfl, ?_, trivial⟩
  all_goals apply bootstrap_ffi_disjoint
  all_goals simp [after, bootLoc, asmUpd, updPc, updReg, initialAsm, initialPc,
    riscvEnc, riscvAst, riscvEncode, initDataRom, initDataRam, initDataEnd]

/-- The computed endpoint of prefix, loop and tail is the tail endpoint. -/
theorem full_run : run fullBootstrapCode initialAsm = tailEndpoint := by
  simp only [fullBootstrapCode, run_append, prefix_endpoint, loopProgram_run]
  rfl

/-- Local checked traces compose without a machine-run premise. -/
theorem full_checked_of_tail (tail : Checked tailCode (copyState 4606)) :
    Checked fullBootstrapCode initialAsm := by
  rw [fullBootstrapCode, checked_append]
  refine ⟨prefix_checked, ?_⟩
  rw [prefix_endpoint, checked_append]
  refine ⟨copyLoop_checked, ?_⟩
  simpa only [loopProgram_run, copyState] using tail

theorem full_guards_of_tail
    (tail : EvaluatorGuards baselineMachineConfig tailCode (copyState 4606)) :
    EvaluatorGuards baselineMachineConfig fullBootstrapCode initialAsm := by
  rw [fullBootstrapCode, guards_append]
  refine ⟨prefix_guards, ?_⟩
  rw [prefix_endpoint, guards_append]
  refine ⟨copyLoop_guards, ?_⟩
  simpa only [loopProgram_run, copyState] using tail

theorem full_endpoint_of_tail (tail : Checked tailCode (copyState 4606)) :
    run fullBootstrapCode initialAsm = installedAsm :=
  full_run.trans (tail_endpoint_eq tail)

/-- Checked ASM execution yields the exact target-evaluator prefix ending at
an installed native-entry state. The machine endpoint is obtained from the
encoder correctness proof, never assumed. -/
theorem full_evaluator_of_tail {σ : Type} (io : HolFfiState σ) (ms : riscv_state)
    (initial : targetStateRel riscvTarget initialAsm ms)
    (tailChecks : Checked tailCode (copyState 4606))
    (tailGuards : EvaluatorGuards baselineMachineConfig tailCode (copyState 4606)) :
    ∃ count post,
      (∀ clock, evaluateTargetHOL baselineMachineConfig io (count + clock) ms =
        evaluateTargetHOL baselineMachineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post := by
  obtain ⟨count, post, shift, relation, _⟩ :=
    checked_trace_evaluator baselineMachineConfig rfl rfl fullBootstrapCode initialAsm
      (full_checked_of_tail tailChecks) (full_guards_of_tail tailGuards) ms io initial
  exact ⟨count, post, shift, by rwa [full_endpoint_of_tail tailChecks] at relation⟩

/-- Every instruction of the actual submitted bootstrap has a checked ASM step. -/
theorem full_checked : Checked fullBootstrapCode initialAsm :=
  full_checked_of_tail tail_checked

theorem full_guards : EvaluatorGuards baselineMachineConfig fullBootstrapCode initialAsm :=
  full_guards_of_tail tail_guards

/-- The submitted startup reaches the exact native compiler installation. -/
theorem full_endpoint : run fullBootstrapCode initialAsm = installedAsm :=
  full_endpoint_of_tail tail_checked

/-- The actual submitted bootstrap supplies a finite evaluator prefix, with
no assumed bootstrap execution or installation poststate. -/
theorem full_evaluator {σ : Type} (io : HolFfiState σ) (ms : riscv_state)
    (initial : targetStateRel riscvTarget initialAsm ms) :
    ∃ count post,
      (∀ clock, evaluateTargetHOL baselineMachineConfig io (count + clock) ms =
        evaluateTargetHOL baselineMachineConfig io clock post) ∧
      targetStateRel riscvTarget installedAsm post :=
  full_evaluator_of_tail io ms initial tail_checked tail_guards

end InitECandidate.Solver.FastEnv.BootstrapTrace

/-! ## Section CompilerInstallationMetadata -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
open InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend.LabToTarget

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem baseline_installation_metadata :
    baselineLabConfig.ffiNames = some baselineNames ∧
    baselineMmio.map (fun rec => nativePc+rec.entryPc) =
      (baselineEntryPcs.map BitVec.toNat).drop 2 ∧
    3788+InitECandidate.nativeCode.length+ffiOffset*(2+3) < 2^64 := by
  rw [LiteralFacts.nativeCode_length]
  decide_cbv

end InitECandidate.Solver.FastEnv

/-! ## Section PanInstallationCore -/

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Pancake.Proofs.PanToTarget

private theorem baseline_dataDm_eq :
    (fun a => decide (installedAsm.regs 11 ≤ a ∧ a < installedAsm.regs 13) ||
      baselineBitmapDm a) = baselineDataDm := by
  funext a
  change (decide (BitVec.ofNat 64 sourceBase ≤ a ∧ a < BitVec.ofNat 64 ramEnd) ||
    baselineBitmapDm a) = _
  simp only [baselineDataDm,BitVec.le_def,BitVec.lt_def]
  rfl

private theorem align_sourceBase : holByteAligned (BitVec.ofNat 64 sourceBase) = true := by
  unfold holByteAligned
  rw [holLOG2_eq_log2 (by decide)]
  decide
private theorem align_ramEnd : holByteAligned (BitVec.ofNat 64 ramEnd) = true := by
  unfold holByteAligned
  rw [holLOG2_eq_log2 (by decide)]
  decide
private theorem align_bitmapPtr : holByteAligned (BitVec.ofNat 64 (initDataRam+24)) = true := by
  unfold holByteAligned
  rw [holLOG2_eq_log2 (by decide)]
  decide

private theorem baseline_good_init :
    goodInitState baselineMachineConfig baselineInstalledState InitECandidate.nativeCode 3788
      installedAsm (packedWordMemory installedMemory) baselineDataDm baselineSharedDm := by
  refine ⟨machineStateOfAsm_relation _ (by decide),⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,
    baseline_start_pc,by decide,baseline_machine_noInterference,
    baseline_ffi_interference,baseline_cache_interference,baseline_native_codeLoaded,
    baseline_code_bytes,baseline_data_program,baseline_data_aligned_closed,
    baseline_shared_domain,baseline_shared_aligned_closed,baseline_program_shared_disjoint,
    packedWordMemory_certificate installedMemory,baseline_code_buffer,baseline_code_size_bound⟩

theorem baseline_pan_installed_core :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      (some baselineNames) (11,13) baselineMachineConfig baselineMmio baselineInstalledState
      (wlabWlocExact ∘ sourceMemory) ordinaryDomain sharedDomain := by
  apply panInstalled_intro _ _ _ _ _ _ _ _ _ _ _ _ installedAsm
    (packedWordMemory installedMemory) (BitVec.ofNat 64 (initDataRam+24))
    baselineBitmapDm baselineSharedDm
  refine ⟨?_,?_,?_,align_sourceBase,align_ramEnd,align_bitmapPtr,
    by decide,by decide,?_,?_,?_,?_,?_,?_,?_,rfl,?_⟩
  · exact installed_ordinary_word
  · simpa only [baseline_dataDm_eq] using baseline_good_init
  · exact source_shared_domain baselineSharedDm (by intro a; simp [baselineSharedDm,machineSharedDomain])
  · exact baseline_heap_bitmap_disjoint
  · exact congrArg WordLocW.word (baseline_source_headers ⟨0,by decide⟩)
  · have h := congrArg WordLocW.word (baseline_source_headers ⟨1,by decide⟩)
    simp only [bitmap_count]
    change packedWordMemory installedMemory (BitVec.ofNat 64 (sourceBase+8*1)) =
      .word Guest.startupHeaders[1]
    exact h
  · have h := congrArg WordLocW.word (baseline_source_headers ⟨2,by decide⟩)
    simp only [bitmap_count]
    change packedWordMemory installedMemory (BitVec.ofNat 64 (sourceBase+8*2)) =
      .word Guest.startupHeaders[2]
    exact h
  · have h := congrArg WordLocW.word (baseline_source_headers ⟨3,by decide⟩)
    simp only [baseline_literal_layout.2.1]
    change packedWordMemory installedMemory (BitVec.ofNat 64 (sourceBase+8*3)) =
      .word Guest.startupHeaders[3]
    exact h
  · have h := congrArg WordLocW.word (baseline_source_headers ⟨4,by decide⟩)
    simp only [baseline_literal_layout.2.1]
    change packedWordMemory installedMemory (BitVec.ofNat 64 (sourceBase+8*4)) =
      .word Guest.startupHeaders[4]
    exact h
  · rw [baseline_bitmap_aligned_domain]
    exact baseline_bitmap_separation
  · intro i hi
    have heq : i = 2 := by
      change mmioPcsMinIndex baselineNames = some i at hi
      rw [baseline_ffi_boundary] at hi
      exact (Option.some.inj hi).symm
    subst i
    refine ⟨baseline_installation_metadata.2.1,?_,baseline_installation_metadata.2.2⟩
    change machineMmioInfo (BitVec.ofNat 64 nativePc) 2 baselineMmio =
      List.zip ((List.range baselineMmio.length).map (fun index => index+2))
        (baselineMmio.map fun rec => (rec.nbytes,
          Flapjack.Compiler.Encoders.Asm.HolAddr.addr rec.addrReg (BitVec.ofNat 64 rec.addrOff),
          rec.reg,BitVec.ofNat 64 rec.exitPc+BitVec.ofNat 64 nativePc))
    simp only [machineMmioInfo,BitVec.add_comm]

end InitECandidate.Solver.FastEnv

/-! ## Section PanInstallation -/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
set_option maxRecDepth 10000
set_option maxHeartbeats 0
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Pancake.Proofs.PanToTarget
set_option maxRecDepth 10000 in
private theorem baseline_mmio_projection : baselineLabConfig.shmemExtra = baselineMmio := by decide_cbv

set_option maxRecDepth 10000 in
theorem baseline_pan_installed_metadata :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineLabConfig.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineLabConfig.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ sourceMemory) ordinaryDomain sharedDomain := by
  have hregs : heapRegs pancakeRiscVBackendConfig.stackConf.regNames = (11,13) := by
    unfold pancakeRiscVBackendConfig
    rw [riscvBackendConfig_eq_executable]
    decide_cbv
  exact panInstalled_metadata_congr _ _ _ _ _ (some baselineNames) _ (11,13)
    _ _ baselineMmio _ _ (wlabWlocExact ∘ sourceMemory) _ ordinaryDomain _ sharedDomain
    baseline_installation_metadata.1 hregs baseline_mmio_projection rfl rfl rfl baseline_pan_installed_core

/-- Every compiler installation premise is certified after the bootstrap. -/
theorem baseline_pan_installed (input : Guest.InputBlob) :
    panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      baselineLabConfig.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig baselineLabConfig.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
  exact panInstalled_metadata_congr _ _ _ _ _ baselineLabConfig.ffiNames
    _ (heapRegs pancakeRiscVBackendConfig.stackConf.regNames) _ _ baselineLabConfig.shmemExtra
    _ _ (wlabWlocExact ∘ sourceMemory) _ ordinaryDomain _ sharedDomain
    rfl rfl rfl rfl (source_memory_domain input) rfl baseline_pan_installed_metadata

end InitECandidate.Solver.FastEnv

/-! ## Section InstallationTransport -/

set_option maxRecDepth 10000

namespace InitECandidate.Solver.FastEnv
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget

/-- The concrete target fields visible to compiler installation. Internal
pipeline bookkeeping may differ after executing startup. -/
structure InstallationAgreement {S Q : Type} (mc : MachineConfig 64 S Q)
    (before after : S) : Prop where
  ok : mc.target.stateOk after = true
  pc : mc.target.getPc after = mc.target.getPc before
  bytes : ∀ a, mc.progAddresses a → mc.target.getByte after a = mc.target.getByte before a
  regs : ∀ r, r < mc.target.config.regCount ∧ mc.target.config.avoidRegs.contains r = false →
    mc.target.getReg after r = mc.target.getReg before r
  fpRegs : ∀ r, r < mc.target.config.fpRegCount →
    mc.target.getFpReg after r = mc.target.getFpReg before r

theorem goodInitState_transport {S Q : Type} {mc : MachineConfig 64 S Q}
    {before after : S} (agreement : InstallationAgreement mc before after)
    {bytes : List (BitVec 8)} {cbspace : Nat} {t : AsmState 64}
    {m : BitVec 64 → WordLocW 64} {dm sdm : BitVec 64 → Bool}
    (initial : goodInitState mc before bytes cbspace t m dm sdm) :
    goodInitState mc after bytes cbspace t m dm sdm := by
  rcases initial with ⟨related, configured, pc, start, aligned, next, ffi, cache,
    loaded, inMem, domain, byteDomain, shared, sharedByte, disjoint, packed, buffer, size⟩
  have relation : targetStateRel mc.target t after := by
    refine ⟨agreement.ok, agreement.pc.trans related.2.1, ?_, ?_, ?_⟩
    · intro a ha
      rw [agreement.bytes a (by rw [← configured.2.2.2.1]; exact ha)]
      exact related.2.2.1 a ha
    · intro r hr
      rw [agreement.regs r hr]
      exact related.2.2.2.1 r hr
    · intro r hr
      rw [agreement.fpRegs r hr]
      exact related.2.2.2.2 r hr
  have code : codeLoaded bytes mc after := by
    classical
    have memory : (fun a => if mc.progAddresses a then some (mc.target.getByte after a) else none) =
        (fun a => if mc.progAddresses a then some (mc.target.getByte before a) else none) := by
      funext a
      by_cases ha : mc.progAddresses a
      · simp only [if_pos ha, agreement.bytes a ha]
      · simp only [if_neg ha]
    simpa only [codeLoaded, agreement.pc, memory] using loaded
  exact ⟨relation, configured, by rw [agreement.pc]; exact pc, start, aligned,
    next, ffi, cache, code, inMem, domain, byteDomain, shared, sharedByte,
    disjoint, packed, buffer, size⟩

theorem panInstalled_transport {S Q : Type} {mc : MachineConfig 64 S Q}
    {before after : S} (agreement : InstallationAgreement mc before after)
    {bytes : List (BitVec 8)} {cbspace : Nat} {bitmaps : List (BitVec 64)} {dataSp : Nat}
    {ffiNames : Option (List HolFfiName)} {regs : Nat × Nat}
    {extra : List Compiler.Backend.LabToTarget.ShmemInfoNum}
    {pMem : BitVec 64 → WordLocW 64} {pDom sdm : BitVec 64 → Prop}
    (installed : panInstalled bytes cbspace bitmaps dataSp ffiNames regs mc extra before pMem pDom sdm) :
    panInstalled bytes cbspace bitmaps dataSp ffiNames regs mc extra after pMem pDom sdm := by
  rcases installed with ⟨t, m, pointer, bitmapsDm, sharedDm, source, initial, rest⟩
  exact ⟨t, m, pointer, bitmapsDm, sharedDm, source,
    goodInitState_transport agreement initial,
    by simpa only [agreement.pc] using rest⟩

/-- Startup's actual endpoint agrees with the canonical installed machine on
all fields that matter to the compiler theorem. -/
theorem baseline_endpoint_agreement (ms : Flapjack.RiscV.L3.riscv_state)
    (related : targetStateRel riscvTarget installedAsm ms) :
    InstallationAgreement baselineMachineConfig baselineInstalledState ms := by
  have canonical := machineStateOfAsm_relation installedAsm (by decide)
  refine ⟨related.1, related.2.1.trans canonical.2.1.symm, ?_, ?_, ?_⟩
  · intro a ha
    exact (related.2.2.1 a ha).trans (canonical.2.2.1 a ha).symm
  · intro r hr
    exact (related.2.2.2.1 r hr).trans (canonical.2.2.2.1 r hr).symm
  · intro r hr
    exact (related.2.2.2.2 r hr).trans (canonical.2.2.2.2 r hr).symm

end InitECandidate.Solver.FastEnv
