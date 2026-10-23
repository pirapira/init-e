import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.SelfContainedBoundedCertificate
import InitECandidate.Solver.SelfContainedTargetBound
import InitECandidate.Solver.YukonBaselineCompat

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
Self-contained five-stage source-to-target clock bridge.
All bounded simulation steps come from Solver modules. The final target
non-timeout obligation remains explicit, as in YukonPipelineBridge.
-/

namespace InitECandidate.Solver.SelfContainedPipelineBridge

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.YukonCleanVerifierCheck (baselineHeapLen baseline_pan_installed oracle_baseline_installation)
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL)
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open Flapjack.LoopToWordStateRelImpSemanticsSupport

/-! ## 1. End-to-End Linear Pipeline Target Budget & Monotonicity -/

/-- End-to-end linear target step budget as a function of the `PanSem` clock `k_pan`,
frontend linear clock expansion `(C_front, D_front)` (`PanSem -> WordSem`),
backend linear clock expansion `(C_back, D_back)` (`WordSem -> StackSem -> LabSem`),
and target instruction expansion factor `C_target` (`LabSem -> Target`). -/
def linearPipelineTargetBudget (k_pan C_front D_front C_back D_back C_target : Nat) : Nat :=
  C_target * (C_back * (C_front * k_pan + D_front) + D_back)

/-- `linearPipelineTargetBudget` is monotone in the source `PanSem` clock `k_pan`. -/
theorem linearPipelineTargetBudget_mono_k_pan
    {k₁ k₂ : Nat} (C_front D_front C_back D_back C_target : Nat)
    (hle : k₁ ≤ k₂) :
    linearPipelineTargetBudget k₁ C_front D_front C_back D_back C_target ≤
      linearPipelineTargetBudget k₂ C_front D_front C_back D_back C_target := by
  unfold linearPipelineTargetBudget
  exact Nat.mul_le_mul_left C_target
    (Nat.add_le_add_right
      (Nat.mul_le_mul_left C_back
        (Nat.add_le_add_right (Nat.mul_le_mul_left C_front hle) D_front))
      D_back)

/-- Compositional stage-bound inequality: if `k_word ≤ C_front * k_pan + D_front`,
`k_lab ≤ C_back * k_word + D_back`, and `K_post ≤ C_target * k_lab`, then
`K_post ≤ linearPipelineTargetBudget k_pan C_front D_front C_back D_back C_target`. -/
theorem linearPipelineTargetBudget_of_stage_bounds
    (k_pan k_word k_lab K_post C_front D_front C_back D_back C_target : Nat)
    (h_front : k_word ≤ C_front * k_pan + D_front)
    (h_back : k_lab ≤ C_back * k_word + D_back)
    (h_target : K_post ≤ C_target * k_lab) :
    K_post ≤ linearPipelineTargetBudget k_pan C_front D_front C_back D_back C_target := by
  unfold linearPipelineTargetBudget
  have h1 : C_back * k_word + D_back ≤ C_back * (C_front * k_pan + D_front) + D_back :=
    Nat.add_le_add_right (Nat.mul_le_mul_left C_back h_front) D_back
  have h2 : k_lab ≤ C_back * (C_front * k_pan + D_front) + D_back :=
    Nat.le_trans h_back h1
  exact Nat.le_trans h_target (Nat.mul_le_mul_left C_target h2)

/-- The composed bound has the exact affine slope and intercept. -/
theorem linearPipelineTargetBudget_affine
    (k a b c d e : Nat) :
    linearPipelineTargetBudget k a b c d e =
      (e * c * a) * k + e * (c * b + d) := by
  simp only [linearPipelineTargetBudget, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]

/-- Zero source clock leaves exactly the composed stage overhead. -/
theorem linearPipelineTargetBudget_zero_source
    (a b c d e : Nat) :
    linearPipelineTargetBudget 0 a b c d e = e * (c * b + d) := by
  simp [linearPipelineTargetBudget]

/-- Increasing the source clock by one adds precisely the composed slope. -/
theorem linearPipelineTargetBudget_succ
    (k a b c d e : Nat) :
    linearPipelineTargetBudget (k + 1) a b c d e =
      linearPipelineTargetBudget k a b c d e + e * c * a := by
  rw [linearPipelineTargetBudget_affine, linearPipelineTargetBudget_affine,
    Nat.mul_add, Nat.mul_one, Nat.add_right_comm]

/-- Target agreement at the composed budget preserves the source outcome and I/O. -/
theorem target_halt_agree_at_linearPipelineTargetBudget
    {width : Nat} [NeZero width] {S Q σ : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (ms : S)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hclocked : ∃ k post finalFfi,
      evaluateTargetHOL mc ffi k ms = (.halt outcome, post, finalFfi) ∧
        finalFfi.ioEvents = events)
    (k a b c d e : Nat)
    (hnt : (evaluateTargetHOL mc ffi
      (linearPipelineTargetBudget k a b c d e) ms).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi (linearPipelineTargetBudget k a b c d e) ms).1 =
        .halt outcome ∧
      (evaluateTargetHOL mc ffi (linearPipelineTargetBudget k a b c d e) ms).2.2.ioEvents =
        events :=
  SelfContainedTargetBound.pan_to_target_backend_halt_agree_of_not_timeOut
    mc ffi ms outcome events hclocked _ hnt

/-! ## 2. Pipeline Stage Initial States (`PanToWord`, `WordToWord`, `WordToStack`, `StackToLab`) -/

/-- Stage 4 (`LabSem`) initial state constructed by `LabToTarget.makeInit` in `PanToTarget`. -/
noncomputable abbrev pipelineLabInitState {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (p : List (Nat × StackLang.HolProg width)) :
    Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config σ :=
  let regNames := c.stackConf.regNames
  let r1 := StackNames.findNameSpt regNames 2
  let r2 := StackNames.findNameSpt regNames 4
  let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
  let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
  let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
  LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
    (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
    (fun a => sdm a && holByteAligned a) ms
    (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
    (LabToTarget.compile mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
    (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
      mc.target.config.addrOffset sp []))

/-- Stage 3 (`StackSem`) initial state constructed by `FullMakeInit.fullMakeInit` in `PanToTarget`. -/
noncomputable abbrev pipelineStackInitState {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (bitmaps : List (BitVec width)) (p : List (Nat × StackLang.HolProg width)) (dataSp : Nat) :
    StackSemStateFiniteExact width LabToTarget.Config σ :=
  let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
  let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
  let labst := pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p
  (FullMakeInit.fullMakeInit c.stackConf c.dataConf maxHeap sp
    mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
    dataSp (fun _ => (ltconf, [], []))).1

/-- Stage 2b (`WordSem` post-`WordToWord`) initial state constructed by `WordToStack.Native.Initialization.makeInit`. -/
noncomputable abbrev pipelineWordInitState {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (p : List (Nat × StackLang.HolProg width)) (dataSp : Nat) :
    WordSemStateFiniteExact width (Nat × LabToTarget.Config) σ :=
  let sst := pipelineStackInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf bitmaps p dataSp
  let k_reg := mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)
  let worac : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
    fun _ => ((bitmaps.length, ltconf), [])
  WordToStack.Native.Initialization.makeInit mc.target.config k_reg sst (sptFromAList wprog) worac

/-- Stage 2a (`WordSem` pre-`WordToWord`, output of `PanToWord`) initial state (`wst0`). -/
noncomputable abbrev pipelinePanToWordInitState {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (panCode : List (Pancake.PanLang.DeclHOL width))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (p : List (Nat × StackLang.HolProg width)) (dataSp : Nat) :
    WordSemStateFiniteExact width (Nat × LabToTarget.Config) σ :=
  { pipelineWordInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf wprog bitmaps p dataSp with
    code := sptFromAList (panToWordCompileProgHOL mc.target.config.isa panCode) }

/-! ## 3. Frontend & Backend Stage Non-`timeOut` Halt Composition -/

/-- Direct `pan_to_word_halt_of_word_not_timeOut` bridge on `WordToStack.Native.Initialization.makeInit`
(arbitrary-clock `WordSem` halt counterpart of `pan_to_target_pan_to_word_stage_clocked_sim`). -/
theorem pan_to_target_pan_to_word_stage_halt_of_word_not_timeOut
    {width : Nat} [NeZero width] {C σ : Type}
    (ac : AsmConfigExact width) (k_reg : Nat) (sst : StackSemStateFiniteExact width C σ)
    (wcode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : PanSemStateFiniteExact width σ) (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS) (globalsSize : Nat)
    (heapLen : BitVec width)
    (hmem : ∀ a, s.memaddrs a → sst.memory a = wlabWlocExact (s.memory a))
    (hnolab : noLabelsHOL sst.memory (fun a => sst.mdomain a = true))
    (hmdomain : (fun a => sst.mdomain a = true) =
      (fun a => s.memaddrs a ∨ StackRemove.addresses s.topAddr globalsSize a))
    (hshmdomain : (fun a => sst.shMdomain a = true) = s.shMemaddrs)
    (hbe : sst.be = s.be) (hffi : sst.ffi = s.ffi)
    (hcurr : (WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac).store.lookup .currHeap =
      some (.word s.baseAddr))
    (hheap : (WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac).store.lookup .heapLength =
      some (.word heapLen))
    (hstart : start = ofString "main")
    (hsize : globalsSize = ((decShapesHOL panCode).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] panCode)))).sum)
    (hparams : distinctParamsHOL (functionsHOL panCode))
    (htop : s.topAddr = s.baseAddr + (2 : BitVec width) * heapLen -
      panBytesInWord width * BitVec.ofNat width globalsSize)
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (halign : panGlobalsByteAlignedHOL s.topAddr)
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty) (good : goodDimindex width)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
      panCode = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome)
    (k_word : Nat) (res_word : Option (WordSemResult width))
    (t_word : WordSemStateFiniteExact width (Nat × C) σ)
    (hrun_w : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec width))
      { { WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac with
          code := sptFromAList (panToWordCompileProgHOL isa panCode) } with clock := k_word } =
      (res_word, t_word))
    (hnt_w : res_word ≠ some .timeOut) :
    wordEntryClass res_word = .CompleteResult outcome ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents := by
  let wst := WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac
  let wst0 := { wst with code := sptFromAList (panToWordCompileProgHOL isa panCode) }
  rw [InitGlobals_location_eq_first_name] at hrun_w
  exact pan_to_word_halt_of_word_not_timeOut s wst0 isa panCode start globalsSize heapLen
    ⟨hmem, hnolab, hstart, hsize, hparams, hmdomain, hshmdomain, hbe, hffi,
      hcurr, hheap,
      htop, hnodup, halign, halloc, hcode, rfl, hglobals, hlocals, heids, heshapes,
      by simp [wst0, wst, WordToStack.Native.Initialization.makeInit, sptLookup],
      good, hfail⟩
    stCtxt s_decls hst hev_decls k_pan res_src s_src_post outcome hev_call hclass_src
    k_word res_word t_word hrun_w hnt_w

/-- Stage-by-stage `PanSem -> WordSem -> StackSem -> LabSem` halt composition:
given `PanSem` halting at `k_pan`, `WordSem` (`pipelinePanToWordInitState`) not timing out at `k_word`,
`StackSem` (`pipelineStackInitState`) not timing out at `k_stack`, and `LabSem` (`pipelineLabInitState`)
not timing out at `k_lab`, composes `pan_to_word_halt_of_word_not_timeOut`,
`word_to_stack_compile_halt_of_stack_not_timeOut`, and `full_make_init_halt_of_lab_not_timeOut`
to conclude that `LabSem.evaluate` at `k_lab` halts with `outcome` and `s_src_post.ffi.ioEvents`! -/
theorem source_to_lab_halt_of_stage_clock_chain {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm : BitVec width → Bool) (ms : S)
    (bytes : List (BitVec 8)) (cbspace : Nat) (ltconf : LabToTarget.Config)
    (panCode : List (Pancake.PanLang.DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (dataSp : Nat) (stackMax : Option Nat)
    (s : PanSemStateFiniteExact width σ) (start : MlS) (globalsSize heapLen : Nat)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : LabToTarget.mcConfOk mc)
    (hinit : BackendProof.mcInitOk mc.target.config c mc) (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hmax : stackMax = WordDepth.maxDepth wconf.stackFrameSize
      (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)))
    (hnodup : ((Pancake.PanLang.functionsHOL panCode).map Prod.fst).Nodup)
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hpi :
      let regNames := c.stackConf.regNames
      let r1 := StackNames.findNameSpt regNames 2
      let r2 := StackNames.findNameSpt regNames 4
      let biw := StackRemove.bytesInWord width
      let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
      holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
      holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
      1024 * biw ≤ t.regs r2 - t.regs r1 ∧
      (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
      m (t.regs r1) = .word bitmapPtr ∧
      m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
        biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
      m (t.regs r1 + 4 * biw) =
        .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
      SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
        (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)))
    (hpm : ∀ a, decide (s.memaddrs a) = true → m a = wlabWlocExact (s.memory a))
    (hsdm : (fun a => decide (s.shMemaddrs a)) = fun a => sdm a && holByteAligned a)
    (hbase : mc.target.getReg ms mc.lenReg = s.baseAddr)
    (hlt : mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg)
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1))
    (hheapLt : (StackRemove.bytesInWord width).toNat *
      (2 * DataToWord.maxHeapLimit width c.dataConf - 1) < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true)
    (hbe : mc.target.config.bigEndian = s.be) (hffi : s.ffi = ffi)
    (hheapLen : heapLen = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (width / 8))
    (hglobLe : globalsSize ≤ heapLen)
    (hmemaddrs : s.memaddrs =
      StackRemove.addresses (mc.target.getReg ms mc.lenReg) (heapLen - globalsSize))
    (htop : s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heapLen -
      BitVec.ofNat width (globalsSize * width / 8))
    (hstart : start = ofString "main")
    (hsize : globalsSize = ((decShapesHOL panCode).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] panCode)))).sum)
    (hparams : distinctParamsHOL (functionsHOL panCode))
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail)
    (hresLimit : optionLt stackMax
      (some (BackendProof.readLimits mc.target.config c mc ms).1) = true)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
      panCode = some s_decls)
    (k_pan k_word k_stack k_lab : Nat)
    (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome)
    (hnt_word : (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { pipelinePanToWordInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf
          panCode wprog bitmaps p dataSp with clock := k_word }).1 ≠ some .timeOut)
    (hnt_stack : (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { pipelineStackInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf
            bitmaps p dataSp with clock := k_stack })).1 ≠ some .timeOut)
    (hnt_lab : (LabSem.evaluate
      { pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p with
          clock := k_lab }).1 ≠ .timeOut) :
    (LabSem.evaluate
      { pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p with
          clock := k_lab }).1 = .halt outcome ∧
    (LabSem.evaluate
      { pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p with
          clock := k_lab }).2.ffi.ioEvents = s_src_post.ffi.ioEvents := by
  let labst := pipelineLabInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf p
  let sst := pipelineStackInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf bitmaps p dataSp
  let k_reg := mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)
  let worac : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
    fun _ => ((bitmaps.length, ltconf), [])
  let wst := pipelineWordInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf wprog bitmaps p dataSp
  let wst0 := pipelinePanToWordInitState c mc ffi t m bitmapsDm sdm ms bytes cbspace ltconf
    panCode wprog bitmaps p dataSp
  have hA := panToTargetFullMakeInitAssumptions (C := LabToTarget.Config) c mc ffi t m bitmapPtr
    bitmapsDm sdm ms (LabToTarget.compile mc.target.config) bytes cbspace ltconf panCode col wprog
    bitmaps wconf fs p dataSp hcfg hmc hinit hisa hwtw hwts hnodup hpi
  obtain ⟨_, hsemEq, x, hfmi⟩ := panToTargetLabSemantics (C := LabToTarget.Config) c mc ffi t m
    bitmapPtr bitmapsDm sdm ms (LabToTarget.compile mc.target.config) bytes cbspace ltconf panCode
    col wprog bitmaps wconf fs p dataSp s start globalsSize heapLen hcfg hmc hinit hisa hwtw
    hwts hnodup hpm hgi hsdm hpi hbase hlt hlo hhi hheap hheapLt halign hbe hffi hheapLen
    hglobLe hmemaddrs htop hstart hsize hparams halloc hcode hglobals hlocals heids heshapes hfail
  -- Stage 1: PanSem (at k_pan) -> WordSem wst0 (at k_word) via `pan_to_word_halt_of_word_not_timeOut`
  rcases hrun_w0 : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec width))
      { wst0 with clock := k_word } with ⟨res_w0, t_w0⟩
  have hnt_w0 : res_w0 ≠ some .timeOut := by
    have h := hnt_word
    rw [hrun_w0] at h
    exact h
  have good : goodDimindex width := hmc.1
  have hregs := hgi.1.2.2.2.1
  have hreg : ∀ r, asmRegOkExact r mc.target.config = true →
      t.regs r = mc.target.getReg ms r := by
    intro r hr
    simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
    exact (hregs r hr).symm
  have r2 := hreg _ hmc.2.2.2.1
  have r3 := hreg _ hmc.2.2.2.2.1
  have r4 := hreg _ hmc.2.2.2.2.2.1
  have hmword := hgi.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have h2_reg : labst.regs labst.lenReg = .word s.baseAddr := by
    simp [labst, pipelineLabInitState, LabToTarget.makeInit, r2, hbase]
  have h3_reg : labst.regs labst.ptr2Reg = .word (mc.target.getReg ms mc.ptr2Reg) := by
    simp [labst, pipelineLabInitState, LabToTarget.makeInit, r3]
  have h4_reg : labst.regs labst.len2Reg = .word (mc.target.getReg ms mc.len2Reg) := by
    simp [labst, pipelineLabInitState, LabToTarget.makeInit, r4]
  obtain ⟨_, _, -, -, -, g2, -, -, a2, -⟩ := panToTargetInitCodeRun hA
  rw [h2_reg] at g2; cases g2
  have hbase_mod : s.baseAddr.toNat % (width / 8) = 0 :=
    (holByteAligned_iff_mod good _).1 a2
  obtain ⟨_, g2', hcurr, hheapLW⟩ :=
    panToTargetWordInitStore (ac := mc.target.config) (k := k_reg) (wcode := sptFromAList wprog)
      (worac := worac) hA hfmi
  rw [h2_reg] at g2'; cases g2'
  rw [readPointers_s2 hA h2_reg h3_reg h4_reg] at hheapLW
  have hsnd := panToTargetHeapLimitSnd good (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    s.baseAddr (mc.target.getReg ms mc.ptr2Reg) (mc.target.getReg ms mc.len2Reg) a2
    (hbase ▸ hlt) (by rw [← hbase, BitVec.mul_comm]; exact hlo)
    (by rw [BitVec.mul_comm]; exact hhi)
    (by rw [← hbase, BitVec.add_comm, Nat.mul_comm]; exact hheap)
    hheapLt (hbase ▸ halign)
  rw [BitVec.add_comm (-1 * s.baseAddr), ← hheapLen] at hsnd
  have hmd := panToTargetWordInitMdomain (ac := mc.target.config) (k := k_reg)
    (wcode := sptFromAList wprog) (worac := worac)
    s.baseAddr (mc.target.getReg ms mc.ptr2Reg) (mc.target.getReg ms mc.len2Reg) hA hfmi
    h2_reg h3_reg h4_reg
    (by rw [← hbase, BitVec.mul_comm]; exact hlo)
    (by rw [BitVec.mul_comm]; exact hhi)
    (by rw [← hbase, BitVec.add_comm, Nat.mul_comm]; exact hheap)
    hheapLt (hbase ▸ halign)
  rw [← hheapLen] at hmd
  have hmdP : (fun a => wst.mdomain a = true) = StackRemove.addresses s.baseAddr heapLen := by
    funext a; rw [hmd a, decide_eq_true_eq]
  obtain ⟨hffi_w, hbe_w, hsh_w, hmem_w⟩ := panToTargetWordInitMemory
    (ac := mc.target.config) (k := k_reg) (wcode := sptFromAList wprog) (worac := worac) hA hfmi
  have hin : ∀ a, s.memaddrs a → wst.mdomain a = true := by
    intro a ha
    have : StackRemove.addresses s.baseAddr heapLen a := by
      rw [← addressesSplitGlobals good s.baseAddr heapLen globalsSize hglobLe]
      exact .inl ((hbase ▸ hmemaddrs) ▸ ha)
    rw [← hmdP] at this; exact this
  have htopAl : panGlobalsByteAlignedHOL s.topAddr := by
    apply panGlobalsByteAligned_of_mod good
    rw [htop, good_dimindex_div_mul width globalsSize good]
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, bytesInWord_toNat good]
    simp only [BitVec.toNat_ofNat]
    rcases good with h | h <;> subst h <;> simp at hbase_mod ⊢ <;> omega
  obtain ⟨hcw0, hio_w0⟩ :=
    pan_to_target_pan_to_word_stage_halt_of_word_not_timeOut
      mc.target.config k_reg sst (sptFromAList wprog) worac s mc.target.config.isa panCode start
      globalsSize
      (BitVec.ofNat width (StackRemove.Proofs.InitLimits.getStackHeapLimit
        (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (s.baseAddr, mc.target.getReg ms mc.ptr2Reg, mc.target.getReg ms mc.len2Reg)).2 *
        StackRemove.bytesInWord width)
      (fun a ha => (hmem_w a (hin a ha)).trans (hpm a (decide_eq_true ha)))
      (fun a ha => by
        have hadr : StackRemove.addresses s.baseAddr heapLen a := by rw [← hmdP]; exact ha
        obtain ⟨w, -, hw⟩ := hmword a
        rw [Compiler.Backend.LabToTarget.holByteAlign_of_aligned good a
          (addresses_mod good s.baseAddr hbase_mod heapLen a hadr)] at hw
        exact ⟨w, (hmem_w a ha).trans hw⟩)
      (by
        show (fun a => wst.mdomain a = true) = _
        have hmemaddrs' : s.memaddrs = StackRemove.addresses s.baseAddr (heapLen - globalsSize) := by
          rw [← hbase]; exact hmemaddrs
        rw [hmdP, ← addressesSplitGlobals good s.baseAddr heapLen globalsSize hglobLe,
          hmemaddrs', htop])
      (by
        show (fun a => wst.shMdomain a = true) = _
        rw [hsh_w]
        funext a
        have := congrFun hsdm a
        simp only [LabToTarget.makeInit] at this ⊢
        rw [← this, decide_eq_true_eq])
      (hbe_w.trans hbe)
      (hffi_w.trans hffi.symm)
      hcurr
      hheapLW
      hstart hsize hparams
      (by
        rw [htop, good_dimindex_div_mul width globalsSize good]
        have e1 : (2 : BitVec width) * (BitVec.ofNat width (StackRemove.Proofs.InitLimits.getStackHeapLimit
            (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
            (s.baseAddr, mc.target.getReg ms mc.ptr2Reg, mc.target.getReg ms mc.len2Reg)).2 *
            StackRemove.bytesInWord width) =
            StackRemove.bytesInWord width * BitVec.ofNat width heapLen := by
          rw [← hsnd, BitVec.ofNat_mul, BitVec.mul_comm (StackRemove.bytesInWord width),
            ← BitVec.mul_assoc]
          rfl
        have e2 : BitVec.ofNat width (globalsSize * (width / 8)) =
            panBytesInWord width * BitVec.ofNat width globalsSize := by
          rw [BitVec.ofNat_mul, BitVec.mul_comm]; rfl
        rw [e1, e2])
      hnodup htopAl halloc hcode hglobals hlocals heids heshapes good hfail
      stCtxt s_decls hst hev_decls k_pan res_src s_src_post outcome hev_call hclass_src
      k_word res_w0 t_w0 hrun_w0 hnt_w0
  -- Stage 1b: WordToWord same-clock agreement at `k_word` (`wst0 -> wst`)
  obtain ⟨hbmS, hcodeS⟩ := fullMakeInit_bitmaps_code
    c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
    mc.target.config.addrOffset bitmaps p labst _ dataSp _ sst x hfmi
  have hinitS := panToTargetInitStateOk mc.target.config wprog bitmaps wconf fs p ltconf
    c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
    mc.target.config.addrOffset labst (fun k => decide (k ∈ mc.calleeSavedRegs)) dataSp
    sst x hmc.1 hcfg.2.2.2.1 hwts hfmi
  rw [Nat.add_comm mc.target.config.avoidRegs.length 5] at hinitS
  obtain ⟨hgc, -, -, -⟩ := panToTargetWordStateFacts
    mc.target.config k_reg (sptFromAList wprog) worac c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
    mc.target.config.addrOffset bitmaps p labst (fun k => decide (k ∈ mc.calleeSavedRegs))
    dataSp _ sst x hfmi
  have hne_w0 : res_w0 ≠ some .error := by
    intro herr; rw [herr] at hcw0; cases hcw0
  have hww := word_to_word_clocked_agree c.wordToWordConf mc.target.config
    (panToWordCompileProgHOL mc.target.config.isa panCode) col wprog wst0
    BvlToBvi.initGlobalsLocation k_word hwtw
    hgc
    (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_alloc_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl)
    (by simp [wst0, pipelineWordInitState, WordToStack.Native.Initialization.makeInit])
    rfl (by rw [hrun_w0]; exact hne_w0)
  rcases hrun_w : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { wst with clock := k_word } with ⟨res_w, s_w_post⟩
  have hres_w : res_w = res_w0 := by
    have h1 := hww.1
    change (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { wst with clock := k_word }).1 =
      (WordSemStateFiniteExact.evaluate
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
        { wst0 with clock := k_word }).1 at h1
    rw [hrun_w, hrun_w0] at h1
    exact h1
  have hffi_w_post : s_w_post.ffi = t_w0.ffi := by
    have h2 := hww.2
    change (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      { wst with clock := k_word }).2.ffi =
      (WordSemStateFiniteExact.evaluate
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
        { wst0 with clock := k_word }).2.ffi at h2
    rw [hrun_w, hrun_w0] at h2
    exact h2
  rw [hres_w] at hrun_w
  -- Stage 2: WordSem wst (at k_word) -> StackSem sst (at k_stack) via `word_to_stack_compile_halt_of_stack_not_timeOut`
  obtain ⟨hraise, hstore⟩ := panToTargetStubLocationsFree
    c.wordToWordConf mc.target.config panCode col wprog hisa hwtw
  have hconv := (BackendProof.compileToWordConventions2 c.wordToWordConf mc.target.config _ col
    wprog hwtw (fun _ _ => Or.inr hisa)).2.2
  have hsafe := panToTargetResourceLimitOfSemantics
    c mc ms panCode col wprog bitmaps wconf fs p stackMax worac hwtw hnodup hwts hmax hA hfmi
    (panToTargetLabRegWord mc ffi t _ _ _ ms _ (LabToTarget.compile mc.target.config) _ cbspace _ hgi.1 _ hmc.2.2.2.1)
    (panToTargetLabRegWord mc ffi t _ _ _ ms _ (LabToTarget.compile mc.target.config) _ cbspace _ hgi.1 _ hmc.2.2.2.2.1)
    (panToTargetLabRegWord mc ffi t _ _ _ ms _ (LabToTarget.compile mc.target.config) _ cbspace _ hgi.1 _ hmc.2.2.2.2.2.1)
    hlo hhi hheap hheapLt halign (hsemEq ▸ hfail) hresLimit
  rcases hrun_stack : StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { sst with clock := k_stack }) with ⟨res_stack, t_stack⟩
  have hnt_stack' : res_stack ≠ some .timeOut := by
    have h := hnt_stack
    rw [hrun_stack] at h
    exact h
  obtain ⟨hres_stack, hffi_stack⟩ :=
    word_to_stack_compile_halt_of_stack_not_timeOut
      mc.target.config wprog sst k_reg worac BvlToBvi.initGlobalsLocation k_word k_stack
      res_w0 s_w_post res_stack t_stack
      (by rw [hwts, hcodeS]) rfl hinitS hraise hstore (by rw [hwts, hbmS])
      (fun entry he => ⟨(hconv entry he).1, (hconv entry he).2.1⟩)
      hsafe hrun_w hne_w0 hnt_w0 hrun_stack hnt_stack'
  have hclass_stack : FlattenSemantics.stackEntryClass res_stack =
      CrepToLoopSemanticsRunRes.CompleteResult outcome := by
    rw [hres_stack]
    rcases res_w0 with _ | r_val
    · cases hcw0
    · cases r_val with
      | result ret_loc _ =>
        by_cases hloc : ret_loc = WordLocW.loc 1 0
        · subst hloc
          simp [wordEntryClass] at hcw0
          subst hcw0
          simp [FlattenSemantics.stackEntryClass, WordToStackProofs.CompCorrect.compileResult]
        · simp [wordEntryClass, hloc] at hcw0
      | notEnoughSpace =>
        simp [wordEntryClass] at hcw0
        subst hcw0
        rcases hmc.1 with rfl | rfl <;>
          simp [FlattenSemantics.stackEntryClass, WordToStackProofs.CompCorrect.compileResult]
      | finalFfi e_ffi =>
        simp [wordEntryClass] at hcw0
        subst hcw0
        simp [FlattenSemantics.stackEntryClass, WordToStackProofs.CompCorrect.compileResult]
      | exception _ _ | timeOut | «break» _ | «continue» _ | error =>
        simp [wordEntryClass] at hcw0
  -- Stage 3: StackSem sst (at k_stack) -> LabSem labst (at k_lab) via `full_make_init_halt_of_lab_not_timeOut`
  obtain ⟨hhalt_lab, hio_lab⟩ :=
    full_make_init_halt_of_lab_not_timeOut
      hfmi hA k_stack res_stack t_stack outcome hrun_stack hclass_stack k_lab hnt_lab
  refine ⟨hhalt_lab, ?_⟩
  rw [hio_lab, hffi_stack, hffi_w_post, hio_w0]

/-- Master integration theorem (`finite_certificate_of_source_to_target_clock_chain`):
reduces `InitE.Certificate (baselineWithFiniteK (bootstrapSteps + K_post)) (.finite (bootstrapSteps + K_post))`
directly to the 5-stage non-`.timeOut` clock chain
(`PanSem` at `k_pan` -> `WordSem` at `k_word` -> `StackSem` at `k_stack` -> `LabSem` at `k_lab` -> `Target` at `K_post`)
by composing `pan_to_word_halt_of_word_not_timeOut`, `word_to_stack_compile_halt_of_stack_not_timeOut`,
`full_make_init_halt_of_lab_not_timeOut`, and `finite_certificate_of_uniform_post_bootstrap_not_timeOut`. -/
theorem finite_certificate_of_source_to_target_clock_chain
    (oracles : List (Option (Spt Nat))) (c : Backend.Config) (depth K_post : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (k_pan k_word k_stack k_lab : Guest.InputBlob → Nat)
    (pan_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
          decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
            { sourceInitialState input with structs := stCtxt }
            (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
            sourceDeclarations = some s_decls →
          (PanSemStateFiniteExact.evaluateHOLFiniteState
            { s_decls with clock := k_pan input }
            (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut)
    (word_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (WordSemStateFiniteExact.evaluate
            (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
            { pipelinePanToWordInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf sourceDeclarations wprog
                InitECandidate.bitmaps p 0 with clock := k_word input }).1 ≠ some .timeOut)
    (stack_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (StackSemEvaluate.evaluate
            ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg 64),
              { pipelineStackInitState (oracleCompilerConfig oracles) baselineMachineConfig
                  (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                  InitECandidate.nativeCode 3788 ltconf InitECandidate.bitmaps p 0 with
                  clock := k_stack input })).1 ≠ some .timeOut)
    (lab_not_timeOut : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).1 ≠ .timeOut)
    (target_not_timeOut_of_lab_halt : ∀ (input : Guest.InputBlob),
      Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
      ∀ (outcome : HolOutcome) (events : List HolIoEvent),
        sourceBehaviour input = .terminate outcome events →
        coveredOutcome outcome →
        ∀ (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
          (bitmapsDm sdm : BitVec 64 → Bool)
          (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config),
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).1 = .halt outcome →
          (LabSem.evaluate
            { pipelineLabInitState (oracleCompilerConfig oracles) baselineMachineConfig
                (sourceFfi input) t m bitmapsDm sdm baselineInstalledState
                InitECandidate.nativeCode 3788 ltconf p with
                clock := k_lab input }).2.ffi.ioEvents = events →
          (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
            (bootstrapSteps + K_post) (baselineInitialState input)).1 ≠ .timeOut) :
    InitE.Certificate (baselineWithFiniteK (bootstrapSteps + K_post))
      (.finite (bootstrapSteps + K_post)) := by
  refine finite_certificate_of_uniform_post_bootstrap_not_timeOut
    oracles c depth K_post hlab compiled depthBound ?_
  intro input hgas outcome events source covered
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]; intro h; cases h
  have hsem := semanticsDecls_mainFirstHOL (sourceInitialState input) (ofString "main")
    (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have hterm : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations = .terminate outcome events :=
    hsem.trans source
  have nonfail' : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations ≠ HolBehaviour.fail := by
    rw [hterm]; intro h; cases h
  obtain ⟨stCtxt, s_decls, hst, hev_decls, -, -, -, -, -, -, -⟩ :=
    semanticsDecls_terminate_extract (sourceInitialState input) (ofString "main")
      sourceDeclarations outcome events hterm
  rcases hev_pan : PanSemStateFiniteExact.evaluateHOLFiniteState
      { s_decls with clock := k_pan input }
      (.call none (ofString "main") [] : ProgHOL 64) with ⟨res_src, s_src_post⟩
  have hnt_pan : res_src ≠ some .timeOut := by
    have h := pan_not_timeOut input hgas outcome events source covered stCtxt s_decls hst hev_decls
    rw [hev_pan] at h
    exact h
  obtain ⟨hclass_src, hio_src⟩ :=
    semanticsDecls_terminate_at_clock (sourceInitialState input) (ofString "main")
      sourceDeclarations outcome events hterm stCtxt s_decls hst hev_decls
      (k_pan input) res_src s_src_post hev_pan hnt_pan
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact YukonCleanVerifierCheck.baseline_pan_installed input
  have installed := oracle_baseline_installation input c hmem
  obtain ⟨hmc, _, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax_heap, hendian, hinstalled, hlimits⟩ := installed
  have hconfig : baselineMachineConfig.target.config = riscvConfig := by rw [hmc.1]; rfl
  have hcomp := compiled
  rw [← hconfig, compileProgMaxAsmExecutable_eq] at hcomp
  have hcfg := oracleBackendConfigOk oracles
  rw [← hconfig] at hcfg
  have hinit := oracleMachineInitOk oracles baselineMachineConfig hmc
  rw [← hconfig] at hinit
  have hprecise : optionLt (some depth)
      (some (readLimits baselineMachineConfig.target.config (oracleCompilerConfig oracles)
        baselineMachineConfig baselineInstalledState).1) = true := by
    change optionLt (some depth)
      (some (readLimits baselineMachineConfig.target.config pancakeRiscVBackendConfig
        baselineMachineConfig baselineInstalledState).1) = true
    rw [hlimits]
    simpa only [optionLt, decide_eq_true_eq] using
      (Nat.lt_of_le_of_lt depthBound oracle_stack_bound_fits)
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, _, rfl, hmax⟩ :=
    compileProgMax_some (oracleCompilerConfig oracles) baselineMachineConfig sourceDeclarations
      InitECandidate.nativeCode InitECandidate.bitmaps c (some depth) hcomp
  obtain ⟨t, m, bitmapPtr, bitmapsDm, sdm, hpm, hgi, hsdm, a1, a2, a3, hle, hbig, hdisj, m0, m1,
    m2, m3, m4, hstar, _, _⟩ := hinstalled
  have hpm' : ∀ a, decide ((sourceInitialState input).memaddrs a) = true →
      m a = wlabWlocExact ((sourceInitialState input).memory a) :=
    fun a h => hpm a (of_decide_eq_true h)
  have hsdm' : (fun a => decide ((sourceInitialState input).shMemaddrs a)) =
      fun a => sdm a && holByteAligned a := by
    funext a; rw [hsdm]; simp only [Bool.decide_and, Bool.decide_eq_true]
  obtain ⟨hhalt_lab, hio_lab⟩ :=
    source_to_lab_halt_of_stage_clock_chain
      (oracleCompilerConfig oracles) baselineMachineConfig (sourceFfi input)
      t m bitmapPtr bitmapsDm sdm baselineInstalledState
      InitECandidate.nativeCode 3788 ltconf sourceDeclarations col wprog
      InitECandidate.bitmaps wconf fs p 0 (some depth)
      (sourceInitialState input) (ofString "main") globalsWords baselineHeapLen
      hcfg (riscvMachineConfigOk baselineMachineConfig hmc) hinit
      (by rw [hconfig]; decide) hwtw hwts hmax sourceDistinctFunctions hgi
      ⟨a1, a2, a3, hle, hbig, hdisj, m0, m1, m2, m3, m4, hstar⟩
      hpm' hsdm' hbase hsplit
      (hadj2 ▸ hleft) (hadj4 ▸ hright) hmax_heap (oracleHeapLimit_lt oracles)
      haligned hendian rfl hlen hglobals hdomain htop rfl
      (by simpa only [sourceDeclarations, globalsWords] using sourceGlobalsSize.symm)
      sourceDistinctParams (source_globals_allocatable input)
      rfl rfl rfl sourceExceptionBound rfl nonfail' hprecise
      stCtxt s_decls hst hev_decls
      (k_pan input) (k_word input) (k_stack input) (k_lab input)
      res_src s_src_post outcome hev_pan hclass_src
      (word_not_timeOut input hgas outcome events source covered t m bitmapsDm sdm wprog p ltconf)
      (stack_not_timeOut input hgas outcome events source covered t m bitmapsDm sdm p ltconf)
      (lab_not_timeOut input hgas outcome events source covered t m bitmapsDm sdm p ltconf)
  exact target_not_timeOut_of_lab_halt input hgas outcome events source covered
    t m bitmapsDm sdm p ltconf hhalt_lab (hio_lab.trans hio_src)


end InitECandidate.Solver.SelfContainedPipelineBridge
