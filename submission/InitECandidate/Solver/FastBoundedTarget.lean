import InitE.Challenge
import InitECandidate.Solver.YukonSelfContainedCert
import Flapjack.Compiler.Backend.LabToTarget.MachineSemantics
import Flapjack.Compiler.Backend.LabToTarget.SemanticsCompileFinal
import Flapjack.Compiler.Backend.LabFilter.Proofs.Semantics
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMachineToLab

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


namespace InitE
open InitECandidate.Proofs
open InitECandidate.Solver.YukonSelfContainedCert
open Flapjack Flapjack.Misc Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget

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

/-- Two non-`.timeOut` `LabSem.evaluate` runs on the same state `s` (at clocks `k` and `k'`)
produce the exact same result and FFI state (`evaluateAddClock`). -/
theorem labEvaluateIgnoreClocks {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (k k' : Nat) (r1 r2 : MachineResult)
    (next1 next2 : Flapjack.Compiler.Backend.LabSem.State width C F)
    (h1 : LabSem.evaluate { s with clock := k } = (r1, next1))
    (hnt1 : r1 ≠ .timeOut)
    (h2 : LabSem.evaluate { s with clock := k' } = (r2, next2))
    (hnt2 : r2 ≠ .timeOut) :
    r1 = r2 ∧ next1.ffi = next2.ffi := by
  have ha1 := evaluateAddClock { s with clock := k } r1 next1 k' ⟨h1, hnt1⟩
  have ha2 := evaluateAddClock { s with clock := k' } r2 next2 k ⟨h2, hnt2⟩
  simp only [Nat.add_comm k' k] at ha2
  rw [ha1] at ha2
  injection ha2 with hr hnext
  have hffi := congrArg Flapjack.Compiler.Backend.LabSem.State.ffi hnext
  exact ⟨hr, hffi⟩

/-- Under `LabSem.semantics s = .terminate outcome events`, any clock `k` at which
`(LabSem.evaluate { s with clock := k }).1 ≠ .timeOut` is already a `.halt outcome`
witness with `ioEvents = events`! -/
theorem lab_halt_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (s : Flapjack.Compiler.Backend.LabSem.State width C F)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hsem : LabSem.semantics s = .terminate outcome events)
    (k : Nat)
    (hnt : (LabSem.evaluate { s with clock := k }).1 ≠ .timeOut) :
    (LabSem.evaluate { s with clock := k }).1 = .halt outcome ∧
      (LabSem.evaluate { s with clock := k }).2.ffi.ioEvents = events := by
  unfold LabSem.semantics at hsem
  by_cases herr : ∃ clock, (LabSem.evaluate { s with clock := clock }).1 = .error
  · rw [if_pos herr] at hsem; cases hsem
  · rw [if_neg herr] at hsem
    cases hsome : holOptionSome (fun result => ∃ clock next outcome,
        LabSem.evaluate { s with clock := clock } = (.halt outcome, next) ∧
        result = HolBehaviour.terminate outcome next.ffi.ioEvents) with
    | none => rw [hsome] at hsem; cases hsem
    | some result =>
      rw [hsome] at hsem
      subst hsem
      obtain ⟨k0, next0, out0, hrun0, heq⟩ := holOptionSome_some hsome
      injection heq with hout0 hev0
      subst hout0 hev0
      rcases hrun1 : LabSem.evaluate { s with clock := k } with ⟨r1, next1⟩
      rw [hrun1] at hnt
      obtain ⟨hr, hffi⟩ := labEvaluateIgnoreClocks s k k0 r1 (.halt outcome) next1 next0
        hrun1 hnt hrun0 (by simp)
      exact ⟨hr, congrArg HolFfiState.ioEvents hffi⟩

/-- Clock-preserving domain alignment (`alignDm` + `alignSdm`) and `filterSkip` bridge:
if the aligned unfiltered `LabSem` state halts at clock `k`, then the `filterSkip`-related
state `s` halts at the exact same clock `k` with the same outcome and FFI state. -/
theorem lab_filter_align_clocked_halt {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width)
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hr : LabFilter.Proofs.stateRel s t)
    (k : Nat) (outcome : HolOutcome)
    (next : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hhalt : LabSem.evaluate { alignDm (alignSdm t) with clock := k } = (.halt outcome, next)) :
    (LabSem.evaluate { s with clock := k }).1 = .halt outcome ∧
      (LabSem.evaluate { s with clock := k }).2.ffi = next.ffi := by
  have hdm : LabSem.evaluate { alignDm (alignSdm t) with clock := k } =
      ((LabSem.evaluate { alignSdm t with clock := k }).1,
        alignDm (LabSem.evaluate { alignSdm t with clock := k }).2) := by
    change LabSem.evaluate (alignDm { alignSdm t with clock := k }) = _
    have h := evaluateAlignDM hw { alignSdm t with clock := k }
    cases he : LabSem.evaluate { alignSdm t with clock := k }
    simpa only [he] using h
  have hsdm : LabSem.evaluate { alignSdm t with clock := k } =
      ((LabSem.evaluate { t with clock := k }).1,
        alignSdm (LabSem.evaluate { t with clock := k }).2) := by
    change LabSem.evaluate (alignSdm { t with clock := k }) = _
    have h := evaluateAlignSDM hw { t with clock := k }
    cases he : LabSem.evaluate { t with clock := k }
    simpa only [he] using h
  rw [hsdm] at hdm
  rw [hhalt] at hdm
  have hres_t : (LabSem.evaluate { t with clock := k }).1 = .halt outcome :=
    (congrArg Prod.fst hdm).symm
  have hffi_t : (LabSem.evaluate { t with clock := k }).2.ffi = next.ffi := by
    have h2 := congrArg Prod.snd hdm
    have hffi := congrArg Flapjack.Compiler.Backend.LabSem.State.ffi h2
    exact hffi.symm
  have hrc : LabFilter.Proofs.stateRel { s with clock := k } { t with clock := k } := by
    rcases hr with ⟨⟨compile, hs, hcomp⟩, hf⟩
    subst s
    exact ⟨⟨compile, rfl, hcomp⟩, hf⟩
  obtain ⟨extra, t2, he, hf⟩ := LabFilter.Proofs.filterCorrect
    { s with clock := k } { t with clock := k }
    (LabSem.evaluate { s with clock := k }).1
    (LabSem.evaluate { s with clock := k }).2
    ⟨rfl, hrc, hrc.2⟩
  have hnt : (LabSem.evaluate { t with clock := k }).1 ≠ .timeOut := by
    rw [hres_t]
    intro h
    cases h
  have hadd := evaluateAddClock { t with clock := k }
    (LabSem.evaluate { t with clock := k }).1
    (LabSem.evaluate { t with clock := k }).2 extra
    ⟨rfl, hnt⟩
  rw [hadd] at he
  constructor
  · exact (congrArg Prod.fst he).symm.trans hres_t
  · have ht2 : (LabSem.evaluate { t with clock := k }).2.ffi = t2.ffi :=
      congrArg (fun p => p.2.ffi) he
    rw [hf, ← ht2]
    exact hffi_t

/-- Clocked `LabToTarget.compileCorrect` bridge: a halting `LabSem` evaluation at clock `k`
yields a halting target execution at clock `k + extra` with the same outcome and FFI state. -/
theorem lab_to_target_clocked_halt {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (p : BitVec width) (ms : S)
    (s : Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config F)
    (hencoder : encoderCorrect mc.target)
    (hinit : initOk (mc, p) s ms)
    (k : Nat) (outcome : HolOutcome)
    (hhalt : (LabSem.evaluate { s with clock := k }).1 = .halt outcome) :
    ∃ extra ms2,
      evaluateTargetHOL mc s.ffi (k + extra) ms =
        (.halt outcome, ms2, (LabSem.evaluate { s with clock := k }).2.ffi) := by
  obtain ⟨code2, labs, t1, hrel, htie⟩ := hinit
  generalize hev : LabSem.evaluate { s with clock := k } = run
  rcases run with ⟨result, next⟩
  have hres : result = .halt outcome := by
    rw [hev] at hhalt
    exact hhalt
  subst hres
  have hnoterr : (MachineResult.halt outcome : MachineResult) ≠ .error := by
    intro h
    cases h
  obtain ⟨extra, _, ms2, htarget⟩ := LabToTarget.compileCorrect (T := Unit) p
    { s with clock := k } (.halt outcome) mc next code2 labs t1 ms
    ⟨oracleTie_clock mc ms s k htie, hev, hnoterr, hencoder,
      stateRelClock (mc, code2, labs, p) s t1 ms k hrel⟩
  exact ⟨extra, ms2, htarget⟩

/-- Clocked `LabToTarget.semanticsMakeInit` bridge: under the 14 `makeInit_initOk` hypotheses,
a halting `LabSem` evaluation at clock `k` yields a halting target execution at clock `k + extra`. -/
theorem lab_to_target_make_init_clocked_halt {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (ms : S) (ffi : HolFfiState F)
    (code code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → LabToTarget.Config × LabProgHOL width)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum)
    (hencoder : encoderCorrect mc.target)
    (hgood : goodCode mc.target.config (.ln : Spt (Spt Nat)) code)
    (hmc : mcConfOk mc)
    (horacle : noShareMemInst code → compilerOracleOk coracle labs (progToBytes code2).length
      mc.target.config mc.ffiNames)
    (hffis : listSubset ((findFfiNames code).filter (fun x => match x with
      | .extCall _ => true | _ => false)) (mc.ffiNames.take i) = true)
    (hremove : removeLabels clock mc.target.config 0 .ln (mc.ffiNames.take i) code =
      some (code2, labs))
    (hinit : goodInitState mc ms (progToBytes code2) cbspace t m dm sdm)
    (hinfo : getShmemInfo code2 0 [] [] = (newFfiNames, shmemInfo))
    (hoff : newShmemInfo = shmemInfo.map (fun rec => { rec with
      entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
      exitPc := (mc.target.getPc ms).toNat + rec.exitPc }))
    (hdrop : mc.ffiNames.drop i = newFfiNames)
    (hboundary : mmioPcsMinIndex mc.ffiNames = some i)
    (hentries : newShmemInfo.map ShmemInfoNum.entryPc = (mc.ffiEntryPcs.map BitVec.toNat).drop i)
    (hmmio : mc.mmioInfo = List.zip ((List.range newShmemInfo.length).map (fun index => index + i))
      (newShmemInfo.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff), rec.reg,
        BitVec.ofNat width rec.exitPc))))
    (hsafe : noInstallOrNoShareMem code mc.ffiNames)
    (hbuffer : ∀ bn, bn < cbspace → BitVec.ofNat width bn +
      BitVec.ofNat width (progToBytes code2).length + mc.target.getPc ms ∉ mc.ffiEntryPcs.take i)
    (k : Nat) (outcome : HolOutcome)
    (hhalt : (LabSem.evaluate { makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle with
        clock := k }).1 = .halt outcome) :
    ∃ extra ms2,
      evaluateTargetHOL mc ffi (k + extra) ms =
        (.halt outcome, ms2,
          (LabSem.evaluate { makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
            (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle with
              clock := k }).2.ffi) := by
  have hentry := makeInit_initOk mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle newFfiNames shmemInfo newShmemInfo
    ⟨hgood, hmc, horacle, hffis, hremove, hinit, hinfo, hoff, hdrop, hboundary,
      hentries, hmmio, hsafe, hbuffer⟩
  exact lab_to_target_clocked_halt mc (mc.target.getPc ms) ms
    (makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle)
    hencoder hentry k outcome hhalt

private theorem goodCodeFiltered_local {width : Nat} [NeZero width] {G : Type}
    (config : AsmConfigExact width) (labels : Spt (Spt G)) (code : LabProgHOL width) :
    goodCode config labels code → goodCode config labels (filterSkip code) := by
  rintro ⟨hend, hsec, hdistinct, hlabels, hdisjoint, htargets, hpre⟩
  refine ⟨Flapjack.Compiler.Backend.LabFilter.Proofs.secEndsWithLabelFilterSkip code hend,
    ?_, ?_, ?_, ?_, ?_, allEncOkPreFilterSkip code config hpre⟩
  · intro sectionData hmem line hline
    rw [filterSkipMap] at hmem
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmem
    exact hsec original horiginal line (List.mem_filter.mp hline).1
  · simpa only [mapSectionNumFilterSkip] using hdistinct
  · intro sectionData hmem
    have hlabelsMem : LabProps.LabelSets.extractLabels sectionData.lines ∈
        (filterSkip code).map
          (fun s => LabProps.LabelSets.extractLabels (LabLang.Section.lines s)) :=
      List.mem_map.mpr ⟨sectionData, hmem, rfl⟩
    rw [filterSkipExtractLabels] at hlabelsMem
    obtain ⟨original, horiginal, heq⟩ := List.mem_map.mp hlabelsMem
    rw [← heq]
    exact hlabels original horiginal
  · simpa only [mapSectionNumFilterSkip] using hdisjoint
  · simpa only [getLabelsFilterSkip, getCodeLabelsFilterSkip] using htargets

private theorem successfulIndex_local {α : Type} [DecidableEq α] (values : List α)
    (target : α) (offset index : Nat) (h : findIndex target values offset = some index) :
    ∃ i, ∃ hi : i < values.length, index = offset + i ∧ values[i]'hi = target := by
  induction values generalizing offset with
  | nil => simp [findIndex] at h
  | cons head tail ih =>
    by_cases he : head = target
    · have hs : offset = index := by simpa only [findIndex, if_pos he, Option.some.injEq] using h
      exact ⟨0, by simp, by omega, he⟩
    · have ht : findIndex target tail (offset + 1) = some index := by
        simpa only [findIndex, if_neg he] using h
      obtain ⟨i, hi, hindex, hvalue⟩ := ih (offset + 1) ht
      exact ⟨i + 1, by simp; omega, by omega, by simpa using hvalue⟩

private theorem bufferNotFfi_local {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (pc : BitVec width) (size space i : Nat)
    (hstart : startPcOk mc pc) (hboundary : mmioPcsMinIndex mc.ffiNames = some i)
    (hbound : space + size + ffiOffset * (i + 3) < 2 ^ width) :
    ∀ bn, bn < space → BitVec.ofNat width bn + BitVec.ofNat width size + pc ∉
      mc.ffiEntryPcs.take i := by
  obtain ⟨_, _, _, _, _, _, _, boundary, hindex, hprefix, _, _⟩ := hstart
  have hi : boundary = i := Option.some.inj (hindex.symm.trans hboundary)
  subst boundary
  intro bn hbn hmem
  obtain ⟨j, hj, hvalue⟩ := List.mem_take_iff_getElem.mp hmem
  have hji : j < i := by omega
  have hfind := (hprefix j hji).2.2.2.2
  obtain ⟨found, hfound, hreturned, hentry⟩ := successfulIndex_local mc.ffiEntryPcs
    (pc - BitVec.ofNat width ((3 + j) * ffiOffset)) 0 j hfind
  have hfj : found = j := by omega
  subst found
  have he : BitVec.ofNat width bn + BitVec.ofNat width size + pc =
      pc - BitVec.ofNat width ((3 + j) * ffiOffset) := hvalue.symm.trans hentry
  have hs : (BitVec.ofNat width bn + BitVec.ofNat width size +
      BitVec.ofNat width ((3 + j) * ffiOffset)) + pc = pc := by
    calc
      _ = (BitVec.ofNat width bn + BitVec.ofNat width size + pc) +
          BitVec.ofNat width ((3 + j) * ffiOffset) := by ac_rfl
      _ = (pc - BitVec.ofNat width ((3 + j) * ffiOffset)) +
          BitVec.ofNat width ((3 + j) * ffiOffset) := congrArg (fun x => x + _) he
      _ = pc := BitVec.sub_add_cancel _ _
  have hz := congrArg (fun x => x - pc) hs
  simp only [BitVec.add_sub_cancel, BitVec.sub_self] at hz
  have hzNat := congrArg BitVec.toNat hz
  have hlt : bn + size + (3 + j) * ffiOffset < 2 ^ width := by
    simp only [ffiOffset] at hbound ⊢
    omega
  rw [← BitVec.ofNat_add, ← BitVec.ofNat_add, BitVec.toNat_ofNat] at hzNat
  simp only [BitVec.toNat_zero, Nat.mod_eq_of_lt hlt] at hzNat
  simp only [ffiOffset] at hzNat
  omega

/-- Clocked `LabToTarget.semanticsCompile` bridge: under the 15 `semanticsCompile` hypotheses,
if the aligned unfiltered `LabSem` state halts at clock `k`, then the target machine halts
at clock `k + extra` with the same outcome and FFI state. -/
theorem lab_to_target_compile_clocked_halt {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (ms : S)
    (code : LabProgHOL width) (asmConf : AsmConfigExact width) (c cNext : LabToTarget.Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → LabToTarget.Config × LabProgHOL width)
    (hmc : mcConfOk mc)
    (horacle : noShareMemInst code → compilerOracleOk coracle cNext.labels bytes.length
      asmConf mc.ffiNames)
    (hgood : goodCode asmConf c.labels code)
    (hasm : asmConf = mc.target.config)
    (hlabs : c.labels = .ln)
    (hpos : c.pos = 0)
    (hcompile : LabToTarget.compile asmConf c code = some (bytes, cNext))
    (hffi : cNext.ffiNames = some mc.ffiNames)
    (hinit : goodInitState mc ms bytes cbspace t m dm sdm)
    (hboundary : mmioPcsMinIndex mc.ffiNames = some i)
    (hentries : cNext.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
      (mc.ffiEntryPcs.map BitVec.toNat).drop i)
    (hmmio : mc.mmioInfo = List.zip ((List.range cNext.shmemExtra.length).map (fun index => index + i))
      (cNext.shmemExtra.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff), rec.reg,
        BitVec.ofNat width rec.exitPc + mc.target.getPc ms))))
    (hsafe : noInstallOrNoShareMem code mc.ffiNames)
    (hbound : cbspace + bytes.length + ffiOffset * (i + 3) < 2 ^ width)
    (hprovided : ∀ ffis, c.ffiNames = some ffis → ∀ name ∈ ffis, ∃ s, name = .extCall s)
    (k : Nat) (outcome : HolOutcome)
    (next : Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config F)
    (hhalt : LabSem.evaluate { makeInit mc ffi t m (fun a => dm a && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms code (LabToTarget.compile asmConf)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle with
        clock := k } = (.halt outcome, next)) :
    ∃ extra ms2,
      evaluateTargetHOL mc ffi (k + extra) ms = (.halt outcome, ms2, next.ffi) := by
  subst hasm
  let tUnaligned := makeInit mc ffi t m dm sdm ms code (LabToTarget.compile mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle
  let sFiltered := makeInit mc ffi t m dm sdm ms (filterSkip code)
    (compileLab mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
    (fun n => ((coracle n).1, filterSkip (coracle n).2))
  have hr : LabFilter.Proofs.stateRel sFiltered tUnaligned := by
    refine ⟨⟨compileLab mc.target.config, ?_, rfl⟩, rfl⟩
    have hadj : LabFilter.Proofs.adjustPc tUnaligned.pc tUnaligned.code = tUnaligned.pc := by
      rw [show tUnaligned.pc = 0 from rfl, LabFilter.Proofs.adjustPc.eq_def]
      simp
    rw [hadj]
    rfl
  obtain ⟨hhalt_s, hffi_s⟩ := lab_filter_align_clocked_halt hmc.1 sFiltered tUnaligned hr
    k outcome next hhalt
  have hgoodNat : goodCode mc.target.config (.ln : Spt (Spt Nat)) code := by
    simpa only [hlabs] using hgood
  have hcomp := hcompile
  simp only [LabToTarget.compile, compileLab, hlabs, hpos] at hcomp
  generalize hchoice : (match c.ffiNames with
    | some names => (names, listSubset (findFfiNames (filterSkip code)) names)
    | none => (findFfiNames (filterSkip code), true)) = choice at hcomp
  rcases choice with ⟨ffis, ffisOk⟩
  let finish (names : List HolFfiName) (ok : Bool) :=
    if ok then
      match removeLabels c.initClock mc.target.config 0 .ln names (filterSkip code) with
      | none => none
      | some (output, labs) =>
          let (newNames, info) := getShmemInfo output 0 [] []
          some (progToBytes output, { c with
            labels := labs
            pos := (progToBytes output).length + 0
            secPosLen := getSymbols 0 output
            ffiNames := some (names ++ newNames)
            shmemExtra := info })
    else none
  have hfinished : finish ffis ffisOk = some (bytes, cNext) := by
    cases hcfg : c.ffiNames with
    | none =>
      simp only [hcfg, Prod.mk.injEq] at hchoice
      rw [← hchoice.1, ← hchoice.2]
      cases hr : removeLabels c.initClock mc.target.config 0 .ln
          (findFfiNames (filterSkip code)) (filterSkip code) <;>
        simpa only [finish, hcfg, hr] using hcomp
    | some supplied =>
      simp only [hcfg, Prod.mk.injEq] at hchoice
      rw [← hchoice.1, ← hchoice.2]
      cases hr : removeLabels c.initClock mc.target.config 0 .ln supplied
          (filterSkip code) <;>
        simpa only [finish, hcfg, hr] using hcomp
  clear hcomp
  have hcomp := hfinished
  dsimp only [finish] at hcomp
  by_cases hok : ffisOk = true
  · simp only [hok, ↓reduceIte] at hcomp
    cases hremove : removeLabels c.initClock mc.target.config 0 .ln ffis
        (filterSkip code) with
    | none => simp only [hremove, reduceCtorEq] at hcomp
    | some output =>
      rcases output with ⟨code2, labs⟩
      simp only [hremove] at hcomp
      cases hinfo : getShmemInfo code2 0 [] [] with
      | mk newNames info =>
        simp only [hinfo, Option.some.injEq, Prod.mk.injEq] at hcomp
        obtain ⟨rfl, rfl⟩ := hcomp
        have hnames : mc.ffiNames = ffis ++ newNames := by
          simpa only [Option.some.injEq] using hffi.symm
        have hffis : ∀ name ∈ ffis, ∃ s, name = HolFfiName.extCall s := by
          cases hcfg : c.ffiNames with
          | none =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact findFfiNamesEvery (filterSkip code) _ rfl
          | some supplied =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact hprovided supplied hcfg
        have hnew : ∀ name ∈ newNames, ∀ s, name ≠ HolFfiName.extCall s := by
          obtain ⟨suffix, heq, hshared⟩ := getShmemInfo_mappedNames code2 0 [] [] newNames info hinfo
          simp only [List.nil_append] at heq
          rw [heq]
          intro name hmem s
          obtain ⟨op, rfl⟩ := hshared name hmem
          intro heq
          cases heq
        have hb : mmioPcsMinIndex mc.ffiNames = some ffis.length := by
          rw [hnames]
          exact mmioPcsMinIndex_append newNames ffis ⟨hnew, hffis⟩
        have hilen : i = ffis.length := Option.some.inj (hboundary.symm.trans hb)
        have htake : mc.ffiNames.take i = ffis := by
          rw [hnames, hilen, List.take_append_length]
        have hdrop : mc.ffiNames.drop i = newNames := by
          rw [hnames, hilen, List.drop_append_length]
        have hsubset : listSubset (findFfiNames (filterSkip code)) ffis = true := by
          cases hcfg : c.ffiNames with
          | none =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact listSubsetRefl _
          | some supplied =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact hchoice.2.trans hok
        let shiftedInfo := info.map (fun rec => { rec with
          entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
          exitPc := (mc.target.getPc ms).toNat + rec.exitPc })
        obtain ⟨extra, ms2, htarget⟩ := lab_to_target_make_init_clocked_halt mc ms ffi
          (filterSkip code) code2 labs c.initClock i cbspace t m dm sdm
          (fun n => ((coracle n).1, filterSkip (coracle n).2))
          newNames info shiftedInfo
          hmc.2.1 (goodCodeFiltered_local _ _ _ hgoodNat) hmc
          (by
            intro hno
            obtain ⟨hall, hzero⟩ := horacle ((noShareMemFilterSkip code).mp hno)
            refine ⟨?_, hzero⟩
            intro k'
            exact ⟨goodCodeFiltered_local _ _ _ (hall k').1,
              (noShareMemFilterSkip (coracle k').2).mpr (hall k').2⟩)
          (by
            rw [htake]
            simp only [listSubset, List.all_eq_true, decide_eq_true_eq] at hsubset ⊢
            intro name hmem
            exact hsubset name (List.mem_filter.mp hmem).1)
          (by simpa only [htake] using hremove)
          hinit hinfo rfl hdrop hboundary
          (by simpa only [shiftedInfo, List.map_map, Function.comp_def] using hentries)
          (by simpa only [shiftedInfo, List.length_map, List.map_map, Function.comp_def,
              BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm] using hmmio)
          (noInstallOrNoShareMemFilterSkip code mc.ffiNames hsafe)
          (by
            have hstart : startPcOk mc (mc.target.getPc ms) := by
              rw [← hinit.2.2.1]
              exact hinit.2.2.2.1
            exact bufferNotFfi_local mc _ _ cbspace i hstart hboundary hbound)
          k outcome hhalt_s
        rw [hffi_s] at htarget
        exact ⟨extra, ms2, htarget⟩
  · simp only [hok, ↓reduceIte, reduceCtorEq] at hcomp

/-- Clocked `panToTargetMachineLabSource` (stage A4): under the stage A4 hypotheses,
if the initial `labst` halts at clock `k` with `(.halt outcome, next)`, then the target
machine halts at clock `k + extra` with the same outcome and FFI state. -/
theorem pan_to_target_machine_lab_clocked_halt {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S) (bytes : List (BitVec 8)) (cbspace : Nat)
    (panCode : List (Pancake.PanLang.DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (ltconf : LabToTarget.Config)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hlab : LabToTarget.compile mc.target.config c.labConf
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p) = some (bytes, ltconf))
    (hnodup : ((Pancake.PanLang.functionsHOL panCode).map Prod.fst).Nodup)
    (hffiOk : match c.labConf.ffiNames with
      | none => True
      | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s)
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hffi : ltconf.ffiNames = some mc.ffiNames)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff),
            rec.reg, BitVec.ofNat width rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + ffiOffset * (i + 3) < 2 ^ width)
    (hsource : pancakeGoodCodeHOL panCode = true)
    (k : Nat) (outcome : HolOutcome)
    (next : Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config σ)
    (hhalt : LabSem.evaluate {
      (let regNames := c.stackConf.regNames
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
           mc.target.config.addrOffset sp []))) with clock := k } = (.halt outcome, next)) :
    ∃ extra ms2,
      evaluateTargetHOL mc ffi (k + extra) ms = (.halt outcome, ms2, next.ffi) := by
  have hpos : c.labConf.pos = 0 := hcfg.2.2.2.2.1
  have hlabels : c.labConf.labels = .ln := hcfg.2.2.2.2.2.1
  obtain ⟨ffis, hffis, i, hi⟩ := BackendProof.compileLabIMPMmioPcsMinIndex mc.target.config
    c.labConf _ bytes ltconf ⟨hlab, hffiOk⟩
  rw [hffi] at hffis
  cases hffis
  obtain ⟨hshm, hmmioI, hbound⟩ := hmmio i hi
  have horacle := panToTargetCompilerOracleOk mc.target.config c.labConf ltconf _ bytes
    mc.ffiNames c.stackConf.regNames c.stackConf.jump mc.target.config.addrOffset
    (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)) hlab hpos hffi
  have hnis := panToTargetNoInstallOrNoShareMem panCode mc.target.config mc.target.config.isa _
    c.wordToWordConf col wprog bitmaps wconf fs p c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
    mc.target.config.addrOffset mc.ffiNames ⟨hnodup, hisa, rfl, hwtw, hwts⟩
  have hgc := panToTargetGoodCodeFromSource (β := Nat) c mc panCode col wprog bitmaps wconf fs p
    hcfg hmc.1 hisa hwtw hwts hnodup hsource
  exact lab_to_target_compile_clocked_halt mc ffi ms _ mc.target.config c.labConf ltconf bytes
    cbspace i t m _ sdm _ hmc (fun _ => horacle) (by rw [hlabels]; exact hgc) rfl hlabels hpos
    hlab hffi hgi hi hshm hmmioI hnis hbound
    (fun ffis h => by rw [h] at hffiOk; exact hffiOk) k outcome next hhalt

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

/-- Same-clock `LabToTarget` non-timeout run agreement: if the target machine does not time out
at clock `K` and `LabSem.evaluate` does not error at clock `K`, then `LabSem.evaluate` at clock `K`
produces the exact same result and FFI state as the target machine at clock `K`! -/
theorem lab_to_target_run_agree_of_not_timeOut {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (p : BitVec width) (ms : S)
    (s : Flapjack.Compiler.Backend.LabSem.State width LabToTarget.Config F)
    (hencoder : encoderCorrect mc.target)
    (hinit : initOk (mc, p) s ms)
    (K : Nat)
    (hne : (LabSem.evaluate { s with clock := K }).1 ≠ .error)
    (hnt : (evaluateTargetHOL mc s.ffi K ms).1 ≠ .timeOut) :
    (LabSem.evaluate { s with clock := K }).1 = (evaluateTargetHOL mc s.ffi K ms).1 ∧
      (LabSem.evaluate { s with clock := K }).2.ffi = (evaluateTargetHOL mc s.ffi K ms).2.2 := by
  obtain ⟨code2, labs, t1, hrel, htie⟩ := hinit
  rcases hev : LabSem.evaluate { s with clock := K } with ⟨res_lab, next_lab⟩
  have hres_ne : res_lab ≠ .error := by
    rw [hev] at hne
    exact hne
  obtain ⟨extra, _, ms2, htarget⟩ := LabToTarget.compileCorrect (T := Unit) p
    { s with clock := K } res_lab mc next_lab code2 labs t1 ms
    ⟨oracleTie_clock mc ms s K htie, hev, hres_ne, hencoder,
      stateRelClock (mc, code2, labs, p) s t1 ms K hrel⟩
  rcases hrunK : evaluateTargetHOL mc s.ffi K ms with ⟨res_t, ms_t, ffi_t⟩
  rw [hrunK] at hnt
  have hadd := evaluateTargetAddClock mc s.ffi K ms extra res_t ms_t ffi_t hrunK hnt
  rw [hadd] at htarget
  injection htarget with hres hrest
  injection hrest with _ hffi
  exact ⟨hres.symm, hffi.symm⟩

/-- Same-clock `alignDm`/`alignSdm` + `filterSkip` non-timeout run agreement:
if the aligned unfiltered `LabSem` state `alignDm (alignSdm t)` does not time out at clock `k`,
then the `filterSkip`-related `LabSem` state `s` at clock `k` has the exact same result and
FFI state as `alignDm (alignSdm t)` at clock `k`! -/
theorem lab_filter_align_run_agree_of_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (hw : goodDimindex width)
    (s t : Flapjack.Compiler.Backend.LabSem.State width C F)
    (hr : LabFilter.Proofs.stateRel s t)
    (k : Nat)
    (hnt : (LabSem.evaluate { alignDm (alignSdm t) with clock := k }).1 ≠ .timeOut) :
    (LabSem.evaluate { s with clock := k }).1 =
      (LabSem.evaluate { alignDm (alignSdm t) with clock := k }).1 ∧
    (LabSem.evaluate { s with clock := k }).2.ffi =
      (LabSem.evaluate { alignDm (alignSdm t) with clock := k }).2.ffi := by
  have hdm : LabSem.evaluate { alignDm (alignSdm t) with clock := k } =
      ((LabSem.evaluate { alignSdm t with clock := k }).1,
        alignDm (LabSem.evaluate { alignSdm t with clock := k }).2) := by
    change LabSem.evaluate (alignDm { alignSdm t with clock := k }) = _
    have h := evaluateAlignDM hw { alignSdm t with clock := k }
    cases he : LabSem.evaluate { alignSdm t with clock := k }
    simpa only [he] using h
  have hsdm : LabSem.evaluate { alignSdm t with clock := k } =
      ((LabSem.evaluate { t with clock := k }).1,
        alignSdm (LabSem.evaluate { t with clock := k }).2) := by
    change LabSem.evaluate (alignSdm { t with clock := k }) = _
    have h := evaluateAlignSDM hw { t with clock := k }
    cases he : LabSem.evaluate { t with clock := k }
    simpa only [he] using h
  have hres_align : (LabSem.evaluate { alignDm (alignSdm t) with clock := k }).1 =
      (LabSem.evaluate { t with clock := k }).1 := by
    rw [hdm, hsdm]
  have hffi_align : (LabSem.evaluate { alignDm (alignSdm t) with clock := k }).2.ffi =
      (LabSem.evaluate { t with clock := k }).2.ffi := by
    rw [hdm, hsdm]
    rfl
  have hrc : LabFilter.Proofs.stateRel { s with clock := k } { t with clock := k } := by
    rcases hr with ⟨⟨compile, hs, hcomp⟩, hf⟩
    subst s
    exact ⟨⟨compile, rfl, hcomp⟩, hf⟩
  obtain ⟨extra, t2, he, hf⟩ := LabFilter.Proofs.filterCorrect
    { s with clock := k } { t with clock := k }
    (LabSem.evaluate { s with clock := k }).1
    (LabSem.evaluate { s with clock := k }).2
    ⟨rfl, hrc, hrc.2⟩
  have hnt_t : (LabSem.evaluate { t with clock := k }).1 ≠ .timeOut :=
    hres_align ▸ hnt
  have hadd := evaluateAddClock { t with clock := k }
    (LabSem.evaluate { t with clock := k }).1
    (LabSem.evaluate { t with clock := k }).2 extra
    ⟨rfl, hnt_t⟩
  rw [hadd] at he
  constructor
  · exact (congrArg Prod.fst he).symm.trans hres_align.symm
  · have ht2 : (LabSem.evaluate { t with clock := k }).2.ffi = t2.ffi :=
      congrArg (fun p => p.2.ffi) he
    rw [hf, ← ht2]
    exact hffi_align.symm

/-- Same-clock `LabToTarget.semanticsMakeInit` non-timeout run agreement:
if the target machine does not time out at clock `K` and `LabSem.evaluate` does not error
at clock `K`, then `LabSem.evaluate` on `makeInit` at clock `K` produces the exact same
result and FFI state as the target machine at clock `K`. -/
theorem lab_to_target_make_init_run_agree_of_not_timeOut {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (ms : S) (ffi : HolFfiState F)
    (code code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → LabToTarget.Config × LabProgHOL width)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum)
    (hencoder : encoderCorrect mc.target)
    (hgood : goodCode mc.target.config (.ln : Spt (Spt Nat)) code)
    (hmc : mcConfOk mc)
    (horacle : noShareMemInst code → compilerOracleOk coracle labs (progToBytes code2).length
      mc.target.config mc.ffiNames)
    (hffis : listSubset ((findFfiNames code).filter (fun x => match x with
      | .extCall _ => true | _ => false)) (mc.ffiNames.take i) = true)
    (hremove : removeLabels clock mc.target.config 0 .ln (mc.ffiNames.take i) code =
      some (code2, labs))
    (hinit : goodInitState mc ms (progToBytes code2) cbspace t m dm sdm)
    (hinfo : getShmemInfo code2 0 [] [] = (newFfiNames, shmemInfo))
    (hoff : newShmemInfo = shmemInfo.map (fun rec => { rec with
      entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
      exitPc := (mc.target.getPc ms).toNat + rec.exitPc }))
    (hdrop : mc.ffiNames.drop i = newFfiNames)
    (hboundary : mmioPcsMinIndex mc.ffiNames = some i)
    (hentries : newShmemInfo.map ShmemInfoNum.entryPc = (mc.ffiEntryPcs.map BitVec.toNat).drop i)
    (hmmio : mc.mmioInfo = List.zip ((List.range newShmemInfo.length).map (fun index => index + i))
      (newShmemInfo.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff), rec.reg,
        BitVec.ofNat width rec.exitPc))))
    (hsafe : noInstallOrNoShareMem code mc.ffiNames)
    (hbuffer : ∀ bn, bn < cbspace → BitVec.ofNat width bn +
      BitVec.ofNat width (progToBytes code2).length + mc.target.getPc ms ∉ mc.ffiEntryPcs.take i)
    (K : Nat)
    (hne : (LabSem.evaluate { makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle with
        clock := K }).1 ≠ .error)
    (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    (LabSem.evaluate { makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle with
        clock := K }).1 = (evaluateTargetHOL mc ffi K ms).1 ∧
    (LabSem.evaluate { makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle with
        clock := K }).2.ffi = (evaluateTargetHOL mc ffi K ms).2.2 := by
  have hentry := makeInit_initOk mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle newFfiNames shmemInfo newShmemInfo
    ⟨hgood, hmc, horacle, hffis, hremove, hinit, hinfo, hoff, hdrop, hboundary,
      hentries, hmmio, hsafe, hbuffer⟩
  exact lab_to_target_run_agree_of_not_timeOut mc (mc.target.getPc ms) ms
    (makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle)
    hencoder hentry K hne hnt

/-- Same-clock `LabToTarget.semanticsCompile` non-timeout run agreement:
if the target machine does not time out at clock `K` and the aligned unfiltered `LabSem`
state does not error at clock `K`, then the aligned unfiltered `LabSem` state at clock `K`
produces the exact same result and FFI state as the target machine at clock `K`! -/
theorem lab_to_target_compile_run_agree_of_not_timeOut {width : Nat} [NeZero width] {S Q F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (ms : S)
    (code : LabProgHOL width) (asmConf : AsmConfigExact width) (c cNext : LabToTarget.Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → LabToTarget.Config × LabProgHOL width)
    (hmc : mcConfOk mc)
    (horacle : noShareMemInst code → compilerOracleOk coracle cNext.labels bytes.length
      asmConf mc.ffiNames)
    (hgood : goodCode asmConf c.labels code)
    (hasm : asmConf = mc.target.config)
    (hlabs : c.labels = .ln)
    (hpos : c.pos = 0)
    (hcompile : LabToTarget.compile asmConf c code = some (bytes, cNext))
    (hffi : cNext.ffiNames = some mc.ffiNames)
    (hinit : goodInitState mc ms bytes cbspace t m dm sdm)
    (hboundary : mmioPcsMinIndex mc.ffiNames = some i)
    (hentries : cNext.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
      (mc.ffiEntryPcs.map BitVec.toNat).drop i)
    (hmmio : mc.mmioInfo = List.zip ((List.range cNext.shmemExtra.length).map (fun index => index + i))
      (cNext.shmemExtra.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff), rec.reg,
        BitVec.ofNat width rec.exitPc + mc.target.getPc ms))))
    (hsafe : noInstallOrNoShareMem code mc.ffiNames)
    (hbound : cbspace + bytes.length + ffiOffset * (i + 3) < 2 ^ width)
    (hprovided : ∀ ffis, c.ffiNames = some ffis → ∀ name ∈ ffis, ∃ s, name = .extCall s)
    (K : Nat)
    (hne : ∀ k, (LabSem.evaluate { makeInit mc ffi t m (fun a => dm a && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms code (LabToTarget.compile asmConf)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle with
        clock := k }).1 ≠ .error)
    (hnt_lab : (LabSem.evaluate { makeInit mc ffi t m (fun a => dm a && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms code (LabToTarget.compile asmConf)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle with
        clock := K }).1 ≠ .timeOut)
    (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    (LabSem.evaluate { makeInit mc ffi t m (fun a => dm a && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms code (LabToTarget.compile asmConf)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle with
        clock := K }).1 = (evaluateTargetHOL mc ffi K ms).1 ∧
    (LabSem.evaluate { makeInit mc ffi t m (fun a => dm a && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms code (LabToTarget.compile asmConf)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle with
        clock := K }).2.ffi = (evaluateTargetHOL mc ffi K ms).2.2 := by
  subst hasm
  let tUnaligned := makeInit mc ffi t m dm sdm ms code (LabToTarget.compile mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle
  let sFiltered := makeInit mc ffi t m dm sdm ms (filterSkip code)
    (compileLab mc.target.config)
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
    (fun n => ((coracle n).1, filterSkip (coracle n).2))
  have hr : LabFilter.Proofs.stateRel sFiltered tUnaligned := by
    refine ⟨⟨compileLab mc.target.config, ?_, rfl⟩, rfl⟩
    have hadj : LabFilter.Proofs.adjustPc tUnaligned.pc tUnaligned.code = tUnaligned.pc := by
      rw [show tUnaligned.pc = 0 from rfl, LabFilter.Proofs.adjustPc.eq_def]
      simp
    rw [hadj]
    rfl
  obtain ⟨hres_align0, hffi_align0⟩ :=
    lab_filter_align_run_agree_of_not_timeOut hmc.1 sFiltered tUnaligned hr K hnt_lab
  have hne_s : (LabSem.evaluate { sFiltered with clock := K }).1 ≠ .error := by
    rw [hres_align0]
    exact hne K
  have hgoodNat : goodCode mc.target.config (.ln : Spt (Spt Nat)) code := by
    simpa only [hlabs] using hgood
  have hcomp := hcompile
  simp only [LabToTarget.compile, compileLab, hlabs, hpos] at hcomp
  generalize hchoice : (match c.ffiNames with
    | some names => (names, listSubset (findFfiNames (filterSkip code)) names)
    | none => (findFfiNames (filterSkip code), true)) = choice at hcomp
  rcases choice with ⟨ffis, ffisOk⟩
  let finish (names : List HolFfiName) (ok : Bool) :=
    if ok then
      match removeLabels c.initClock mc.target.config 0 .ln names (filterSkip code) with
      | none => none
      | some (output, labs) =>
          let (newNames, info) := getShmemInfo output 0 [] []
          some (progToBytes output, { c with
            labels := labs
            pos := (progToBytes output).length + 0
            secPosLen := getSymbols 0 output
            ffiNames := some (names ++ newNames)
            shmemExtra := info })
    else none
  have hfinished : finish ffis ffisOk = some (bytes, cNext) := by
    cases hcfg : c.ffiNames with
    | none =>
      simp only [hcfg, Prod.mk.injEq] at hchoice
      rw [← hchoice.1, ← hchoice.2]
      cases hr : removeLabels c.initClock mc.target.config 0 .ln
          (findFfiNames (filterSkip code)) (filterSkip code) <;>
        simpa only [finish, hcfg, hr] using hcomp
    | some supplied =>
      simp only [hcfg, Prod.mk.injEq] at hchoice
      rw [← hchoice.1, ← hchoice.2]
      cases hr : removeLabels c.initClock mc.target.config 0 .ln supplied
          (filterSkip code) <;>
        simpa only [finish, hcfg, hr] using hcomp
  clear hcomp
  have hcomp := hfinished
  dsimp only [finish] at hcomp
  by_cases hok : ffisOk = true
  · simp only [hok, ↓reduceIte] at hcomp
    cases hremove : removeLabels c.initClock mc.target.config 0 .ln ffis
        (filterSkip code) with
    | none => simp only [hremove, reduceCtorEq] at hcomp
    | some output =>
      rcases output with ⟨code2, labs⟩
      simp only [hremove] at hcomp
      cases hinfo : getShmemInfo code2 0 [] [] with
      | mk newNames info =>
        simp only [hinfo, Option.some.injEq, Prod.mk.injEq] at hcomp
        obtain ⟨rfl, rfl⟩ := hcomp
        have hnames : mc.ffiNames = ffis ++ newNames := by
          simpa only [Option.some.injEq] using hffi.symm
        have hffis : ∀ name ∈ ffis, ∃ s, name = HolFfiName.extCall s := by
          cases hcfg : c.ffiNames with
          | none =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact findFfiNamesEvery (filterSkip code) _ rfl
          | some supplied =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact hprovided supplied hcfg
        have hnew : ∀ name ∈ newNames, ∀ s, name ≠ HolFfiName.extCall s := by
          obtain ⟨suffix, heq, hshared⟩ := getShmemInfo_mappedNames code2 0 [] [] newNames info hinfo
          simp only [List.nil_append] at heq
          rw [heq]
          intro name hmem s
          obtain ⟨op, rfl⟩ := hshared name hmem
          intro heq
          cases heq
        have hb : mmioPcsMinIndex mc.ffiNames = some ffis.length := by
          rw [hnames]
          exact mmioPcsMinIndex_append newNames ffis ⟨hnew, hffis⟩
        have hilen : i = ffis.length := Option.some.inj (hboundary.symm.trans hb)
        have htake : mc.ffiNames.take i = ffis := by
          rw [hnames, hilen, List.take_append_length]
        have hdrop : mc.ffiNames.drop i = newNames := by
          rw [hnames, hilen, List.drop_append_length]
        have hsubset : listSubset (findFfiNames (filterSkip code)) ffis = true := by
          cases hcfg : c.ffiNames with
          | none =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact listSubsetRefl _
          | some supplied =>
            simp only [hcfg, Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact hchoice.2.trans hok
        let shiftedInfo := info.map (fun rec => { rec with
          entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
          exitPc := (mc.target.getPc ms).toNat + rec.exitPc })
        obtain ⟨hres_s, hffi_s⟩ := lab_to_target_make_init_run_agree_of_not_timeOut mc ms ffi
          (filterSkip code) code2 labs c.initClock i cbspace t m dm sdm
          (fun n => ((coracle n).1, filterSkip (coracle n).2))
          newNames info shiftedInfo
          hmc.2.1 (goodCodeFiltered_local _ _ _ hgoodNat) hmc
          (by
            intro hno
            obtain ⟨hall, hzero⟩ := horacle ((noShareMemFilterSkip code).mp hno)
            refine ⟨?_, hzero⟩
            intro k'
            exact ⟨goodCodeFiltered_local _ _ _ (hall k').1,
              (noShareMemFilterSkip (coracle k').2).mpr (hall k').2⟩)
          (by
            rw [htake]
            simp only [listSubset, List.all_eq_true, decide_eq_true_eq] at hsubset ⊢
            intro name hmem
            exact hsubset name (List.mem_filter.mp hmem).1)
          (by simpa only [htake] using hremove)
          hinit hinfo rfl hdrop hboundary
          (by simpa only [shiftedInfo, List.map_map, Function.comp_def] using hentries)
          (by simpa only [shiftedInfo, List.length_map, List.map_map, Function.comp_def,
              BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm] using hmmio)
          (noInstallOrNoShareMemFilterSkip code mc.ffiNames hsafe)
          (by
            have hstart : startPcOk mc (mc.target.getPc ms) := by
              rw [← hinit.2.2.1]
              exact hinit.2.2.2.1
            exact bufferNotFfi_local mc _ _ cbspace i hstart hboundary hbound)
          K hne_s hnt
        exact ⟨hres_align0.symm.trans hres_s, hffi_align0.symm.trans hffi_s⟩
  · simp only [hok, ↓reduceIte, reduceCtorEq] at hcomp

/-- Same-clock stage A4 (`panToTargetMachineLabSource`) non-timeout run agreement:
if the target machine and `labst` do not time out at clock `K` and `labst` does not error at
any clock, then `labst` at clock `K` has the exact same result and FFI state as the target
machine at clock `K`! -/
theorem pan_to_target_machine_lab_run_agree_of_not_timeOut {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S) (bytes : List (BitVec 8)) (cbspace : Nat)
    (panCode : List (Pancake.PanLang.DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (ltconf : LabToTarget.Config)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hlab : LabToTarget.compile mc.target.config c.labConf
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p) = some (bytes, ltconf))
    (hnodup : ((Pancake.PanLang.functionsHOL panCode).map Prod.fst).Nodup)
    (hffiOk : match c.labConf.ffiNames with
      | none => True
      | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s)
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hffi : ltconf.ffiNames = some mc.ffiNames)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff),
            rec.reg, BitVec.ofNat width rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + ffiOffset * (i + 3) < 2 ^ width)
    (hsource : pancakeGoodCodeHOL panCode = true)
    (K : Nat)
    (hne : ∀ k, (LabSem.evaluate {
      (let regNames := c.stackConf.regNames
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
           mc.target.config.addrOffset sp []))) with clock := k }).1 ≠ .error)
    (hnt_lab : (LabSem.evaluate {
      (let regNames := c.stackConf.regNames
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
           mc.target.config.addrOffset sp []))) with clock := K }).1 ≠ .timeOut)
    (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    (LabSem.evaluate {
      (let regNames := c.stackConf.regNames
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
           mc.target.config.addrOffset sp []))) with clock := K }).1 =
      (evaluateTargetHOL mc ffi K ms).1 ∧
    (LabSem.evaluate {
      (let regNames := c.stackConf.regNames
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
           mc.target.config.addrOffset sp []))) with clock := K }).2.ffi =
      (evaluateTargetHOL mc ffi K ms).2.2 := by
  have hpos : c.labConf.pos = 0 := hcfg.2.2.2.2.1
  have hlabels : c.labConf.labels = .ln := hcfg.2.2.2.2.2.1
  obtain ⟨ffis, hffis, i, hi⟩ := BackendProof.compileLabIMPMmioPcsMinIndex mc.target.config
    c.labConf _ bytes ltconf ⟨hlab, hffiOk⟩
  rw [hffi] at hffis
  cases hffis
  obtain ⟨hshm, hmmioI, hbound⟩ := hmmio i hi
  have horacle := panToTargetCompilerOracleOk mc.target.config c.labConf ltconf _ bytes
    mc.ffiNames c.stackConf.regNames c.stackConf.jump mc.target.config.addrOffset
    (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)) hlab hpos hffi
  have hnis := panToTargetNoInstallOrNoShareMem panCode mc.target.config mc.target.config.isa _
    c.wordToWordConf col wprog bitmaps wconf fs p c.stackConf c.dataConf
    (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
    (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
    mc.target.config.addrOffset mc.ffiNames ⟨hnodup, hisa, rfl, hwtw, hwts⟩
  have hgc := panToTargetGoodCodeFromSource (β := Nat) c mc panCode col wprog bitmaps wconf fs p
    hcfg hmc.1 hisa hwtw hwts hnodup hsource
  exact lab_to_target_compile_run_agree_of_not_timeOut mc ffi ms _ mc.target.config c.labConf ltconf bytes
    cbspace i t m _ sdm _ hmc (fun _ => horacle) (by rw [hlabels]; exact hgc) rfl hlabels hpos
    hlab hffi hgi hi hshm hmmioI hnis hbound
    (fun ffis h => by rw [h] at hffiOk; exact hffiOk) K hne hnt_lab hnt

/-- Every successful `asmFetchAux position code = some line` occurs at a non-label
instruction index strictly bounded by `asmCodeLength code`. -/
theorem asmFetchAux_some_lt_asmCodeLength {width : Nat} [NeZero width]
    (code : LabProgHOL width) :
    ∀ (position : Nat) (line : LabLineHOL width),
      asmFetchAux position code = some line → position < asmCodeLength code := by
  induction code with
  | nil => intro position line h; simp [asmFetchAux] at h
  | cons sect rest ih =>
    rcases sect with ⟨sid, lines⟩
    induction lines with
    | nil =>
      intro position line h
      rw [asmFetchAux] at h
      rw [asmCodeLength]
      exact ih position line h
    | cons l ls ihl =>
      intro position line h
      rw [asmFetchAux] at h
      rw [asmCodeLength]
      by_cases hl : isLabelHOL l = true
      · simp only [hl, if_true, Nat.add_zero] at h ⊢
        exact ihl position line h
      · simp only [hl, Bool.false_eq_true, if_false] at h ⊢
        by_cases hp : position = 0
        · omega
        · simp only [hp, if_false] at h
          have hlt := ihl (position - 1) line h
          omega

/-- Any contiguous run of `.skip` instructions `allSkips pc code count` has length
`count ≤ asmCodeLength code` (and if `count > 0`, `pc + count ≤ asmCodeLength code`). -/
theorem allSkips_count_le_asmCodeLength {width : Nat} [NeZero width]
    (pc : Nat) (code : LabProgHOL width) (count : Nat)
    (hs : LabFilter.Proofs.allSkips pc code count) :
    count ≤ asmCodeLength code := by
  by_cases hc : count = 0
  · omega
  · obtain ⟨bytes, len, hfetch⟩ := hs.2 (count - 1) (by omega)
    have hlt := asmFetchAux_some_lt_asmCodeLength code (pc + (count - 1)) _ hfetch
    omega

/-- Quantitative refinement of `LabFilter.Proofs.asmFetchAuxEq`: the number of
skipped `.skip` instructions `count` at any `pc` is bounded by `asmCodeLength code`. -/
theorem asmFetchAuxEq_bounded {width : Nat} [NeZero width]
    (pc : Nat) (code : LabProgHOL width) :
    ∃ count ≤ asmCodeLength code,
      asmFetchAux (pc + count) code =
        asmFetchAux (LabFilter.Proofs.adjustPc pc code) (filterSkip code) ∧
      LabFilter.Proofs.allSkips pc code count := by
  obtain ⟨count, heq, hs⟩ := LabFilter.Proofs.asmFetchAuxEq pc code
  exact ⟨count, allSkips_count_le_asmCodeLength pc code count hs, heq, hs⟩

/-- Quantitative clock-overhead version of `LabToTarget.compileCorrect_step`:
if one `LabSem` step takes `l` target instructions (`l ≠ 0`) to transition from
`(mc, ms1)` to `(mc', ms2)` and the remaining `s1'.clock = s1.clock - 1` steps
have target clock overhead `k' ≤ M`, then `s1` runs in `s1.clock + k` target steps
with `k ≤ M + l - 1`. -/
theorem lab_to_target_step_clock_bound {width : Nat} [NeZero width] {S Q F : Type}
    {mc mc' : MachineConfig width S Q}
    {s1 s1' s2 : LabSem.State width LabToTarget.Config F}
    {ms1 ms2 : S} {res : MachineResult} {l M : Nat}
    (hclock : s1.clock ≠ 0)
    (hl : ∀ k, evaluateTargetHOL mc s1.ffi (k + l) ms1 =
        evaluateTargetHOL mc' s1.ffi k ms2)
    (hl0 : l ≠ 0)
    (hc : s1'.clock = s1.clock - 1)
    (hffi : s1'.ffi = s1.ffi)
    (ih : ∃ k' ≤ M, ∃ ms3,
      evaluateTargetHOL mc' s1'.ffi (s1'.clock + k') ms2 = (res, ms3, s2.ffi)) :
    ∃ k ≤ M + l - 1, ∃ ms3,
      evaluateTargetHOL mc s1.ffi (s1.clock + k) ms1 = (res, ms3, s2.ffi) := by
  obtain ⟨k', hk', ms3, hk⟩ := ih
  refine ⟨k' + l - 1, by omega, ms3, ?_⟩
  rw [show s1.clock + (k' + l - 1) = (s1'.clock + k') + l by omega, hl _, ← hffi]
  exact hk


end InitE
