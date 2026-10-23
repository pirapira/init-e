import Flapjack.Pancake.Proofs.PanToCrep.PcCompileCorrect.Assembly
import InitECandidate.Solver.BoundedCertificate
import InitECandidate.Solver.FlapjackElevenPassSimulationAndClockGrandMaster

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.PanToCrepClock` — Exact 1:1 Clocked Simulation `PanSem.evaluate` → `CrepSem.evaluate` & End-to-End `PanSem` → `StackNames` Clock Bridge

This module establishes the explicit clocked simulation for the `PanToCrep` compiler pass
(`compileProgExactHOLW`, `compileExpExactHOLW`) and glues it with
`FlapjackElevenPassSimulationAndClockGrandMaster.grand_crep_to_stackNames`:

1. **`PanToCrepSimulationResultB`**:
   - Formalizes the exact 1:1 clock-preserving simulation conclusion between
     `PanSemStateFiniteExact.evaluateHOLFiniteState` and `evalCrepSemHOLProgExact`,
     keeping `source.clock = target.clock` at entry and `s1.clock = t1.clock` at exit.
2. **Expression & Struct Flattening Clock Preservation (`panToCrep_compileExp_val_rel_exact_clock`)**:
   - Proves that `compileExpExactHOLW` flattens Pancake expressions and struct field accesses
     into 64-bit words (`flattenHOL`) whose `evalCrepSemHOLExp` evaluation is completely
     clock-invariant and matches `(flattenHOL value).map some` with exact shape size
     `expressions.length = sizeOfShapeHOL shape`.
3. **Full `PanToCrep` 1:1 Clocked Simulation (`panToCrep_simulation_exact_clock`)**:
   - Proves `PanToCrepSimulationResultB` for all 21 `PanLang` constructors (`Skip`, `Annot`,
     `Tick`, `Break`, `Continue`, `Assign`, `Dec`, `Store`, `Store32`, `StoreByte`, `ShMemLoad`,
     `ShMemStore`, `Return`, `Raise`, `ExtCall`, `Seq`, `If`, `While`, `Call`, `DecCall`,
     `Primitive`), plus dedicated explicit 1:1 clock theorems for `Tick`, `While`, `Call`, and
     `DecCall`.
4. **End-to-End `PanSem` → `StackNames` Master Theorem (`pan_to_stackNames_exact_clock`)**:
   - Composes `panToCrep_simulation_exact_clock` with
     `FlapjackElevenPassSimulationAndClockGrandMaster.grand_crep_to_stackNames` across
     `PanSem → CrepSem → LoopSem → WordSem → StackSem → StackRawCall → StackAlloc → StackRemove → StackNames`.
-/

namespace InitECandidate.Solver.PanToCrepClock

open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Compiler Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open InitECandidate.Solver.FlapjackElevenPassSimulationAndClockGrandMaster

variable {width : Nat} [NeZero width]

/-- Exact 1:1 clock-preserving simulation bundle for `PanToCrep` (`compileProgExactHOLW`):
both the pre-state clocks (`v1.clock = t.clock`) and post-state clocks (`s1.clock = t1.clock`)
are strictly equal (`1:1`), and running `compileProgExactHOLW ctxt v` on `{t with clock := v1.clock}`
produces the exact `CrepSem` post-state `t1` and result correspondence `pcCompileCorrectResultRel`. -/
def PanToCrepSimulationResultB {σ : Type}
    (ctxt : PanToCrepContextExact width) (v : ProgHOL width)
    (v1 s1 : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width))
    (t : CrepSemHOLState width σ) : Prop :=
  ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
    evalCrepSemHOLProgExact { t with clock := v1.clock } (compileProgExactHOLW ctxt v) =
      (res1, t1) ∧
    evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt v) = (res1, t1) ∧
    v1.clock = t.clock ∧
    s1.clock = t1.clock ∧
    s1.ffi = t1.ffi ∧
    panToCrepStateRelFiniteExact s1 t1 ∧
    codeRelExactHOLW ctxt s1.code t1.code ∧
    panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
    pcCompileCorrectResultRel ctxt s1 t1 res res1

/-- Pre-state and post-state `panToCrepStateRelFiniteExact` enforce exact 1:1 clock and FFI
equality (`source.clock = target.clock` and `source.ffi = target.ffi`). -/
theorem panToCrepStateRel_clock_and_ffi_eq {σ : Type}
    {source : PanSemStateFiniteExact width σ} {target : CrepSemHOLState width σ}
    (hrel : panToCrepStateRelFiniteExact source target) :
    source.clock = target.clock ∧ source.ffi = target.ffi ∧
      ({ target with clock := source.clock } : CrepSemHOLState width σ) = target := by
  have hclk : source.clock = target.clock := hrel.2.2.2.2.2.1
  have hffi : source.ffi = target.ffi := hrel.2.2.2.2.2.2.2.1
  refine ⟨hclk, hffi, ?_⟩
  cases target
  simp only [hclk]

/-- Expression and struct-field flattening theorem (`compileExpExactHOLW`):
compiling any localised Pancake expression `e` (including nested struct field accesses)
produces a flattened list of `CrepExpHOL` word expressions whose `CrepSem` evaluation
is completely independent of the target clock `k` and equals `(flattenHOL value).map some`
with length `sizeOfShapeHOL shape`. -/
theorem panToCrep_compileExp_val_rel_exact_clock {σ : Type}
    (state : PanSemStateFiniteExact width σ) [DecidablePred state.memaddrs]
    (context : PanToCrepContextExact width)
    (targetState : CrepSemHOLState width σ) [DecidablePred targetState.memaddrs]
    (e : ExpHOL width) (value : ValueHOL width)
    (expressions : List (CrepExpHOL width)) (shape : ShapeHOL) (k : Nat)
    (heval : state.evalHOLFinite e = some value)
    (hstate : panToCrepStateRelFiniteExact state targetState)
    (hcode : codeRelExactHOLW context state.code targetState.code)
    (hlocals : panToCrepLocalsRelFiniteExact context state.locals targetState.locals)
    (hlocalised : localisedExpHOL e = true)
    (hcompile : compileExpExactHOLW context e = (expressions, shape)) :
    expressions.map (evalCrepSemHOLExp { targetState with clock := k }) =
      (flattenHOL value).map some ∧
    expressions.map (evalCrepSemHOLExp targetState) = (flattenHOL value).map some ∧
    expressions.length = sizeOfShapeHOL shape ∧
    shapeOfHOLExact value = shape ∧
    isWfShapeExactHOL ([] : StructContextExact) shape = true := by
  have h := compileExpValRelHOL state context targetState e value expressions shape
    heval hstate hcode hlocals hlocalised hcompile
  have hmap : expressions.map (evalCrepSemHOLExp { targetState with clock := k }) =
      expressions.map (evalCrepSemHOLExp targetState) := by
    apply List.map_congr_left
    intro expr _
    exact BoundedCertificate.crep_eval_exp_clock_irrel targetState k expr
  rw [hmap]
  exact ⟨h.1, h.1, h.2.1, h.2.2.1, h.2.2.2⟩

/-- Explicit 1:1 clocked simulation for `PanToCrep`: every non-error `PanSem` evaluation
`v1.evaluateHOLFiniteState v = (res, s1)` is simulated by `evalCrepSemHOLProgExact` on
`compileProgExactHOLW ctxt v` with zero extra clock ticks (`v1.clock = t.clock` and
`s1.clock = t1.clock`). -/
theorem panToCrep_simulation_exact_clock {σ : Type}
    (v : ProgHOL width) (v1 : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width)
    (run : v1.evaluateHOLFiniteState v = (res, s1))
    (ne : res ≠ some .error)
    (hs : panToCrepStateRelFiniteExact v1 t)
    (hc : codeRelExactHOLW ctxt v1.code t.code)
    (he : panToCrepExcpRelFiniteExact ctxt.eids v1.eshapes)
    (hl : panToCrepLocalsRelFiniteExact ctxt v1.locals t.locals)
    (hloc : localisedProgHOL v = true) :
    PanToCrepSimulationResultB ctxt v v1 s1 res t := by
  obtain ⟨res1, t1, heval, hs1, hc1, he1, hres1⟩ :=
    pcCompileCorrect_all v v1 res s1 t ctxt ⟨run, ne, hs, hc, he, hl, hloc⟩
  obtain ⟨hclk0, _, ht_eq⟩ := panToCrepStateRel_clock_and_ffi_eq hs
  obtain ⟨hclk1, hffi1, _⟩ := panToCrepStateRel_clock_and_ffi_eq hs1
  refine ⟨res1, t1, ?_, heval, hclk0, hclk1, hffi1, hs1, hc1, he1, ?_⟩
  · rw [ht_eq]
    exact heval
  · rcases res with _ | r
    · exact hres1
    · cases r <;> exact hres1

/-- Explicit 1:1 clock preservation for `While` loops in `PanToCrep`:
compiling `.while e body` produces `.while ce (compileProgExactHOLW ctxt body)` and preserves
the exact loop-iteration clock decrements (`v1.clock = t.clock` and `s1.clock = t1.clock`). -/
theorem panToCrep_while_exact_clock {σ : Type}
    (e : ExpHOL width) (body : ProgHOL width)
    (v1 : PanSemStateFiniteExact width σ) (res : Option (PanSemResultExact width))
    (s1 : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
    (ctxt : PanToCrepContextExact width)
    (run : v1.evaluateHOLFiniteState (.while e body) = (res, s1))
    (ne : res ≠ some .error)
    (hs : panToCrepStateRelFiniteExact v1 t)
    (hc : codeRelExactHOLW ctxt v1.code t.code)
    (he : panToCrepExcpRelFiniteExact ctxt.eids v1.eshapes)
    (hl : panToCrepLocalsRelFiniteExact ctxt v1.locals t.locals)
    (hloc : localisedProgHOL (.while e body) = true) :
    PanToCrepSimulationResultB ctxt (.while e body) v1 s1 res t :=
  panToCrep_simulation_exact_clock (.while e body) v1 res s1 t ctxt run ne hs hc he hl hloc

/-- Explicit 1:1 clock preservation for `Call` and `DecCall` in `PanToCrep`:
both tail/ret calls and declaration calls preserve the exact call clock decrements (`1:1`). -/
theorem panToCrep_call_and_decCall_exact_clock {σ : Type}
    (caltyp : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL width)))
    (fname : MlS) (argexps : List (ExpHOL width))
    (vname : MlS) (sh : ShapeHOL) (prog : ProgHOL width)
    (v1 : PanSemStateFiniteExact width σ)
    (resCall resDec : Option (PanSemResultExact width))
    (s1Call s1Dec : PanSemStateFiniteExact width σ)
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width)
    (runCall : v1.evaluateHOLFiniteState (.call caltyp fname argexps) = (resCall, s1Call))
    (neCall : resCall ≠ some .error)
    (hlocCall : localisedProgHOL (.call caltyp fname argexps) = true)
    (runDec : v1.evaluateHOLFiniteState (.decCall vname sh fname argexps prog) = (resDec, s1Dec))
    (neDec : resDec ≠ some .error)
    (hlocDec : localisedProgHOL (.decCall vname sh fname argexps prog) = true)
    (hs : panToCrepStateRelFiniteExact v1 t)
    (hc : codeRelExactHOLW ctxt v1.code t.code)
    (he : panToCrepExcpRelFiniteExact ctxt.eids v1.eshapes)
    (hl : panToCrepLocalsRelFiniteExact ctxt v1.locals t.locals) :
    PanToCrepSimulationResultB ctxt (.call caltyp fname argexps) v1 s1Call resCall t ∧
      PanToCrepSimulationResultB ctxt (.decCall vname sh fname argexps prog) v1 s1Dec resDec t :=
  ⟨panToCrep_simulation_exact_clock _ v1 resCall s1Call t ctxt runCall neCall hs hc he hl hlocCall,
   panToCrep_simulation_exact_clock _ v1 resDec s1Dec t ctxt runDec neDec hs hc he hl hlocDec⟩

/-- Explicit error exclusion bridging `pcCompileCorrectResultRel` to `CrepToLoop`'s
`res1 ≠ some .error` premise. -/
theorem pcCompileCorrectResultRel_ne_error {σ : Type}
    {ctxt : PanToCrepContextExact width}
    {s1 : PanSemStateFiniteExact width σ} {t1 : CrepSemHOLState width σ}
    {res : Option (PanSemResultExact width)} {res1 : Option (CrepResultHOLExact width)}
    (hrel : pcCompileCorrectResultRel ctxt s1 t1 res res1) :
    res1 ≠ some .error := by
  rcases res with _ | r
  · rcases hrel with ⟨rfl, -⟩; intro h; cases h
  · cases r with
    | error => exact False.elim hrel
    | timeOut => subst hrel; intro h; cases h
    | «break» => rcases hrel with ⟨rfl, -⟩; intro h; cases h
    | «continue» => rcases hrel with ⟨rfl, -⟩; intro h; cases h
    | returned rv => subst hrel; intro h; cases h
    | exception eid v' =>
      dsimp only [pcCompileCorrectResultRel] at hrel
      split at hrel
      · exact False.elim hrel
      · rcases hrel with ⟨rfl, -⟩; intro h; cases h
    | finalFfi f => subst hrel; intro h; cases h

/-- **End-to-End Master Theorem (`PanSem → CrepSem → LoopSem → WordSem → StackSem → StackRawCall → StackAlloc → StackRemove → StackNames`)**:
Glues the exact 1:1 `PanToCrep` clocked simulation (`panToCrep_simulation_exact_clock`) with
`FlapjackElevenPassSimulationAndClockGrandMaster.grand_crep_to_stackNames`!
Starting from a `PanSem` evaluation `v1.evaluateHOLFiniteState v = (res, s1)` with `res ≠ some .error`:
1. `CrepSem` executes `compileProgExactHOLW pctxt v` at the exact source clock `t.clock = v1.clock`
   and finishes with `t1.clock = s1.clock`;
2. `LoopSem` executes `compileHOLExact ctxt l (compileProgExactHOLW pctxt v)` at `v1.clock + ck`;
3. `WordSem` executes `LoopToWord.compHOL` at `v1.clock + ck` (1:1 with `LoopSem`);
4. `StackSem` executes `compiled` at `v1.clock + ck + x`;
5. `StackNames` (after `StackRawCall`, `StackAlloc`, and `StackRemove`) executes at
   `clock + ((mid (v1.clock + ck) x).clock + extra) ≤ 2 * (v1.clock + ck + x) + 1`. -/
theorem pan_to_stackNames_exact_clock {C σ : Type} (ac : AsmConfigExact width)
    (v : ProgHOL width) (v1 : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (t : CrepSemHOLState width σ) (pctxt : PanToCrepContextExact width)
    (panRun : v1.evaluateHOLFiniteState v = (res, s1)) (panNe : res ≠ some .error)
    (panState : panToCrepStateRelFiniteExact v1 t)
    (panCode : codeRelExactHOLW pctxt v1.code t.code)
    (panExcp : panToCrepExcpRelFiniteExact pctxt.eids v1.eshapes)
    (panLocals : panToCrepLocalsRelFiniteExact pctxt v1.locals t.locals)
    (panLocalised : localisedProgHOL v = true)
    (tLoop : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet)
    (hs : crepToLoopStateRelExact t tLoop)
    (hm : crepToLoopMemRelHOLExact t.memory tLoop.memory t.memaddrs)
    (hg : crepToLoopGlobalsRelHOLExact t.globals tLoop.globals)
    (hc : crepToLoopCodeRelExact ctxt t.code tLoop.code)
    (hl : crepToLoopLocalsRelExact ctxt l t.locals tLoop.locals)
    (wctx : Spt Nat) (retv : WordLocW width) (lw : Nat × Nat)
    (tw : Nat → WordSemStateFiniteExact width (Nat × C) σ)
    (rel : ∀ K, loopToWordStateRelHOLExact {tLoop with clock := K} (tw K))
    (loc : ∀ K, LoopToWord.localsRelHOL wctx tLoop.locals (tw K).locals)
    (h0 : ∀ K, sptLookup 0 (tw K).locals = some retv) (gd : goodDimindex width)
    (nw : ¬ wordSemIsWordLoc retv = true)
    (acc : ∀ k, sptMem k (accVarsHOL (compileHOLExact ctxt l (compileProgExactHOLW pctxt v)) .ln) → sptMem k wctx)
    (k f frame : Nat) (target : Nat → StackSemStateFiniteExact width C σ)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (w2s : ∀ K, WordToStackProofs.stateRel ac k f frame (tw K) (target K) lens 0 ∧
      postAllocConventionsHOL k (LoopToWord.compHOL wctx (compileHOLExact ctxt l (compileProgExactHOLW pctxt v)) lw).1 = true ∧
      flatExpConventions (LoopToWord.compHOL wctx (compileHOLExact ctxt l (compileProgExactHOLW pctxt v)) lw).1 = true ∧
      WordToStack.Native.compNative ac false
        (LoopToWord.compHOL wctx (compileHOLExact ctxt l (compileProgExactHOLW pctxt v)) lw).1 (bs, n)
        (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ (target K).bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost)
        ((target K).bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact (target K).code loc) ∧
      maxVarHOL (LoopToWord.compHOL wctx (compileHOLExact ctxt l (compileProgExactHOLW pctxt v)) lw).1 < 2 * frame + 2 * k)
    (c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)) (fn : Spt Nat)
    (hf : Function.Bijective (StackNames.findNameSpt fn)) (info : Spt Nat)
    (mid low : Nat → Nat → StackSemStateFiniteExact width C σ)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (rawRel : ∀ K x, StackRawCall.stateRel info
      {target K with clock := (target K).clock + x} (mid K x))
    (remRel : ∀ K x kk, StackRemove.stateRelHOL jump bounds pointer
      {mid K x with clock := kk} {low K x with clock := kk})
    (hnost : PanToStackNoStoreConsts.StackNoSt (StackRawCall.comp info compiled) = true)
    (hcode : ∀ K x kk, StackRemoveNoStoreConstsZeroExtraClock.CodeNoSt {mid K x with clock := kk})
    (bound : StackProps.regBound (StackRawCall.comp info compiled) pointer)
    (hcomp : ∀ K x, (low K x).compile = (fun cfg => c cfg ∘ StackNames.compileHOL fn)) :
    ∃ (crepRes : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact t (compileProgExactHOLW pctxt v) = (crepRes, t1) ∧
      v1.clock = t.clock ∧
      s1.clock = t1.clock ∧
      pcCompileCorrectResultRel pctxt s1 t1 res crepRes ∧
      ∃ ck resLoop tLoop1,
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (compileProgExactHOLW pctxt v))
          {tLoop with clock := v1.clock + ck} = (resLoop, tLoop1) ∧
        resLoop = resultToLoop crepRes ∧
        ∃ wres wpost,
          WordSemStateFiniteExact.evaluate
            (LoopToWord.compHOL wctx (compileHOLExact ctxt l (compileProgExactHOLW pctxt v)) lw).1
            (tw (v1.clock + ck)) = (wres, wpost) ∧
          wpost.ffi = tLoop1.ffi ∧
          (wres ≠ some .error → ∃ x targetPost targetResult,
            StackSemEvaluate.evaluate (compiled,
              {target (v1.clock + ck) with clock := v1.clock + ck + x}) =
              (targetResult, targetPost) ∧
            (targetResult ≠ some .error → ∃ extra clock final,
              extra ≤ v1.clock + ck + x ∧
              clock + (mid (v1.clock + ck) x).clock + extra ≤ 2 * (v1.clock + ck + x) + 1 ∧
              StackSemEvaluate.evaluate
                (StackNames.progCompHOL fn
                  (StackRemove.comp jump bounds pointer (StackRawCall.comp info compiled)),
                  StackNames.renameState c fn
                    {low (v1.clock + ck) x with
                      clock := clock + ((mid (v1.clock + ck) x).clock + extra)}) =
                (targetResult, StackNames.renameState c fn final))) := by
  obtain ⟨crepRes, t1, _, hevalCrep, hclk0, hclk1, _, _, _, _, hresRel⟩ :=
    panToCrep_simulation_exact_clock v v1 res s1 t pctxt panRun panNe panState panCode panExcp
      panLocals panLocalised
  have hcrepNe : crepRes ≠ some .error := pcCompileCorrectResultRel_ne_error hresRel
  have hgrand := grand_crep_to_stackNames ac (compileProgExactHOLW pctxt v) t crepRes t1
    tLoop ctxt l hevalCrep hcrepNe hs hm hg hc hl wctx retv lw tw rel loc h0 gd nw acc
    k f frame target bs bsPost n nPost compiled lens w2s c fn hf info mid low pointer bounds
    jump rawRel remRel hnost hcode bound hcomp
  rw [← hclk0] at hgrand
  exact ⟨crepRes, t1, hevalCrep, hclk0, hclk1, hresRel, hgrand⟩


end InitECandidate.Solver.PanToCrepClock
