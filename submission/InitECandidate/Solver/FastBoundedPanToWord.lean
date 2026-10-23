import InitECandidate.Solver.FastBoundedStackToLab
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTop
import Flapjack.Pancake.LoopToWord.Proofs.StateRelImpSemantics
import Flapjack.Pancake.CrepToLoop.Proofs.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemanticsTop
import Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanSimp.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanStructs.SemanticsEq
import Flapjack.Pancake.Proofs.PanGlobals.CompileTopSemanticsDecls

open InitECandidate.Solver.FastEnv
open InitECandidate.Proofs.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapCopyGuards
open InitECandidate.Solver.FastEnv.BootstrapStraightLine
open InitECandidate.Solver.FastEnv.BootstrapTrace


namespace InitE
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open Flapjack.LoopToWord.CompileCorrect
open InitECandidate.Solver.YukonSelfContainedCert

/-- Clock-preserving `LoopToWord` simulation: at any clock `k`, a non-error entry call
on `s` (with `sptIsEmpty s.locals`) produces a `WordSem` entry call on `t` at the **same**
clock `k` (`extra = 0`) with `resultCase` and identical FFI state. -/
theorem loop_to_word_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (start k : Nat)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F)
    (hsr : loopToWordStateRelHOLExact s t)
    (hemp : sptIsEmpty s.locals = true)
    (hdim : goodDimindex width)
    (hret : sptLookup 0 t.locals = some (WordLocW.loc 1 0))
    (hev : LoopSemStateFiniteExact.evaluate
      (.call none (some start) [] none : HolLoopProg width) { s with clock := k } = (res, s1))
    (hne : res ≠ some .error) :
    ∃ t1 res1,
      WordSemStateFiniteExact.evaluate
        (.call none (some start) [0] none : WordLangProgHOL (BitVec width))
        { t with clock := k } = (res1, t1) ∧
      t1.ffi = s1.ffi ∧
      resultCase (makeCtxtHOL 2 [] .ln) (WordLocW.loc 1 0) { t with clock := k } res s1 res1 t1 := by
  have hloc : s.locals = .ln := by
    cases h : s.locals <;> first | rfl | (rw [h] at hemp; cases hemp)
  have hlocals : LoopToWord.localsRelHOL (makeCtxtHOL 2 [] .ln)
      ({ s with clock := k } : LoopSemStateFiniteExact width F).locals
      ({ t with clock := k } : WordSemStateFiniteExact width C F).locals := by
    show LoopToWord.localsRelHOL _ s.locals t.locals
    rw [hloc]
    exact LoopToWord.localsRelHOLMkCtxtLn 2 [] _ ⟨by decide, by decide⟩
  obtain ⟨t1, res1, hrun, hffi, hrc⟩ :=
    compileCorrect (C := C) (.call none (some start) [] none) { s with clock := k } res s1
      { t with clock := k } (makeCtxtHOL 2 [] .ln) (WordLocW.loc 1 0) (0, 0)
      ⟨hev, hne, loopToWordStateRelWithClockHOLExact s t k hsr, hlocals, hret, hdim,
        by simp [wordSemIsWordLoc], by intro x hx; simp [accVarsHOL, sptMem, sptDomain] at hx⟩
  have hcomp : (LoopToWord.compHOL (makeCtxtHOL 2 [] .ln)
      (.call none (some start) [] none : HolLoopProg width) (0, 0)).1 =
      .call none (some start) [0] none := by simp [LoopToWord.compHOL]
  rw [hcomp] at hrun
  exact ⟨t1, res1, hrun, hffi, hrc⟩

/-- Clocked `CrepToLoop` simulation: at any clock `k`, a non-error entry call on `s`
produces a `LoopSem` entry call on `t` at clock `k + k'` with mapped result
`resultToLoop res` and `crepToLoopStateRelExact s1 t1` (which includes `s1.ffi = t1.ffi`). -/
theorem crep_to_loop_clocked_sim {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (t : LoopSemStateFiniteExact width σ)
    (crep_code : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (lc : Nat) (c : AsmArchitecture)
    (prog : CrepProgHOL width) (k : Nat)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (hmd : s.memaddrs = (fun address => t.mdomain address = true))
    (hbe : s.be = t.be)
    (hsh : s.shMemaddrs = (fun address => t.shMdomain address = true))
    (hffi : s.ffi = t.ffi)
    (hbase : s.baseAddr = t.baseAddr)
    (htop : s.topAddr = t.topAddr)
    (hmem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hglob : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hdist : (crep_code.map Prod.fst).Nodup)
    (hscode : s.code = alistToFmapCodeExact crep_code)
    (htcode : t.code = sptFromAList (compileProgHOLExact c crep_code))
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hmf : (crepToLoopMakeFuncsExactHOL crep_code).lookup start = some (lc, 0))
    (hprog : holAlookup crep_code start = some ([], prog))
    (hev : evalCrepSemHOLProgExact { s with clock := k } (.call none start []) = (res, s1))
    (hne : res ≠ some .error) :
    ∃ k' t',
      LoopSemStateFiniteExact.evaluate
        (.call none (some lc) [] none : HolLoopProg width)
        { t with clock := k + k' } =
        (Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res, t') ∧
      s1.ffi = t'.ffi := by
  let nctxt : CrepToLoopContextExact :=
    mkCtxtExact c HolFiniteMapExact.empty (crepToLoopMakeFuncsExactHOL crep_code) 0
  have hcode2 : crepToLoopCodeRel2Exact nctxt s.code t.code := by
    rw [hscode, htcode]
    exact mkCtxtCodeImpCodeRel2Exact c crep_code start prog ⟨hdist, hprog⟩
  have hlc : findLabExact nctxt start = lc := by
    simp [findLabExact, nctxt, mkCtxtExact, hmf]
  have hdv : crepToLoopDistinctVarsExact nctxt.vars := by
    intro x y n m hx
    simp [nctxt, mkCtxtExact, HolFiniteMapExact.empty] at hx
  have hcm : crepToLoopCtxtMaxExact nctxt.vmax nctxt.vars := by
    intro v m hv
    simp [nctxt, mkCtxtExact, HolFiniteMapExact.empty] at hv
  have hmf' : (crepToLoopMakeFuncsExactHOL crep_code).lookup start =
      some (findLabExact nctxt start, 0) := by
    rw [hlc]; exact hmf
  obtain ⟨k', res', t', hrun, hsr, hres⟩ :=
    crepToLoopCodeRelEvaluateCallCorrect nctxt s.code t.code start
      { s with clock := k } res s1 { t with clock := k } crep_code lc prog hcode2 hev
      ⟨hbe, hsh, hmd, rfl, hffi, hbase, htop, hmem, hglob, hloc, rfl, rfl⟩ hmf'
      ⟨hlc, hscode, rfl, hprog, hdv, hcm⟩ hne
  rw [hlc] at hrun
  have hrun' : LoopSemStateFiniteExact.evaluate (.call none (some lc) [] none : HolLoopProg width)
      { t with clock := k + k' } = (res', t') := by
    have heq : ({ { t with clock := k } with clock := k + k' } :
        LoopSemStateFiniteExact width σ) = { t with clock := k + k' } := by
      cases t; rfl
    rw [← heq]
    exact hrun
  rw [hres] at hrun'
  exact ⟨k', t', hrun', hsr.2.2.2.2.1⟩

/-- Clock-preserving `CrepInline` simulation: at any clock `k`, a non-error entry call
on `s` produces the exact same result and FFI state on `t` at the same clock `k`. -/
theorem crep_inline_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ)
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (start : MlString)
    (inl_fname : List CrepInlineMapHOLName)
    (k : Nat)
    (hsr : CrepInlineExact.crepInlineStateRelCodeExact s t)
    (hls : CrepInlineExact.crepInlineLocalsStrongRelExact s t)
    (hd : (crep_code.map Prod.fst).Nodup)
    (hs : s.code = alistToFmapCodeExact crep_code)
    (ht : t.code = alistToFmapCodeExact (CrepInlineCanonical.compileInlTopHOLExact inl_fname crep_code))
    (hne : (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ≠ some .error) :
    (evalCrepSemHOLProgExact { t with clock := k } (.call none start [])).1 =
      (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ∧
    (evalCrepSemHOLProgExact { t with clock := k } (.call none start [])).2.ffi =
      (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).2.ffi := by
  let inl_fs := CrepInlineCanonical.alistToFmapHOLExact
    (crep_code.filter fun triple => inl_fname.contains triple.1)
  have ht' : t.code = alistToFmapCodeExact
      (CrepInlineCanonical.compileInlProgHOLExact inl_fs crep_code) := by
    rw [ht, CrepInlineCanonical.compileInlTopHOLExact]
    rw [CrepInlineCanonical.compileInlProgHOLExactWithSupport_eq_compileInlProgHOLExact]
  have hsub : HolFiniteMapExact.submap inl_fs s.code := by
    intro key v h
    rw [hs]
    have hm := flookup_fupdateList_reverse_mem' _ key v h
    exact flookup_fupdateList_reverse_of_mem crep_code key v hd
      (List.mem_filter.mp hm).1
  have hci := CrepInlineStateRelImpSemantics.codeInl_of_alist s t crep_code inl_fs hd hs ht'
  exact CrepInlineStateRelImpSemantics.entry_agree s t start inl_fs hsr hls hsub hci k hne

/-- Clock-preserving `PanToCrep` (pre-inline) simulation: at any clock `k`, a non-error
`PanSem` entry call on `s` produces a `CrepSem` entry call on `t` at the **same** clock `k`
(`extra = 0`) with `res1 ≠ some .error`, matching entry classification (`panEntryClass`),
and identical FFI state. -/
theorem pan_to_crep_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
    (pan_code : List (DeclHOL width)) (start : MlS) (k : Nat)
    (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (hsr : panToCrepStateRelFiniteExact s t)
    (hdist : ((functionsHOL pan_code).map Prod.fst).Nodup)
    (hscode : s.code = HolFiniteMapExact.empty.updateList (functionsHOL pan_code).reverse)
    (htcode : t.code = HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse)
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hlocal : ∀ entry ∈ functionsHOL pan_code, localisedProgHOL entry.2.2.1 = true)
    (hsize : sizeOfEidsHOL pan_code < 2 ^ width)
    (hdom : ∀ key, (s.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL pan_code).lookup key).isSome)
    (hev : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none start [] : ProgHOL width) = (res, s1))
    (hne : res ≠ some .error) :
    ∃ res1 t1,
      evalCrepSemHOLProgExact { t with clock := k }
        (.call none start [] : CrepProgHOL width) = (res1, t1) ∧
      res1 ≠ some .error ∧
      t1.ffi = s1.ffi ∧
      (match res1 with
       | some .timeOut => .Incomplete
       | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
       | some (.return _) => .CompleteResult HolOutcome.success
       | _ => .RunError) = panEntryClass res := by
  let ctxt : PanToCrepContextExact width :=
    mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL pan_code)) 0
      (getEidsFromDeclsHOL pan_code)
  have hsr' : panToCrepStateRelFiniteExact ({ s with clock := k } : PanSemStateFiniteExact width σ)
      ({ t with clock := k } : CrepSemHOLState width σ) := by
    obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10⟩ := hsr
    exact ⟨h1, h2, h3, h4, h5, rfl, h7, h8, h9, h10⟩
  have hcode : codeRelExactHOLW ctxt ({ s with clock := k } : PanSemStateFiniteExact width σ).code
      ({ t with clock := k } : CrepSemHOLState width σ).code := by
    show codeRelExactHOLW ctxt s.code t.code
    rw [hscode, htcode]
    exact mkCtxtCodeImpCodeRelExactHOLW pan_code hdist hlocal
  have hexcp : panToCrepExcpRelFiniteExact ctxt.eids
      ({ s with clock := k } : PanSemStateFiniteExact width σ).eshapes :=
    getEidsImpExcpRelExact s.eshapes pan_code ⟨hsize, hdom⟩
  have hlocals : panToCrepLocalsRelFiniteExact ctxt
      ({ s with clock := k } : PanSemStateFiniteExact width σ).locals
      ({ t with clock := k } : CrepSemHOLState width σ).locals := by
    show panToCrepLocalsRelFiniteExact ctxt s.locals t.locals
    rw [hloc]
    exact mkCtxtImpLocalsRelExact _ _ _
  obtain ⟨res1, t1, hrun, hsr1, _, _, hres⟩ :=
    pcCompileCorrect (.call none start []) { s with clock := k } res s1 { t with clock := k } ctxt
      ⟨hev, hne, hsr', hcode, hexcp, hlocals, by simp [localisedProgHOL, everyExpListHOL]⟩
  have hcomp : compileProgExactHOLW ctxt (.call none start [] : ProgHOL width) =
      (.call none start [] : CrepProgHOL width) := by
    simp [compileProgExactHOLW, compileCallNoReturnExactHOLW, compileExpExactHOLWList]
  rw [hcomp] at hrun
  refine ⟨res1, t1, hrun, ?_, hsr1.2.2.2.2.2.2.2.1.symm, ?_⟩
  · rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only at hres <;>
      (try split at hres) <;> first | exact False.elim hres | exact hne rfl | (rcases hres with ⟨rfl, _⟩ | rfl; rintro ⟨⟩)
  · rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;> dsimp only [panEntryClass] at hres ⊢ <;>
      (try split at hres) <;> first | exact False.elim hres | exact hne rfl | (rcases hres with ⟨rfl, _⟩ | rfl; rfl)

/-- Clock-preserving `PanSimp` simulation: at any clock `k`, a non-error entry call
on `s` produces the exact same result and FFI state on `t` at the same clock `k` (`extra = 0`). -/
theorem pan_simp_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (s t : PanSemStateFiniteExact width σ) (start : MlS) (k : Nat)
    (hrel : PanSimp.stateRel s t t.code)
    (hne : (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .error) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState { t with clock := k }
      (.call none start [] : ProgHOL width)).1 =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
        (.call none start [] : ProgHOL width)).1 ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState { t with clock := k }
      (.call none start [] : ProgHOL width)).2.ffi =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
        (.call none start [] : ProgHOL width)).2.ffi := by
  obtain ⟨ht, hnone, hsome⟩ := hrel
  rcases hs : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none start [] : ProgHOL width) with ⟨result, sourcePost⟩
  have hne' : result ≠ some .error := by simpa only [hs] using hne
  obtain ⟨hsim, _⟩ := PanSimp.codeSimAll (.call none start []) { s with clock := k }
    result sourcePost t.code hs hne' ⟨hnone, hsome⟩
  have htk : ({ t with clock := k } : PanSemStateFiniteExact width σ) =
      { s with clock := k, code := t.code } := by
    rw [ht]
  rw [htk, hsim]
  exact ⟨rfl, rfl⟩

/-- Clock-preserving `PanStructs` simulation: at any clock `k`, a non-error entry call
on `source` produces a `PanSem` entry call on `convertStateExact context source` at the
same clock `k` (`extra = 0`) with mapped result `convertResHOL` and identical FFI state. -/
theorem pan_structs_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (source : PanSemStateFiniteExact width σ) (start : MlS)
    (context : Pancake.PanStructs.CompileShapeExact.ContextExact) (k : Nat)
    (res : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width σ)
    (hstructs : context.structs = source.structs.map (fun entry => (entry.1, entry.2.fields)))
    (hlocals : source.locals = HolFiniteMapExact.empty)
    (hfields : feveryHOL
      (fun entry => valueFldsOkHOLExact source.structs entry.2)
      source.globals)
    (hwf : feveryHOL
      (fun entry => isWfShapeValueHOLExact source.structs entry.2)
      source.globals)
    (hclocals : context.locals = [])
    (hglobals : Pancake.Proofs.PanStructs.ShapeMap.shapeMap context.globals =
      source.globals.map2 (fun entry => shapeOfHOLExact entry.2))
    (hinfos : Pancake.Proofs.PanStructs.StructInfosOkExact.structInfosOkHOLExact source.structs)
    (hev : PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
      (.call none start [] : ProgHOL width) = (res, post))
    (hne : res ≠ some .error) :
    PanSemStateFiniteExact.evaluateHOLFiniteState
      { Pancake.Proofs.PanStructs.ConvertState.convertStateExact context source with clock := k }
      (.call none start [] : ProgHOL width) =
      (convertResHOL res,
        Pancake.Proofs.PanStructs.ConvertState.convertStateExact context post) := by
  have hlocalfields : feveryHOL
      (fun entry => valueFldsOkHOLExact source.structs entry.2)
      source.locals := by
    simp [hlocals, feveryHOL, HolFiniteMapExact.empty]
  have hlocalwf : feveryHOL
      (fun entry => isWfShapeValueHOLExact source.structs entry.2)
      source.locals := by
    simp [hlocals, feveryHOL, HolFiniteMapExact.empty]
  have hlocalmap : Pancake.Proofs.PanStructs.ShapeMap.shapeMap context.locals =
      source.locals.map2 (fun entry => shapeOfHOLExact entry.2) := by
    rw [hclocals, hlocals]
    apply HolFiniteMapExact.ext
    rfl
  obtain ⟨hrun, _⟩ := Pancake.Proofs.PanStructs.CompileCorrectExact.compileCorrectExact
    (.call none start []) { source with clock := k } post context res
    ⟨hev, hstructs, hlocalfields, hfields, hlocalwf, hwf, hinfos, hlocalmap, hglobals, hne⟩
  have hcomp : Pancake.PanStructs.CompileShapeExact.compileProgExact context
      (.call none start [] : ProgHOL width) = .call none start [] := by
    simp [Pancake.PanStructs.CompileShapeExact.compileProgExact,
      Pancake.PanStructs.CompileShapeExact.compileExpsExact]
  rw [hcomp] at hrun
  exact hrun

/-- Clock-preserving `PanGlobals` simulation: at any clock `k`, a non-error entry call
on `source` produces the exact same result and FFI state on `target` at the same clock `k`. -/
theorem pan_globals_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (context : PanGlobalsContextExact width)
    (source target : PanSemStateFiniteExact width σ) (start : MlS) (k : Nat)
    (hrel : panGlobalsStateRelHOLExact true context source target)
    (hne : (PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .error) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState { target with clock := k }
      (.call none start [] : ProgHOL width)).1 =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
        (.call none start [] : ProgHOL width)).1 ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState { target with clock := k }
      (.call none start [] : ProgHOL width)).2.ffi =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
        (.call none start [] : ProgHOL width)).2.ffi := by
  have hclock : panGlobalsStateRelHOLExact true context
      { source with clock := k } { target with clock := k } :=
    ⟨hrel.1, hrel.2.1, hrel.2.2.1, hrel.2.2.2.1, hrel.2.2.2.2.1, rfl, hrel.2.2.2.2.2.2⟩
  rcases hs : PanSemStateFiniteExact.evaluateHOLFiniteState { source with clock := k }
      (.call none start [] : ProgHOL width) with ⟨result, sourcePost⟩
  have hne' : result ≠ some .error := by simpa only [hs, Prod.fst] using hne
  obtain ⟨targetPost, ht, hr⟩ := PanGlobalsCompileCorrectAssembly.compileCorrectHOL
    (.call none start []) { source with clock := k } result context
    { target with clock := k } sourcePost ⟨hclock, hs, hne'⟩
  have compiledEntry : compileProgExactHOL context (.call none start [] : ProgHOL width) =
      .call none start [] := by simp [compileProgExactHOL, compileExpExactHOLList]
  rw [compiledEntry] at ht
  rcases hr with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hffi, _⟩
  rw [ht]
  exact ⟨rfl, hffi.symm⟩

/-- Clocked `PanGlobals` initializer call shift (+1): running `start` on `s` at clock `c + 1`
(which executes `body` at clock `0` and tail-calls `start'`) produces the exact same result
and FFI state as running `start'` on `s'` at clock `c`. -/
theorem pan_globals_init_call_clocked_shift {width : Nat} [NeZero width] {σ : Type}
    (s s' : PanSemStateFiniteExact width σ) (start start' : MlS)
    (body body' : ProgHOL width) (args' : List (MlS × ShapeHOL)) (rshape : ShapeHOL)
    (h1 : s.code.lookup start = some ([], .seq body (.call none start' []), rshape))
    (h2 : s.code.lookup start' = some (args', body', rshape))
    (h3 : PanSemStateFiniteExact.evaluateHOLFiniteState
      { s with locals := HolFiniteMapExact.empty } body = (none, s'))
    (h4 : s'.clock = s.clock)
    (c : Nat) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := c + 1 }
      (.call none start [] : ProgHOL width)).1 =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { s' with clock := c }
        (.call none start' [] : ProgHOL width)).1 ∧
    (PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := c + 1 }
      (.call none start [] : ProgHOL width)).2.ffi =
      (PanSemStateFiniteExact.evaluateHOLFiniteState { s' with clock := c }
        (.call none start' [] : ProgHOL width)).2.ffi := by
  let tin : PanSemStateFiniteExact width σ := { s with locals := HolFiniteMapExact.empty }
  have hcs : EvaluateClockSubCall.Mc tin body :=
    EvaluateClockSubCall.mc_of_pair tin body
      (evaluateClockSubHOLFinite body (PanPropsEvalStateFiniteExact.ofPanSemFinite tin))
  have hzero : PanSemStateFiniteExact.evaluateHOLFiniteState { tin with clock := 0 } body =
      (none, { s' with clock := 0 }) := by
    have hpre : PanSemStateFiniteExact.evaluateHOLFiniteState tin body =
        (none, { { s' with clock := 0 } with
          clock := ({ s' with clock := 0 }).clock + s.clock }) := by
      rw [show tin = { s with locals := HolFiniteMapExact.empty } from rfl, h3]
      congr 1
      simp only [Nat.zero_add]
      rw [← h4]
    have h := hcs none { s' with clock := 0 } s.clock hpre (by simp)
    simpa only [tin, Nat.sub_self] using h
  have hstep : ∀ k, PanSemStateFiniteExact.evaluateHOLFiniteState
      { s with locals := HolFiniteMapExact.empty, clock := k } body =
      (none, { s' with clock := k }) := by
    intro k
    have h := panPropsEvaluateAddClockEq body { tin with clock := 0 } none
      { s' with clock := 0 } k ⟨hzero, by simp⟩
    simpa only [tin, Nat.zero_add] using h
  exact SemInitSupport.step s s' start start' body body' args' rshape h1 h2 hstep c

private theorem bvSubZero_local {width : Nat} (x : BitVec width) : x - 0 = x := by
  apply BitVec.eq_of_toNat_eq
  simp

open PanGlobalsCompileDecsStructural PanGlobalsDeclListExact PanGlobalsCompileTopSemanticsDecls PanSemStateFiniteExact in
/-- Clocked `PanGlobals.compileTopExactHOL` declaration + entry-call simulation (+1 clock shift):
under the 14 hypotheses of `compileTopSemanticsDeclsHOL`, if `code` evaluates declarations to `s1`
and `s1` runs `start` at clock `k` without `.error`, then `compileTopExactHOL code start`
evaluates declarations to `T` and `T` runs `start` at clock `k + 1` with the exact same result
and FFI I/O events! -/
theorem pan_globals_compile_top_clocked_shift {width : Nat} [NeZero width] {σ : Type}
    (s t : PanSemStateFiniteExact width σ) (code : List (DeclHOL width)) (start : MlS)
    (mgs : BitVec width) (freeAddrs : BitVec width → Prop)
    (tmem : BitVec width → HolWordLab width)
    (tlocals : HolFiniteMapExact MlS (ValueHOL width))
    (h : ((functionsHOL code).map Prod.fst).Nodup ∧
      t = { s with
        topAddr := s.topAddr + mgs
        memaddrs := fun address => s.memaddrs address ∨ freeAddrs address
        memory := tmem
        locals := tlocals } ∧
      s.code = HolFiniteMapExact.empty ∧
      s.globals = HolFiniteMapExact.empty ∧
      panGlobalsByteAlignedHOL s.topAddr ∧
      goodDimindex width ∧
      mgs = panBytesInWord width *
        BitVec.ofNat width ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      freeAddrs = Flapjack.Compiler.Backend.StackRemove.addresses s.topAddr
        ((decShapesHOL code).map sizeOfShapeHOL).sum ∧
      (∀ address, s.memaddrs address → ¬ freeAddrs address) ∧
      (∀ address, s.memaddrs address → s.memory address = tmem address) ∧
      ¬ s.memaddrs (s.topAddr + mgs) ∧
      (panBytesInWord width).toNat * ((decShapesHOL code).map sizeOfShapeHOL).sum <
        2 ^ width ∧
      (∀ d ∈ code, isFunctionHOL d = true ∨ isDeclHOL d = true ∨ isExnDeclHOL d = true) ∧
      PanSemStateFiniteExact.semanticsDecls s start code ≠ .fail)
    (s1 : PanSemStateFiniteExact width σ) (k : Nat)
    (hs1 : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := [] } (fun a => Classical.propDecidable (s.memaddrs a)) code = some s1)
    (hne : (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .error) :
    ∃ T,
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { t with structs := [] } (fun a => Classical.propDecidable (t.memaddrs a))
        (compileTopExactHOL code start) = some T ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).1 =
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
          (.call none start [] : ProgHOL width)).1 ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).2.ffi.ioEvents =
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
          (.call none start [] : ProgHOL width)).2.ffi.ioEvents := by
  classical
  obtain ⟨hdistinct, ht, hcode, hglobals, halign, hgood, rfl, rfl, hdisj, hmem,
    htopNot, hbound, hkinds, hnf⟩ := h
  obtain ⟨body, rshape, hmain⟩ := PanPropsHasMain.semanticsDeclsHasMainPrime s start code hnf
  have hkindsB : code.all (fun d => isFunctionHOL d || isDeclHOL d || isExnDeclHOL d) =
      true := by
    apply List.all_eq_true.mpr
    intro d hd
    rcases hkinds d hd with h | h | h <;> simp [h]
  have hstartLookup : (functionsHOL code).lookup start = some ([], body, rshape) := by
    rw [hcode, emptyUpdateListLookup _ _ hdistinct] at hmain; exact hmain
  have hevT := evaluateCompileTopOfSource _ s1 { t with structs := [] } code start _ hs1 hstartLookup
    hkinds rfl (by rw [ht])
  have hpart : resortDeclsHOL code = code.filter isExnDeclHOL ++ code.filter isDeclHOL ++
      code.filter isFunctionHOL := by
    have hnames : code.filter isNameHOL = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro d hd
      rcases hkinds d hd with h | h | h <;> cases d <;>
        first | exact Bool.noConfusion h | exact Bool.noConfusion
    simp [resortDeclsHOL, hnames]
  have hs1orig := hs1
  have hres := Flapjack.resortDeclsEvaluate { s with structs := [] } code hkindsB
  rw [← hres, hpart, Flapjack.evaluateDeclsHOLFinite_append,
    Flapjack.evaluateDeclsHOLFinite_append] at hs1
  cases hsE : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := [] } (fun a => Classical.propDecidable (s.memaddrs a))
      (code.filter isExnDeclHOL) with
  | none => simp [hsE] at hs1
  | some sE =>
  cases hsD : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      sE (fun a => Classical.propDecidable (sE.memaddrs a)) (code.filter isDeclHOL) with
  | none => simp [hsE, hsD] at hs1
  | some sD =>
  simp only [hsE, hsD, Option.bind_some] at hs1
  have hsEform := evalExnsForm _ _ sE (fun d hd => (List.mem_filter.mp hd).2) hsE
  have hs1form := evalFunsForm _ _ s1 (fun d hd => (List.mem_filter.mp hd).2) hs1
  have hsDcode : sD.code = sE.code := by
    have := evaluateDeclsHOLFinite_functions sE _ sD hsD
    rw [this, functionsHOL_filter_isDecl]
    rfl
  rcases hc : compileDecsExactHOL
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
           ((decShapesHOL code).map sizeOfShapeHOL).sum } : PanGlobalsContextExact width)
      (fpermDecsHOL start (newMainNameHOL code) (resortDeclsHOL code)) with
    ⟨inits, funsC, exnsC, ctx⟩
  have hexplicit := PanGlobalsCompileTopSemanticsExact.evaluateDeclsCompileTopHOLFinite
    _ s1 code start [] body rshape inits funsC exnsC ctx ⟨hs1orig, hstartLookup, hkinds, hc⟩
  have hgeneric := evaluateCompileTopOfSource _ s1 { s with structs := [] } code start _ hs1orig
    hstartLookup hkinds rfl rfl
  rw [hgeneric] at hexplicit
  have htable := congrArg PanSemStateFiniteExact.code (Option.some.inj hexplicit)
  simp only at htable
  clear hexplicit hgeneric hres
  subst hsEform
  clear hsE hs1orig hpart hmain
  simp only at hsD hsDcode
  obtain ⟨N, hNdef⟩ : ∃ N, N = ((decShapesHOL code).map sizeOfShapeHOL).sum := ⟨_, rfl⟩
  obtain ⟨nm, hnm⟩ : ∃ nm, nm = newMainNameHOL code := ⟨_, rfl⟩
  rw [← hNdef] at ht hdisj htopNot hbound hc
  rw [← hnm] at hc htable
  obtain ⟨T, hT⟩ : ∃ T : PanSemStateFiniteExact width σ, T = { t with
    structs := []
    code := t.code.updateList (functionsHOL (compileTopExactHOL code start))
    eshapes := t.eshapes.updateList (exceptionsHOL (compileTopExactHOL code start)) } :=
    ⟨_, rfl⟩
  have hTcode : T.code = (HolFiniteMapExact.empty.update
      (start, [], .seq (nestedSeqHOL inits) (.call none nm []), rshape)).updateList
      ((functionsHOL (fpermDecsHOL start nm code)).map (fun entry =>
        (entry.1, entry.2.1, compileProgExactHOL ctx entry.2.2.1, entry.2.2.2))) := by
    rw [hT]; simp only; rw [ht]; simp only; rw [htable, hcode]; rfl
  have hcD : compileDecsExactHOL
      ({ globals := HolFiniteMapExact.empty, globalsSize := 0,
         maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width N } :
         PanGlobalsContextExact width) (code.filter isDeclHOL) = (inits, [], [], ctx) := by
    have := compile_decs_FILTER_declsHOL _ _ _ _ _ _ hc
    rwa [filterDeclFperm, filterDeclResort] at this
  have hND : ((decShapesHOL (code.filter isDeclHOL)).map sizeOfShapeHOL).sum = N := by
    rw [(dec_shapes_FILTERHOL code).2.2.1]; exact hNdef.symm
  obtain ⟨t', hrun, hrel', hclk, hffi, hloc, -⟩ :=
    PanGlobalsInitGlobalsAssembly.initGlobalsAll _ (code.filter isDeclHOL) _ sD
      inits [] [] ctx { T with locals := HolFiniteMapExact.empty } _
      ⟨hsD, fun d hd => (List.mem_filter.mp hd).2, hcD, by
        unfold panGlobalsStateRelHOLExact
        subst hT ht
        refine ⟨?_, fun h => absurd h (by decide), rfl, rfl, ?_, rfl, rfl, rfl, ?_, ?_,
          fun a h => Or.inl h, rfl, hmem, rfl, ?_, ?_, ?_, ?_, hgood⟩
        · change s.topAddr = s.topAddr + panBytesInWord width * BitVec.ofNat width N -
            panBytesInWord width * BitVec.ofNat width N
          rw [BitVec.add_sub_cancel]
        · rw [exceptionsFilterExn, exceptions_compile_topHOL code start _ hstartLookup]
        · intro name value h
          rw [hglobals] at h
          cases h
        · intro name shape address h
          cases h
        · intro f ps p rs h
          rw [hcode] at h
          cases h
        · intro _ _ _ _ _ _ _ h
          exact absurd (by rw [hglobals]; rfl) h
        · rintro (h | h)
          · exact htopNot h
          · exact topNotInAddresses hgood _ _ hbound h
        · exact alignedAdd hgood _ _ halign
            (PanGlobalsInitGlobalsAlignment.byteAlignedBytesInWordMulHOL _ hgood), rfl, by
      intro a h
      rw [hND]
      subst hT ht
      change ¬ Flapjack.Compiler.Backend.StackRemove.addresses
        (s.topAddr + panBytesInWord width * BitVec.ofNat width N -
          panBytesInWord width * BitVec.ofNat width N - 0) N a
      rw [bvSubZero_local, BitVec.add_sub_cancel]
      exact hdisj a h, by
      intro a h
      rw [hND] at h
      subst hT ht
      change Flapjack.Compiler.Backend.StackRemove.addresses
        (s.topAddr + panBytesInWord width * BitVec.ofNat width N -
          panBytesInWord width * BitVec.ofNat width N - 0) N a at h
      rw [bvSubZero_local, BitVec.add_sub_cancel] at h
      exact Or.inr h,
      alignedZero, hcode, by
      rintro v sh addr ⟨h1, -⟩
      change (s.globals.lookup v).isSome = true at h1
      rw [hglobals] at h1
      (cases h1), by rw [hND]; exact hbound⟩
  have hnmFresh : nm ∉ (functionsHOL code).map Prod.fst := by
    rw [hnm]; exact new_main_name_correctHOL code
  have hstartMem : start ∈ (functionsHOL code).map Prod.fst :=
    List.mem_map.mpr ⟨_, lookupMem _ _ _ hstartLookup, rfl⟩
  have hnmStart : nm ≠ start := fun h => hnmFresh (h ▸ hstartMem)
  have hfpNodup := ALL_DISTINCT_fperm_decsHOL start nm code hdistinct
  have hLkeys : ((functionsHOL (fpermDecsHOL start nm code)).map (fun entry =>
      (entry.1, entry.2.1, compileProgExactHOL ctx entry.2.2.1, entry.2.2.2))).map Prod.fst =
      (functionsHOL (fpermDecsHOL start nm code)).map Prod.fst := by
    rw [List.map_map]; rfl
  have hLNodup := hLkeys ▸ hfpNodup
  have hTlookup : ∀ f entry, (f, entry) ∈ functionsHOL (fpermDecsHOL start nm code) →
      T.code.lookup f = some (entry.1, compileProgExactHOL ctx entry.2.1, entry.2.2) := by
    intro f entry hmem'
    rw [hTcode, HolFiniteMapExact.lookup_updateList, fupdateListLookup,
      lookupReverseOfNodup _ _ hLNodup,
      lookupOfMemNodup _ f (entry.1, compileProgExactHOL ctx entry.2.1, entry.2.2)
        (List.mem_map.mpr ⟨(f, entry), hmem', rfl⟩) hLNodup]
  have hstartNotRenamed : start ∉ (functionsHOL (fpermDecsHOL start nm code)).map Prod.fst := by
    rw [functionsFpermDecsHOL, List.map_map]
    intro hmem'
    obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp hmem'
    simp only [Function.comp, fpermName] at heq
    by_cases h1 : start = entry.1
    · rw [if_pos h1] at heq; exact hnmStart heq
    · rw [if_neg h1] at heq
      by_cases h2 : nm = entry.1
      · exact hnmFresh (List.mem_map.mpr ⟨entry, hentry, h2.symm⟩)
      · rw [if_neg h2] at heq; exact h1 heq.symm
  have hL1 : T.code.lookup start =
      some ([], .seq (nestedSeqHOL inits) (.call none nm []), rshape) := by
    rw [hTcode, HolFiniteMapExact.lookup_updateList, fupdateListLookup,
      lookupNoneOfNotMem _ _ (by
        rw [List.map_reverse, List.mem_reverse, hLkeys]; exact hstartNotRenamed)]
    simp [HolFiniteMapExact.update, FUPDATE]
  have hbodyMem : (nm, ([] : List (MlS × ShapeHOL)), fpermHOL start nm body, rshape) ∈
      functionsHOL (fpermDecsHOL start nm code) := by
    rw [functionsFpermDecsHOL]
    refine List.mem_map.mpr ⟨(start, [], body, rshape), lookupMem _ _ _ hstartLookup, ?_⟩
    simp [fpermName]
  have hL2 := hTlookup nm _ hbodyMem
  have hsDempty : sD.code = HolFiniteMapExact.empty := hsDcode.trans hcode
  have hupd : ∀ (m : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL))
      (l : List (MlS × List (MlS × ShapeHOL) × ProgHOL width × ShapeHOL)),
      m.updateList l = m.updateListEq l := by
    intro m l
    apply HolFiniteMapExact.ext
    funext k'
    simp only [HolFiniteMapExact.lookup_updateList, HolFiniteMapExact.lookup_updateListEq]
    rw [FUPDATE_LIST_HOL_eq_FUPDATE_LIST]
  have hC2 : fpermCodeHOL start nm s1.code =
      HolFiniteMapExact.empty.updateList (functionsHOL (fpermDecsHOL start nm code)) := by
    rw [hs1form]
    simp only
    rw [hsDempty, functionsHOL_filter_isFunction, hupd, hupd,
      fpermCodeHOL_updateList_functions, fpermCodeHOL_empty]
  have hinv := Flapjack.evaluateInvariantsHOLFinite (nestedSeqHOL inits)
    (PanPropsEvalStateFiniteExact.ofPanSemFinite { T with locals := HolFiniteMapExact.empty })
    none (PanPropsEvalStateFiniteExact.ofPanSemFinite t') (by
      simp [PanPropsEvalStateFiniteExact.evaluateHOLFinitePair,
        PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite, hrun])
  have htcode : t'.code = T.code := hinv.2.2.2.2.2.2.1
  have hrelT : panGlobalsStateRelHOLExact true ctx
      (emptyLocalsHOLFinite { s1 with code := (HolFiniteMapExact.empty.updateList
        (functionsHOL (fpermDecsHOL start nm code))) }) t' := by
    subst hs1form
    obtain ⟨h1, -, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, -, h16, h17, h18,
      h19⟩ := hrel'
    refine ⟨h1, fun _ => ?_, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, ?_, h16,
      h17, h18, h19⟩
    · rw [hloc]; rfl
    · intro f ps p rs hlk
      change (HolFiniteMapExact.empty.updateList
        (functionsHOL (fpermDecsHOL start nm code))).lookup f = _ at hlk
      rw [emptyUpdateListLookup _ _ hfpNodup] at hlk
      rw [htcode]
      exact hTlookup f (ps, p, rs) (lookupMem _ _ _ hlk)
  -- Clocked chain: T at k + 1 -> t' at k -> emptyLocals s1_fperm at k -> s1_fperm at k -> s1 at k
  have hshift := pan_globals_init_call_clocked_shift T t' start nm
    (nestedSeqHOL inits) (compileProgExactHOL ctx (fpermHOL start nm body)) [] rshape
    hL1 hL2 hrun hclk k
  have hfperm_k : PanSemStateFiniteExact.evaluateHOLFiniteState
      { s1 with code := fpermCodeHOL start nm s1.code, clock := k }
      (.call none (fpermName start nm start) [] : ProgHOL width) =
      (fun outcome : Option (PanSemResultExact width) × PanSemStateFiniteExact width σ =>
        (outcome.1, { outcome.2 with code := fpermCodeHOL start nm outcome.2.code }))
        (PanSemStateFiniteExact.evaluateHOLFiniteState { s1 with clock := k }
          (.call none start [] : ProgHOL width)) := by
    simpa [fpermHOL] using evaluateFpermPrimeHOL start nm (.call none start []) s1 k
  have hname : fpermName start nm start = nm := by simp [fpermName]
  rw [hname, hC2] at hfperm_k
  let fpermCode := HolFiniteMapExact.empty.updateList (functionsHOL (fpermDecsHOL start nm code))
  have hemp_obs := Flapjack.panGlobals_call_emptyLocals_observation
    { s1 with code := fpermCode, clock := k } nm
  have hemp_eq : ({ emptyLocalsHOLFinite { s1 with code := fpermCode } with clock := k } :
      PanSemStateFiniteExact width σ) =
      emptyLocalsHOLFinite { s1 with code := fpermCode, clock := k } := rfl
  have hne_empty : (PanSemStateFiniteExact.evaluateHOLFiniteState
      { emptyLocalsHOLFinite { s1 with code := fpermCode } with clock := k }
      (.call none nm [] : ProgHOL width)).1 ≠ some .error := by
    rw [hemp_eq, ← (Prod.mk.inj hemp_obs).1, show fpermCode = _ from rfl, hfperm_k]
    exact hne
  have hglob_k := pan_globals_clocked_agree ctx
    (emptyLocalsHOLFinite { s1 with code := fpermCode }) t' nm k hrelT hne_empty
  refine ⟨T, ?_, ?_, ?_⟩
  · rw [hT]
    exact hevT
  · rw [hshift.1, hglob_k.1, hemp_eq, ← (Prod.mk.inj hemp_obs).1, show fpermCode = _ from rfl,
      hfperm_k]
  · rw [hshift.2, hglob_k.2, hemp_eq, ← (Prod.mk.inj hemp_obs).2, show fpermCode = _ from rfl,
      hfperm_k]

open Pancake.PanStructs.CompileShapeExact
open Pancake.Proofs.PanStructs.ConvertState
open Pancake.Proofs.PanStructs.ShapeMap
open Pancake.Proofs.PanStructs.StructInfosOkExact
open Pancake.Proofs.PanToWord.InitialComposition in
/-- Clocked `InitialComposition.initialToGlobalsSemantics` (`PanSimp` + `PanStructs` + `PanGlobals`):
if `code` evaluates declarations to `s_decls` and `s_decls` runs `start` at clock `k` with
`(res_src, s_src_post)` (`res_src ≠ some .error`), then `compileTopExactHOL (compileTopExact (panSimpDeclsHOL code)) start`
evaluates declarations on `globalState` to `T` and `T` runs `start` at clock **`k + 1`** with
`(convertResHOL res_src, ...)` and the exact same FFI I/O events `s_src_post.ffi.ioEvents`! -/
theorem pan_simp_structs_globals_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (code : List (DeclHOL width)) (start : MlS) (globalsSize : Nat)
    (hfail : PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (hdist : ((functionsHOL code).map Prod.fst).Nodup)
    (hcode : source.code = HolFiniteMapExact.empty)
    (hlocals : source.locals = HolFiniteMapExact.empty)
    (hglobals : source.globals = HolFiniteMapExact.empty)
    (heshapes : source.eshapes = HolFiniteMapExact.empty)
    (hsize : globalsSize = ((decShapesHOL code).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum)
    (halloc : globalsAllocatableHOL source code)
    (halign : panGlobalsByteAlignedHOL source.topAddr) (hdim : goodDimindex width)
    (hmem : ∀ address, source.memaddrs address →
      target.memory address = wlabWlocExact (source.memory address))
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : res_src ≠ some .error) :
    let globalState : PanSemStateFiniteExact width σ :=
      { source with
        topAddr := source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize
        memaddrs := fun address => source.memaddrs address ∨
          Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
        memory := wlocWlabHOL ∘ target.memory
        locals := source.locals }
    ∃ T,
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { globalState with structs := [] }
        (fun a => Classical.propDecidable (globalState.memaddrs a))
        (compileTopExactHOL (compileTopExact (panSimpDeclsHOL code)) start) = some T ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).1 = convertResHOL res_src ∧
      (PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
        (.call none start [] : ProgHOL width)).2.ffi.ioEvents = s_src_post.ffi.ioEvents := by
  classical
  intro globalState
  -- Pass 1: PanSimp
  have hrel0 : PanSimp.stateRel { source with structs := stCtxt }
      { source with structs := stCtxt } { source with structs := stCtxt }.code := by
    refine ⟨rfl, fun _ h => h, ?_⟩
    intro f vs p sh he
    simp [hcode, HolFiniteMapExact.empty] at he
  obtain ⟨s_simp, hev_simp, hrel_simp⟩ := PanSimp.stateRelImpEvaluateDeclsHOL
    { source with structs := stCtxt } code { source with structs := stCtxt } s_decls start
    ⟨hrel0, hdist, hev_decls⟩
  have hsimp_agree := pan_simp_clocked_agree s_decls s_simp start k hrel_simp
    (by rw [hev_call]; exact hne_src)
  rcases hev_simp_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_simp with clock := k }
      (.call none start [] : ProgHOL width) with ⟨res_simp, s_simp_post⟩
  have hres_simp : res_simp = res_src := by
    have h1 := hsimp_agree.1
    rw [hev_simp_call, hev_call] at h1
    exact h1
  have hffi_simp : s_simp_post.ffi = s_src_post.ffi := by
    have h2 := hsimp_agree.2
    rw [hev_simp_call, hev_call] at h2
    exact h2
  rw [hres_simp] at hev_simp_call
  -- Pass 2: PanStructs
  let code1 := panSimpDeclsHOL code
  have hnames1 : decsStcnamesHOLExact [] code1 = some stCtxt := by
    rw [decsStcnamesHOLExact_panSimpDeclsHOL_eq]
    exact hst
  let context := getNamesExact { structs := [], locals := [], globals := [] } code1
  have hctx := decsStcnamesToGetNames [] code1 stCtxt
    ({ structs := [], locals := [], globals := [] } : ContextExact) ⟨hnames1, rfl⟩
  have hctxstructs : context.structs = stCtxt.map (fun entry => (entry.1, entry.2.fields)) := by
    simp [context, hctx]
  have hctxlocals : context.locals = [] := by simp [context, hctx]
  have hctxglobals : context.globals = [] := by simp [context, hctx]
  have hinfos := decsStcnamesInfosOk [] code1 stCtxt ()
    ⟨hnames1, by simp [structInfosOkHOLExact]⟩
  have hmapempty : ∀ {α β γ : Type} (f : α × β → γ),
      HolFiniteMapExact.map2 f (HolFiniteMapExact.empty : HolFiniteMapExact α β) =
        HolFiniteMapExact.empty := by
    intro α β γ f
    apply HolFiniteMapExact.ext
    rfl
  have hfields : feveryHOL (fun entry => valueFldsOkHOLExact stCtxt entry.2) source.globals := by
    simp [hglobals, feveryHOL, HolFiniteMapExact.empty]
  have hwf : feveryHOL (fun entry => isWfShapeValueHOLExact stCtxt entry.2) source.globals := by
    simp [hglobals, feveryHOL, HolFiniteMapExact.empty]
  have hshapes : shapeMap context.globals =
      source.globals.map2 (fun entry => shapeOfHOLExact entry.2) := by
    rw [hctxglobals, hglobals, hmapempty]
    rfl
  rcases hcompile : compileDeclsExact context code1 with ⟨compiled, finalContext⟩
  have hsim := Pancake.Proofs.PanStructs.CompileDeclsCorrectExact.compileDeclsCorrectExact
    { source with structs := stCtxt } code1 s_simp context finalContext compiled
    ⟨hev_simp, hctxstructs, hctxlocals, hinfos, hfields, hwf, hshapes, hcompile⟩
  obtain ⟨hrun_decls, _, hfinal, hpostfields, hpostwf, hpoststructs, hpostlocals, hpostshapes⟩ := hsim
  have htop_eq : compileTopExact code1 = compiled := by
    change (compileDeclsExact context code1).1 = compiled
    rw [hcompile]
  have hboot : convertStateExact finalContext { source with structs := stCtxt } =
      { source with structs := [] } := by
    simp [convertStateExact, convertCodeExact, convertEshapesExact,
      hlocals, hglobals, hcode, heshapes, hmapempty, hfinal]
  have hs1 : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := [] }
      (fun address => Classical.propDecidable (source.memaddrs address))
      (compileTopExact code1) = some (convertStateExact finalContext s_simp) := by
    rw [htop_eq]
    exact (congrArg (fun state : PanSemStateFiniteExact width σ =>
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ state
        (fun address => Classical.propDecidable (state.memaddrs address)) compiled)
      hboot).symm.trans hrun_decls
  have hstruct_call := pan_structs_clocked_agree s_simp start finalContext k res_src s_simp_post
    (by simpa [hfinal, hpoststructs] using hctxstructs)
    (by simpa [hpostlocals] using hlocals)
    (by simpa [hpoststructs] using hpostfields)
    (by simpa [hpoststructs] using hpostwf)
    (by simpa [hfinal] using hctxlocals)
    (by simpa [hfinal] using hpostshapes)
    (by simpa [hpoststructs] using hinfos)
    hev_simp_call hne_src
  -- Pass 3: PanGlobals
  have hrel0_src : PanSimp.stateRel source source source.code := by
    refine ⟨by cases source; rfl, fun _ h => h, ?_⟩
    intro f vs p sh he
    simp [hcode, HolFiniteMapExact.empty] at he
  have hsimp_sem := PanSimp.stateRelImpSemanticsDeclsHOL source source code start
    ⟨hrel0_src, hdist, hcode, hcode, hfail⟩
  have hsimpnf : PanSemStateFiniteExact.semanticsDecls source start code1 ≠ .fail := by
    rw [← hsimp_sem]; exact hfail
  have hstruct_sem := Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact.compileTopSemanticsDeclsExact
    source start code1 ⟨hsimpnf, hlocals, hcode, hglobals⟩
  have hboot_esh : { source with eshapes := source.eshapes.map2 (fun entry =>
      compileShapeExact (getNamesExact { structs := [], locals := [], globals := [] } code1).structs
        entry.2) } = source := by
    have hm : source.eshapes.map2 (fun entry =>
        compileShapeExact (getNamesExact { structs := [], locals := [], globals := [] } code1).structs
          entry.2) = source.eshapes := by
      rw [heshapes, hmapempty]
    rw [hm]
  rw [hboot_esh] at hstruct_sem
  have hstructnf : PanSemStateFiniteExact.semanticsDecls source start (compileTopExact code1) ≠ .fail := by
    rw [← hstruct_sem]; exact hsimpnf
  let structCode := compileTopExact code1
  have hdiststruct : ((functionsHOL structCode).map Prod.fst).Nodup := by
    dsimp only [structCode, code1]
    rw [functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]
    exact hdist
  have hsizelist := semanticsSizeDecsStcnamesCompileStructsHOL source start code1
    ⟨hsimpnf, hglobals⟩
  have hsizecompiled : ((decShapesHOL structCode).map sizeOfShapeHOL).sum = globalsSize := by
    dsimp only [structCode, code1]
    rw [hsizelist, decShapesCompileProgHOL, decsStcnamesHOLExact_panSimpDeclsHOL_eq]
    exact hsize.symm
  have halloc' := halloc
  dsimp only [globalsAllocatableHOL] at halloc'
  rw [← hsize] at halloc'
  obtain ⟨_, hdisjoint, htopnot, hbound⟩ := halloc'
  have hmemory : ∀ address, source.memaddrs address →
      source.memory address = (wlocWlabHOL ∘ target.memory) address := by
    intro address ha
    simp only [Function.comp_apply, hmem address ha, wlocWlabWlabWlocHOL]
  have hne_struct : (PanSemStateFiniteExact.evaluateHOLFiniteState
      { convertStateExact finalContext s_simp with clock := k }
      (.call none start [] : ProgHOL width)).1 ≠ some .error := by
    rw [hstruct_call]
    rcases res_src with _ | r_val
    · intro h; cases h
    · cases r_val <;> intro h <;> first | exact hne_src rfl | cases h
  obtain ⟨T, hevT, hresT, hev_ioT⟩ := pan_globals_compile_top_clocked_shift
    source globalState structCode start
    (panBytesInWord width * BitVec.ofNat width globalsSize)
    (Compiler.Backend.StackRemove.addresses source.topAddr globalsSize)
    (wlocWlabHOL ∘ target.memory) source.locals
    ⟨hdiststruct, rfl, hcode, hglobals, halign, hdim,
      (by rw [hsizecompiled]), (by rw [hsizecompiled]),
      (fun address hs hf => hdisjoint address ⟨hs, hf⟩), hmemory,
      htopnot, (by simpa [hsizecompiled, panBytesInWord,
        Compiler.Backend.StackRemove.bytesInWord, Nat.mul_comm] using hbound),
      compileTopNoNames _, hstructnf⟩
    (convertStateExact finalContext s_simp) k hs1 hne_struct
  refine ⟨T, hevT, ?_, ?_⟩
  · rw [hresT, hstruct_call]
  · rw [hev_ioT, hstruct_call]
    show (convertStateExact finalContext s_simp_post).ffi.ioEvents = s_src_post.ffi.ioEvents
    have hffi_conv : (convertStateExact finalContext s_simp_post).ffi = s_simp_post.ffi := rfl
    rw [hffi_conv, hffi_simp]

open PanToCrepStateRelImpSemanticsTop
open LoopToWordStateRelImpSemanticsSupport in
private theorem list_lookup_isSome_iff_local {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) : (List.lookup k l).isSome = true ↔ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp only [List.lookup, Option.isSome, List.map_nil, List.not_mem_nil, reduceCtorEq]
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    by_cases h : k = a
    · subst h; simp only [List.lookup_cons, beq_self_eq_true, Option.isSome_some, List.map_cons, List.mem_cons, true_or]
    · have hbeq : (k == a) = false := beq_false_of_ne h
      simp only [List.lookup_cons, hbeq, ih, List.map_cons, List.mem_cons, h, false_or]

private theorem fupdateList_empty_eq_lookup_local {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) :
    FUPDATE_LIST FEMPTY l k = List.lookup k l.reverse := by
  have := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup l.reverse k
  simpa [FLOOKUP] using this

private theorem alistToFmap_eq_lookup_local {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) : FLOOKUP (alistToFmap l) k = List.lookup k l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    change FLOOKUP (FUPDATE (alistToFmap l) (a, b)) k = _
    rw [FLOOKUP_update, ih, List.lookup_cons]
    by_cases hk : k = a
    · subst hk; simp
    · have h1 : (a == k) = false := by simp [Ne.symm hk]
      have h2 : (k == a) = false := by simp [hk]
      simp [h1, h2]

open PanToCrepStateRelImpSemanticsTop
open LoopToWordStateRelImpSemanticsSupport in
/-- Clocked `PanToCrep` + `CrepInline` + `CrepToLoop` + `LoopToWord` composition:
given `T` resulting from `evaluateDeclsHOLFinite { globalState with structs := [] } panCode = some T`
and a non-error entry run on `T` at clock `c`, there exists `k'` such that `target`
(`WordSem`) runs `firstLoopName` at clock `c + k'` with matching `wordEntryClass`
(`panEntryClass res_pan`) and identical FFI I/O events! -/
theorem pan_to_crep_to_word_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
    (globalState T : PanSemStateFiniteExact width σ)
    (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS)
    (heapLen : BitVec width)
    (hnolabels : noLabelsHOL target.memory (fun address => target.mdomain address = true))
    (_hstart : start = ofString "main")
    (hmdomain : (fun address => target.mdomain address = true) = globalState.memaddrs)
    (hshdomain : (fun address => target.shMdomain address = true) = globalState.shMemaddrs)
    (hbe : target.be = globalState.be)
    (hffi : target.ffi = globalState.ffi)
    (hcurrheap : target.store.lookup .currHeap = some (.word globalState.baseAddr))
    (hheaplen : target.store.lookup .heapLength = some (.word heapLen))
    (htop' : globalState.topAddr = globalState.baseAddr + (2 : BitVec width) * heapLen)
    (hmem_glob : globalState.memory = wlocWlabHOL ∘ target.memory)
    (hcode : globalState.code = HolFiniteMapExact.empty)
    (hglobals : globalState.globals = HolFiniteMapExact.empty)
    (hlocals : globalState.locals = HolFiniteMapExact.empty)
    (heshapes : globalState.eshapes = HolFiniteMapExact.empty)
    (htcode : target.code = sptFromAList
      (loopToWordCompileProgHOL (compileProgHOLExact arch (compileProgDeclsHOLW panCode))))
    (hloc0 : sptLookup 0 target.locals = some (WordLocW.loc 1 0))
    (hdim : goodDimindex width)
    (hdist_pan : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hlocal_pan : ∀ entry ∈ functionsHOL panCode, localisedProgHOL entry.2.2.1 = true)
    (hall_pan : panCode.all (fun x => isFunctionHOL x || isExnDeclHOL x) = true)
    (hpanSize : sizeOfEidsHOL panCode < 2 ^ width)
    (hmf : (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW panCode)).lookup start =
      some (firstLoopName, 0))
    (hglobalnf : PanSemStateFiniteExact.semanticsDecls globalState start panCode ≠ .fail)
    (hevT : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { globalState with structs := [] }
      (fun a => Classical.propDecidable (globalState.memaddrs a)) panCode = some T)
    (c : Nat) (res_pan : Option (PanSemResultExact width))
    (s_pan_post : PanSemStateFiniteExact width σ)
    (hev_pan : PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := c }
      (.call none start [] : ProgHOL width) = (res_pan, s_pan_post))
    (hne_pan : panEntryClass res_pan ≠ .RunError) :
    ∃ k' t_word res_word,
      WordSemStateFiniteExact.evaluate
        (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
        { target with clock := c + k' } = (res_word, t_word) ∧
      t_word.ffi.ioEvents = s_pan_post.ffi.ioEvents ∧
      wordEntryClass res_word = panEntryClass res_pan := by
  classical
  have hne_pan_err : res_pan ≠ some .error := by
    intro h; subst h; exact hne_pan rfl
  -- Shape of T from evaluateDeclsOnlyFunsAndExnDeclsHOLFinite
  let s0 : PanSemStateFiniteExact width σ := { globalState with structs := [] }
  let p0 := PanPropsEvalStateFiniteExact.ofPanSemFinite s0
  let hdec : DecidablePred p0.memaddrs := fun a => Classical.propDecidable _
  have hcanon : PanPropsEvalStateFiniteExact.evaluateDeclsPanPropsCanonical p0 panCode =
      some (PanPropsEvalStateFiniteExact.ofPanSemFinite T) := by
    unfold PanPropsEvalStateFiniteExact.evaluateDeclsPanPropsCanonical
    have key : ∀ (st : PanSemStateFiniteExact width σ) (h1 h2 : DecidablePred st.memaddrs),
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ st h1 panCode =
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ st h2 panCode := by
      intro st h1 h2
      rw [Subsingleton.elim h1 h2]
    have hE := (key p0.toPanSemFinite inferInstance hdec).trans hevT
    rw [hE]
    rfl
  have hshape := PanPropsEvalStateFiniteExact.evaluateDeclsOnlyFunsAndExnDeclsHOLFinite p0 panCode
    (PanPropsEvalStateFiniteExact.ofPanSemFinite T) hall_pan hcanon
  have hT_eq : T = { s0 with
      code := HolFiniteMapExact.empty.updateList (functionsHOL panCode)
      eshapes := HolFiniteMapExact.empty.updateList (exceptionsHOL panCode) } := by
    have h := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hshape
    simp only [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at h
    rw [h]
    simp [PanPropsEvalStateFiniteExact.toPanSemFinite, p0,
      PanPropsEvalStateFiniteExact.ofPanSemFinite, s0, hcode, heshapes]
  -- Pass 4a: PanToCrep (to_crep)
  let crepState := crepStateHOL globalState panCode globalState.memory
  let crepStatePre := { crepState with
    code := HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW panCode).reverse }
  have hsr_crep : panToCrepStateRelFiniteExact T crepStatePre := by
    rw [hT_eq]
    simp [panToCrepStateRelFiniteExact, s0, crepStatePre, crepState, crepStateHOL,
      hglobals, HolFiniteMapExact.empty]
  have hscode_T : T.code = HolFiniteMapExact.empty.updateList (functionsHOL panCode).reverse := by
    rw [hT_eq]
    apply HolFiniteMapExact.ext
    funext k
    simp only [HolFiniteMapExact.lookup_updateList]
    change FUPDATE_LIST FEMPTY _ k = FUPDATE_LIST FEMPTY _ k
    rw [fupdateList_empty_eq_lookup_local, fupdateList_empty_eq_lookup_local, List.reverse_reverse,
      PanGlobalsCompileTopSemanticsDecls.lookupReverseOfNodup _ _ hdist_pan]
  have hdom_T : ∀ key, (T.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL panCode).lookup key).isSome := by
    intro key
    rw [hT_eq]
    show ((HolFiniteMapExact.empty.updateList (exceptionsHOL panCode)).lookup key).isSome =
      ((getEidsFromDeclsHOL panCode).lookup key).isSome
    rw [HolFiniteMapExact.lookup_updateList, holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL,
      alistToFmap_eq_lookup_local]
    change (FUPDATE_LIST FEMPTY _ key).isSome = _
    rw [fupdateList_empty_eq_lookup_local]
    apply Bool.eq_iff_iff.mpr
    rw [list_lookup_isSome_iff_local, list_lookup_isSome_iff_local, List.map_reverse,
      List.mem_reverse, getEidsEntriesHOL_eq_lengthBased]
    simp only
    rw [List.map_fst_zip (by simp)]
  have hloc_T : T.locals = HolFiniteMapExact.empty := by
    rw [hT_eq]; exact hlocals
  obtain ⟨res_crep1, t_crep1, hrun_crep1, hne_crep1_val, hffi_crep1, hclass_crep1⟩ :=
    pan_to_crep_clocked_agree T crepStatePre panCode start c res_pan s_pan_post
      hsr_crep hdist_pan hscode_T rfl hloc_T hlocal_pan hpanSize hdom_T hev_pan hne_pan_err
  -- Pass 4b: CrepInline
  have hne_crep1 : (evalCrepSemHOLProgExact { crepStatePre with clock := c }
      (.call none start [])).1 ≠ some .error := by
    rw [hrun_crep1]
    exact hne_crep1_val
  have hinl := crep_inline_clocked_agree crepStatePre crepState
    (compileToCrepExactHOLW panCode) start
    ((functionsHOL (panCode.filter inlinableHOL)).map Prod.fst) c
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
    (firstCompileToCrepAllDistinctExact panCode hdist_pan) rfl
    (by simp [crepState, crepStateHOL, compileProgDeclsHOLW, alistToFmapCodeExact])
    hne_crep1
  rcases hrun_crep : evalCrepSemHOLProgExact { crepState with clock := c }
      (.call none start []) with ⟨res_crep, t_crep⟩
  have hres_crep : res_crep = res_crep1 := by
    have h1 := hinl.1
    rw [hrun_crep, hrun_crep1] at h1
    exact h1
  have hffi_crep : t_crep.ffi = t_crep1.ffi := by
    have h2 := hinl.2
    rw [hrun_crep, hrun_crep1] at h2
    exact h2
  -- Pass 5: CrepToLoop
  let crepCode := compileProgDeclsHOLW panCode
  let loopState := loopStateHOL crepState arch crepCode target.clock target.memory
  have hcrep_sem := stateRelImpSemanticsDeclsPanToCrep globalState crepState panCode start
    ⟨(by simp [panToCrepStateRelFiniteExact, crepState, crepStateHOL,
          hglobals, HolFiniteMapExact.empty]),
      hdist_pan, hcode, rfl, hlocals, heshapes, hlocal_pan, hall_pan, hpanSize, hglobalnf⟩
  have hcrepnf : crepSemantics crepState start ≠ .fail := by
    rw [hcrep_sem]; exact hglobalnf
  have hdist_crep : (crepCode.map Prod.fst).Nodup :=
    panToCrepFirstCompileProgAllDistinctExact panCode hdist_pan
  obtain ⟨prog_crep, hprog_crep⟩ :=
    crepSemantics_ne_fail_imp_holAlookup crepState crepCode start rfl rfl hdist_crep hcrepnf
  have hne_crep : res_crep ≠ some .error := by
    rw [hres_crep]
    intro h
    subst h
    rw [hrun_crep1] at hne_crep1
    exact hne_crep1 rfl
  obtain ⟨k', t_loop, hrun_loop, hffi_loop⟩ :=
    crep_to_loop_clocked_sim crepState loopState crepCode start firstLoopName arch
      prog_crep c res_crep t_crep
      (by simp [loopState, loopStateHOL]) rfl
      (by simp [loopState, loopStateHOL]) rfl rfl rfl
      (by intro address ha
          have ha' : target.mdomain address = true := (congrFun hmdomain address).symm ▸ ha
          obtain ⟨w, hw⟩ := hnolabels address ha'
          simp [crepState, crepStateHOL, loopState, loopStateHOL, hmem_glob,
            wlocWlabHOL, wlabWlocExact, hw])
      (by intro address value he
          simp [crepState, crepStateHOL, HolFiniteMapExact.empty] at he)
      hdist_crep rfl rfl rfl hmf hprog_crep hrun_crep hne_crep
  -- Pass 6: LoopToWord
  have hdm : loopState.mdomain = target.mdomain := by
    funext address
    have hd := congrFun hmdomain address
    apply Bool.eq_iff_iff.mpr
    simpa [loopState, loopStateHOL, crepState, crepStateHOL] using Iff.of_eq hd.symm
  have hsh : loopState.shMdomain = target.shMdomain := by
    funext address
    have hd := congrFun hshdomain address
    simp [loopState, loopStateHOL, crepState, crepStateHOL, ← hd]
  have hparamsLoop := crepToLoopCompileProgDistinctParamsHOLExact crepCode arch
    (compileProgDeclsHOLW_params_nodup panCode)
  have hrel_word : loopToWordStateRelHOLExact loopState target := by
    refine ⟨heapLen, rfl, hdm.symm, hsh.symm, rfl, hbe, hffi, hcurrheap, hheaplen, htop', ?_, ?_⟩
    · intro name value hl
      simp [loopState, loopStateHOL, HolFiniteMapExact.empty] at hl
    · intro name params body hl
      constructor
      · rw [htcode]
        exact loopToWordLookupProgSomeLookupCompileProg _ name params body hl
      · apply of_decide_eq_true
        apply (List.all_eq_true.mp hparamsLoop) (name, params, body)
        apply sptAListLookup_mem name (compileProgHOLExact arch crepCode) (params, body)
        simpa only [loopState, loopStateHOL, sptLookup_sptFromAList] using hl
  have hne_loop : Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res_crep ≠ some .error := by
    rcases res_crep with _ | r_val
    · intro h; cases h
    · cases r_val <;> intro h <;> first | exact hne_crep rfl | cases h
  obtain ⟨t_word, res_word, hrun_word, hffi_word, hrc_word⟩ :=
    loop_to_word_clocked_agree loopState target firstLoopName (c + k')
      (Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res_crep) t_loop
      hrel_word rfl hdim hloc0 hrun_loop hne_loop
  refine ⟨k', t_word, res_word, hrun_word, ?_, ?_⟩
  · rw [hffi_word, ← hffi_loop, hffi_crep, hffi_crep1]
  · rw [← hclass_crep1, ← hres_crep] at hne_pan ⊢
    rcases res_crep with _ | (_ | _ | _ | _ | _ | _) <;>
      dsimp only [Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop, resultCase] at hne_pan hrc_word ⊢ <;>
      first | exact False.elim hrc_word | exact False.elim (hne_pan rfl) |
        (rcases hrc_word with ⟨rfl, _⟩; rfl) |
        (rcases hrc_word with ⟨_, rfl, _⟩; rfl) |
        (rcases hrc_word with ⟨_, _, rfl, _⟩; rfl) |
        (subst hrc_word; rfl)

open LoopToWordStateRelImpSemanticsSupport in
/-- Complete clocked `PanToWord` simulation (counterpart of `panToWordStateRelImpSemantics`):
under the 24 hypotheses of `panToWordStateRelImpSemantics`, if `code` evaluates declarations
to `s_decls` and `s_decls` runs `start` at clock `k` with `(res_src, s_src_post)`
(`panEntryClass res_src ≠ .RunError`), then there exists `k'` such that `target` (`WordSem`) runs
`firstLoopName` at clock **`(k + 1) + k'`** with `wordEntryClass res_word = panEntryClass res_src`
and the exact same FFI I/O events `s_src_post.ffi.ioEvents`! -/
theorem pan_to_word_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (h : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
      noLabelsHOL target.memory (fun address => target.mdomain address = true) ∧
      start = ofString "main" ∧
      globalsSize = ((decShapesHOL code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum ∧
      distinctParamsHOL (functionsHOL code) ∧
      (fun address => target.mdomain address = true) =
        (fun address => source.memaddrs address ∨ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (fun address => target.shMdomain address = true) = source.shMemaddrs ∧
      target.be = source.be ∧ target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word heapLen) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * heapLen - panBytesInWord width * BitVec.ofNat width globalsSize ∧
      ((functionsHOL code).map Prod.fst).Nodup ∧ panGlobalsByteAlignedHOL source.topAddr ∧
      globalsAllocatableHOL source code ∧ source.code = HolFiniteMapExact.empty ∧
      target.code = sptFromAList (panToWordCompileProgHOL arch code) ∧
      source.globals = HolFiniteMapExact.empty ∧ source.locals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL code < 2 ^ width ∧ source.eshapes = HolFiniteMapExact.empty ∧
      sptLookup 0 target.locals = some (WordLocW.loc 1 0) ∧ goodDimindex width ∧
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError) :
    ∃ k' t_word res_word,
      WordSemStateFiniteExact.evaluate
        (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
        { target with clock := (k + 1) + k' } = (res_word, t_word) ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents ∧
      wordEntryClass res_word = panEntryClass res_src := by
  classical
  have hne_src_err : res_src ≠ some .error := by
    intro herr; subst herr; exact hne_src rfl
  obtain ⟨hmem, hnolabels, hstart, hsize, _hparams, hmdomain, hshdomain, hbe, hffi,
    hcurrheap, hheaplen, htop, hdist, halign, halloc, hcode, htcode, hglobals,
    hlocals, heids, heshapes, hloc0, hdim, hfail⟩ := h
  have hglobalsSem := Pancake.Proofs.PanToWord.InitialComposition.initialToGlobalsSemantics
    source target code start globalsSize hfail hdist hcode hlocals hglobals heshapes
    hsize halloc halign hdim hmem
  let structCode := Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code)
  let panCode := compileTopExactHOL structCode start
  let globalState : PanSemStateFiniteExact width σ :=
    { source with
      topAddr := source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize
      memaddrs := fun address => source.memaddrs address ∨
        Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
      memory := wlocWlabHOL ∘ target.memory
      locals := source.locals }
  have hglobalnf : PanSemStateFiniteExact.semanticsDecls globalState start panCode ≠ .fail := by
    rw [← hglobalsSem]; exact hfail
  have hstructnf : PanSemStateFiniteExact.semanticsDecls source start structCode ≠ .fail := by
    have h1 := Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact.compileTopSemanticsDeclsExact
      source start (panSimpDeclsHOL code)
    have hs := PanSimp.stateRelImpSemanticsDeclsHOL source source code start
      ⟨(by refine ⟨?_, (fun _ h => h), ?_⟩
           · cases source; rfl
           · intro f vs p sh he; simp [hcode, HolFiniteMapExact.empty] at he),
        hdist, hcode, hcode, hfail⟩
    have he := h1 ⟨(by rw [← hs]; exact hfail), hlocals, hcode, hglobals⟩
    have hm : source.eshapes.map2 (fun entry =>
        Pancake.PanStructs.CompileShapeExact.compileShapeExact
          (Pancake.PanStructs.CompileShapeExact.getNamesExact
            { structs := [], locals := [], globals := [] } (panSimpDeclsHOL code)).structs
          entry.2) = source.eshapes := by
      rw [heshapes]; apply HolFiniteMapExact.ext; rfl
    rw [hm] at he
    rw [← he, ← hs]; exact hfail
  have hdiststruct : ((functionsHOL structCode).map Prod.fst).Nodup := by
    dsimp only [structCode]
    rw [functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]; exact hdist
  obtain ⟨mainBody, mainShape, hmain⟩ := semanticsDeclsHasMainPanToWordHOL source start structCode
    ⟨hcode, hdiststruct, hstructnf⟩
  have hpanSize : sizeOfEidsHOL panCode < 2 ^ width := by
    dsimp only [panCode]
    rw [sizeOfEidsCompileTopHOL structCode start [] mainBody mainShape hmain]
    dsimp only [structCode]
    rw [sizeOfEidsStructsCompileEqHOL, sizeOfEidsHOL_panSimpDeclsHOL_eq]
    exact heids
  have hmf : (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW panCode)).lookup start =
      some (firstLoopName, 0) :=
    flookupMakeFuncsMainHOL structCode start mainBody mainShape hmain
  have htop' : globalState.topAddr = globalState.baseAddr + (2 : BitVec width) * heapLen := by
    change source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize = _
    rw [htop]
    exact BitVec.sub_add_cancel _ _
  have hcodeWord : target.code = sptFromAList
      (loopToWordCompileProgHOL (compileProgHOLExact arch (compileProgDeclsHOLW panCode))) := by
    simpa [panToWordCompileProgHOL, panCode, structCode, hstart, loopToWordCompileHOL] using htcode
  obtain ⟨T, hevT, hresT, hioT⟩ := pan_simp_structs_globals_clocked_sim
    source target code start globalsSize hfail hdist hcode hlocals hglobals heshapes
    hsize halloc halign hdim hmem stCtxt s_decls hst hev_decls k res_src s_src_post hev_call hne_src_err
  rcases hev_pan : PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
      (.call none start [] : ProgHOL width) with ⟨res_pan, s_pan_post⟩
  have hres_pan : res_pan = convertResHOL res_src := by
    rw [hev_pan] at hresT; exact hresT
  have hio_pan : s_pan_post.ffi.ioEvents = s_src_post.ffi.ioEvents := by
    rw [hev_pan] at hioT; exact hioT
  have hclass_conv : panEntryClass (convertResHOL res_src) = panEntryClass res_src := by
    rcases res_src with _ | (_ | _ | _ | _ | _ | _ | _) <;>
      simp [convertResHOL, panEntryClass]
  have hne_pan : panEntryClass res_pan ≠ .RunError := by
    rw [hres_pan, hclass_conv]
    exact hne_src
  obtain ⟨k', t_word, res_word, hrun_word, hio_word, hclass_word⟩ :=
    pan_to_crep_to_word_clocked_sim globalState T target arch panCode start heapLen
      hnolabels hstart hmdomain hshdomain hbe hffi hcurrheap hheaplen htop' rfl
      hcode hglobals hlocals heshapes hcodeWord hloc0 hdim
      (allDistinctCompileTopHOL start structCode hdiststruct)
      (compileTopLocalisedHOL structCode start)
      (by apply List.all_eq_true.mpr
          intro d hd
          rcases PanGlobalsCompileDecsStructural.compile_top_only_functions_or_exnsHOL structCode start d hd with h | h <;> simp [h])
      hpanSize hmf hglobalnf hevT (k + 1) res_pan s_pan_post hev_pan hne_pan
  refine ⟨k', t_word, res_word, hrun_word, ?_, ?_⟩
  · rw [hio_word, hio_pan]
  · rw [hclass_word, hres_pan, hclass_conv]

open Flapjack.Compiler.Backend Flapjack.Pancake.Proofs.PanToTarget
open LoopToWordStateRelImpSemanticsSupport in
/-- Clocked counterpart of `panToTargetPanToWordStage`: bridges a concrete `PanSem` run on `s`
at clock `k_pan` to a `WordSem` run on `wst0` at `BvlToBvi.initGlobalsLocation` at clock
`(k_pan + 1) + k'`. -/
theorem pan_to_target_pan_to_word_stage_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
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
    (hcurr : sst.store.lookup .currHeap = some (.word s.baseAddr))
    (hheap : sst.store.lookup .heapLength = some (.word heapLen))
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
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError) :
    let wst := WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac
    let wst0 := { wst with code := sptFromAList (panToWordCompileProgHOL isa panCode) }
    ∃ k' t_word res_word,
      WordSemStateFiniteExact.evaluate
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec width))
        { wst0 with clock := (k_pan + 1) + k' } = (res_word, t_word) ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents ∧
      wordEntryClass res_word = panEntryClass res_src := by
  intro wst wst0
  rw [InitGlobals_location_eq_first_name]
  exact pan_to_word_clocked_sim s wst0 isa panCode start globalsSize heapLen
    ⟨hmem, hnolab, hstart, hsize, hparams, hmdomain, hshmdomain, hbe, hffi,
      by simpa [wst0, wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hcurr,
      by simpa [wst0, wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hheap,
      htop, hnodup, halign, halloc, hcode, rfl, hglobals, hlocals, heids, heshapes,
      by simp [wst0, wst, WordToStack.Native.Initialization.makeInit, sptLookup],
      good, hfail⟩
    stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src

open Flapjack.Compiler.Backend Flapjack.Pancake.Proofs.PanToTarget
open StackToLab.Proofs.FullMakeInitSemantics LoopToWordStateRelImpSemanticsSupport in
/-- Clocked counterpart of `panToTargetPanToWordFromInit`. -/
theorem pan_to_target_pan_to_word_from_init_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {t : LabSem.State width C σ}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C σ}
    (ac : AsmConfigExact width) (k_reg : Nat) (wcode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : PanSemStateFiniteExact width σ) (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS) (globalsSize heapLen : Nat)
    (w3 w4 : BitVec width)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle)
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset
      bitmaps code t saveRegs dataSp coracle = (sst, some x))
    (h2 : t.regs t.lenReg = .word s.baseAddr) (h3 : t.regs t.ptr2Reg = .word w3)
    (h4 : t.regs t.len2Reg = .word w4) (hlt : s.baseAddr < w3)
    (hlo : s.baseAddr + BitVec.ofNat width StackRemove.maxStackAlloc *
      StackRemove.bytesInWord width ≤ w3)
    (hhi : w3 ≤ w4 - BitVec.ofNat width StackRemove.maxStackAlloc *
      StackRemove.bytesInWord width)
    (hheap : (-1 * s.baseAddr + w3).toNat ≤ maxHeap * (StackRemove.bytesInWord width).toNat)
    (hheapLt : (StackRemove.bytesInWord width).toNat * maxHeap < 2 ^ width)
    (halign : holAligned (wordShiftAmount width + 1) (w3 + -1 * s.baseAddr) = true)
    (htmem : ∀ a, s.memaddrs a → t.memory a = wlabWlocExact (s.memory a))
    (htword : ∀ a, a.toNat % (width / 8) = 0 → ∃ w, t.memory a = .word w)
    (htsh : (fun a => t.sharedMemDomain a = true) = s.shMemaddrs)
    (htbe : t.be = s.be) (htffi : t.ffi = s.ffi)
    (hheapLen : heapLen = (w3 + -1 * s.baseAddr).toNat / (width / 8))
    (hglobLe : globalsSize ≤ heapLen)
    (hmemaddrs : s.memaddrs = StackRemove.addresses s.baseAddr (heapLen - globalsSize))
    (htop : s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heapLen -
      BitVec.ofNat width (globalsSize * width / 8))
    (hstart : start = ofString "main")
    (hsize : globalsSize = ((decShapesHOL panCode).map
      (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] panCode)))).sum)
    (hparams : distinctParamsHOL (functionsHOL panCode))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
      panCode = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError) :
    let wst := WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac
    let wst0 := { wst with code := sptFromAList (panToWordCompileProgHOL isa panCode) }
    ∃ k' t_word res_word,
      WordSemStateFiniteExact.evaluate
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec width))
        { wst0 with clock := (k_pan + 1) + k' } = (res_word, t_word) ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents ∧
      wordEntryClass res_word = panEntryClass res_src := by
  classical
  intro wst wst0
  have good : goodDimindex width := hA.1
  obtain ⟨t', v2, -, -, -, g2, -, -, a2, -⟩ := panToTargetInitCodeRun hA
  rw [h2] at g2; cases g2
  have hbase : s.baseAddr.toNat % (width / 8) = 0 :=
    (holByteAligned_iff_mod good _).1 a2
  obtain ⟨w2, g2', hcurr, hheapLW⟩ :=
    panToTargetWordInitStore (ac := ac) (k := k_reg) (wcode := wcode) (worac := worac) hA hfmi
  rw [h2] at g2'; cases g2'
  rw [readPointers_s2 hA h2 h3 h4] at hheapLW
  have hsnd := panToTargetHeapLimitSnd good maxHeap s.baseAddr w3 w4 a2 hlt hlo hhi hheap
    hheapLt halign
  rw [BitVec.add_comm (-1 * s.baseAddr), ← hheapLen] at hsnd
  have hmd := panToTargetWordInitMdomain (ac := ac) (k := k_reg) (wcode := wcode) (worac := worac)
    s.baseAddr w3 w4 hA hfmi h2 h3 h4 hlo hhi hheap hheapLt halign
  rw [← hheapLen] at hmd
  have hmdP : (fun a => wst.mdomain a = true) = StackRemove.addresses s.baseAddr heapLen := by
    funext a; rw [hmd a, decide_eq_true_eq]
  obtain ⟨hffi, hbe, hsh, hmem⟩ := panToTargetWordInitMemory (ac := ac) (k := k_reg)
    (wcode := wcode) (worac := worac) hA hfmi
  have hin : ∀ a, s.memaddrs a → wst.mdomain a = true := by
    intro a ha
    have : StackRemove.addresses s.baseAddr heapLen a := by
      rw [← addressesSplitGlobals good s.baseAddr heapLen globalsSize hglobLe]
      exact .inl (hmemaddrs ▸ ha)
    rw [← hmdP] at this; exact this
  have htopAl : panGlobalsByteAlignedHOL s.topAddr := by
    apply panGlobalsByteAligned_of_mod good
    rw [htop, good_dimindex_div_mul width globalsSize good]
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_mul, bytesInWord_toNat good]
    simp only [BitVec.toNat_ofNat]
    rcases good with h | h <;> subst h <;> simp at hbase ⊢ <;> omega
  refine pan_to_target_pan_to_word_stage_clocked_sim ac k_reg sst wcode worac s isa panCode start
    globalsSize (BitVec.ofNat width (StackRemove.Proofs.InitLimits.getStackHeapLimit maxHeap
      (s.baseAddr, w3, w4)).2 * StackRemove.bytesInWord width)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hstart hsize hparams ?_ hnodup htopAl halloc hcode hglobals hlocals
    heids heshapes good hfail stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src
  · intro a ha
    exact (hmem a (hin a ha)).trans (htmem a ha)
  · intro a ha
    have hadr : StackRemove.addresses s.baseAddr heapLen a := by
      rw [← hmdP]; exact ha
    obtain ⟨w, hw⟩ := htword a (addresses_mod good s.baseAddr hbase heapLen a hadr)
    exact ⟨w, (hmem a ha).trans hw⟩
  · show (fun a => wst.mdomain a = true) = _
    rw [hmdP, ← addressesSplitGlobals good s.baseAddr heapLen globalsSize hglobLe, hmemaddrs,
      htop]
  · show (fun a => wst.shMdomain a = true) = _
    rw [hsh]; exact htsh
  · exact hbe.trans htbe
  · exact hffi.trans htffi
  · simpa [wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hcurr
  · simpa [wst, WordToStack.Native.Initialization.makeInit, FDOMSUB_HOL] using hheapLW
  · rw [htop, good_dimindex_div_mul width globalsSize good]
    have e1 : (2 : BitVec width) * (BitVec.ofNat width (StackRemove.Proofs.InitLimits.getStackHeapLimit
        maxHeap (s.baseAddr, w3, w4)).2 * StackRemove.bytesInWord width) =
        StackRemove.bytesInWord width * BitVec.ofNat width heapLen := by
      rw [← hsnd, BitVec.ofNat_mul, BitVec.mul_comm (StackRemove.bytesInWord width),
        ← BitVec.mul_assoc]
      rfl
    have e2 : BitVec.ofNat width (globalsSize * (width / 8)) =
        panBytesInWord width * BitVec.ofNat width globalsSize := by
      rw [BitVec.ofNat_mul, BitVec.mul_comm]; rfl
    rw [e1, e2]

open Classical Flapjack.Compiler.Backend Flapjack.Pancake.Proofs.PanToTarget
open StackToLab.Proofs.FullMakeInitSemantics LoopToWordStateRelImpSemanticsSupport in
/-- Clocked counterpart of `panToTargetPanToWordStageLab`. -/
theorem pan_to_target_pan_to_word_stage_lab_clocked_sim {width : Nat} [NeZero width] {S Q C σ : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C σ}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (tAsm : AsmState width)
    (m : BitVec width → WordLocW width) (dm dm' sdm : BitVec width → Bool) (ms : S)
    (lcode : LabSem.LabProgHOL width)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (lorac : Nat → C × LabSem.LabProgHOL width)
    (bytes : List (BitVec 8))
    (ac : AsmConfigExact width) (k_reg : Nat) (wcode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : PanSemStateFiniteExact width σ) (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS) (globalsSize heapLen : Nat)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code
      (LabToTarget.makeInit (C := C) mc ffi tAsm m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms lcode comp cbpos cbspace lorac)
      saveRegs dataSp coracle)
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset
      bitmaps code
      (LabToTarget.makeInit (C := C) mc ffi tAsm m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms lcode comp cbpos cbspace lorac)
      saveRegs dataSp coracle = (sst, some x))
    (hmc : LabToTarget.mcConfOk mc)
    (hpm : ∀ a, decide (s.memaddrs a) = true → m a = wlabWlocExact (s.memory a))
    (hgi : goodInitState mc ms bytes cbspace tAsm m dm' sdm)
    (hsdm : (fun a => decide (s.shMemaddrs a)) = fun a => sdm a && holByteAligned a)
    (hbase : mc.target.getReg ms mc.lenReg = s.baseAddr)
    (hlt : mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg)
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * maxHeap)
    (hheapLt : (StackRemove.bytesInWord width).toNat * maxHeap < 2 ^ width)
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
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
      panCode = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError) :
    let wst := WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac
    let wst0 := { wst with code := sptFromAList (panToWordCompileProgHOL isa panCode) }
    ∃ k' t_word res_word,
      WordSemStateFiniteExact.evaluate
        (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec width))
        { wst0 with clock := (k_pan + 1) + k' } = (res_word, t_word) ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents ∧
      wordEntryClass res_word = panEntryClass res_src := by
  have good : goodDimindex width := hmc.1
  have hregs := hgi.1.2.2.2.1
  have hreg : ∀ r, asmRegOkExact r mc.target.config = true →
      tAsm.regs r = mc.target.getReg ms r := by
    intro r hr
    simp only [asmRegOkExact, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hr
    exact (hregs r hr).symm
  have r2 := hreg _ hmc.2.2.2.1
  have r3 := hreg _ hmc.2.2.2.2.1
  have r4 := hreg _ hmc.2.2.2.2.2.1
  have hmword := hgi.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine pan_to_target_pan_to_word_from_init_clocked_sim ac k_reg wcode worac s isa panCode start
    globalsSize heapLen (mc.target.getReg ms mc.ptr2Reg) (mc.target.getReg ms mc.len2Reg) hA hfmi
    ?_ ?_ ?_ (hbase ▸ hlt) ?_ ?_ ?_ hheapLt (hbase ▸ halign) ?_ ?_ ?_ ?_ ?_ hheapLen hglobLe
    (hbase ▸ hmemaddrs) htop hstart hsize hparams hnodup halloc hcode hglobals hlocals heids
    heshapes hfail stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src
  · simp [LabToTarget.makeInit, r2, hbase]
  · simp [LabToTarget.makeInit, r3]
  · simp [LabToTarget.makeInit, r4]
  · rw [← hbase, BitVec.mul_comm]; exact hlo
  · rw [BitVec.mul_comm]; exact hhi
  · rw [← hbase, BitVec.add_comm, Nat.mul_comm]; exact hheap
  · intro a ha
    exact hpm a (decide_eq_true ha)
  · intro a ha
    obtain ⟨w, -, hw⟩ := hmword a
    rw [Compiler.Backend.LabToTarget.holByteAlign_of_aligned good a ha] at hw
    exact ⟨w, hw⟩
  · funext a
    have := congrFun hsdm a
    simp only [LabToTarget.makeInit] at this ⊢
    rw [← this, decide_eq_true_eq]
  · exact hbe
  · exact hffi.symm

open Classical Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Pancake.Proofs.PanToTarget LoopToWordStateRelImpSemanticsSupport in
set_option maxHeartbeats 800000 in
/-- Complete end-to-end clocked `PanToTarget` theorem (clocked counterpart of
`panToTargetCompileSemantics` / `panToTargetCompileSemanticsStatement_proof`):
under the 35 hypotheses of `panToTargetCompileSemantics` and the resource-limit guard
`optionLt stack_max (some (readLimits mc.target.config c mc ms).1) = true`, if `pan_code`
evaluates declarations to `s_decls` and `s_decls` runs `start` at clock `k_pan` with
`panEntryClass res_src = .CompleteResult outcome`, then there exists a concrete target step
count `k_target` at which `evaluateTargetHOL mc ffi k_target ms` halts with `outcome` and
the exact same FFI I/O events `s_src_post.ffi.ioEvents`! -/
theorem pan_to_target_compile_clocked_halt {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (pan_code : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stack_max : Option Nat) (s : PanSemStateFiniteExact width σ) (ffi : HolFfiState σ)
    (ms : S) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec width)
    (cbspace data_sp : Nat) (start : MlS)
    (h :
      let getReg := mc.target.getReg ms
      compileProgMax c mc pan_code = (some (bytes, bitmaps, c'), stack_max) ∧
      pancakeGoodCodeHOL pan_code = true ∧
      distinctParamsHOL (functionsHOL pan_code) ∧
      ((functionsHOL pan_code).map Prod.fst).Nodup ∧
      s.code = HolFiniteMapExact.empty ∧
      s.locals = HolFiniteMapExact.empty ∧
      s.globals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL pan_code < 2 ^ width ∧
      s.eshapes = HolFiniteMapExact.empty ∧
      backendConfigOk mc.target.config c ∧ LabToTarget.mcConfOk mc ∧
      mcInitOk mc.target.config c mc ∧ mc.target.config.isa ≠ .ag32 ∧
      (0 : BitVec width) < getReg mc.lenReg ∧
      globals_size =
        (let dec_shs := decShapesHOL pan_code
         let struct_ctxt := decsStcnamesHOLExact (width := width) [] pan_code
         (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
      getReg mc.lenReg < getReg mc.ptr2Reg ∧
      getReg mc.lenReg = s.baseAddr ∧
      globalsAllocatableHOL s pan_code ∧
      heap_len = (getReg mc.ptr2Reg + -1 * s.baseAddr).toNat / (width / 8) ∧
      s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heap_len -
        BitVec.ofNat width (globals_size * width / 8) ∧
      globals_size ≤ heap_len ∧
      s.memaddrs = StackRemove.addresses (getReg mc.lenReg) (heap_len - globals_size) ∧
      holAligned (wordShiftAmount width + 1) (getReg mc.ptr2Reg + -1 * getReg mc.lenReg) = true ∧
      adj_ptr2 = getReg mc.lenReg +
        StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ∧
      adj_ptr4 = getReg mc.len2Reg -
        StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ∧
      adj_ptr2 ≤ getReg mc.ptr2Reg ∧
      getReg mc.ptr2Reg ≤ adj_ptr4 ∧
      (getReg mc.ptr2Reg + -1 * getReg mc.lenReg).toNat ≤
        (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) ∧
      (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) <
        2 ^ width ∧
      s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
      (match c.labConf.ffiNames with
        | none => True
        | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s) ∧
      panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
        (heapRegs c.stackConf.regNames) mc c'.labConf.shmemExtra ms
        (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
      start = ofString "main" ∧
      PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail)
    (hresLimit : optionLt stack_max (some (readLimits mc.target.config c mc ms).1) = true)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] pan_code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
      pan_code = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome) :
    ∃ k_target ms2 ffi2,
      evaluateTargetHOL mc ffi k_target ms = (.halt outcome, ms2, ffi2) ∧
      ffi2.ioEvents = s_src_post.ffi.ioEvents := by
  obtain ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hcfg, hmc,
    hinit, hisa, -, hsize, hlt, hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign,
    rfl, rfl, hlo, hhi, hheap, hheapLt, hffi, hbe, hffiOk, hinst, hstart, hfail⟩ := h
  obtain ⟨col, wprog, wconf, fs, p, ltconf, hwtw, hwts, hlab, rfl, hmax⟩ :=
    compileProgMax_some c mc pan_code bytes bitmaps _ stack_max hcomp
  obtain ⟨t, m, bitmapPtr, bitmapsDm, sdm, hpm, hgi, hsdm, a1, a2, a3, hle, hbig, hdisj, m0, m1,
    m2, m3, m4, hstar, hffiN, hmmio⟩ := hinst
  have hpi :
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
      m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width data_sp +
        biw * BitVec.ofNat width bitmaps.length) ∧
      m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
      m (t.regs r1 + 4 * biw) =
        .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
      SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
        (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) data_sp)
        (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)) :=
    ⟨a1, a2, a3, hle, hbig, hdisj, m0, m1, m2, m3, m4, hstar⟩
  have hpm' : ∀ a, decide (s.memaddrs a) = true → m a = wlabWlocExact (s.memory a) :=
    fun a h => hpm a (of_decide_eq_true h)
  have hsdm' : (fun a => decide (s.shMemaddrs a)) = fun a => sdm a && holByteAligned a := by
    funext a; rw [hsdm]; simp only [Bool.decide_and, Bool.decide_eq_true]
  obtain ⟨_, hsemEq, x, hfmi⟩ := panToTargetLabSemantics (C := LabToTarget.Config) c mc ffi t m
    bitmapPtr bitmapsDm sdm ms (LabToTarget.compile mc.target.config) bytes cbspace ltconf pan_code
    col wprog bitmaps wconf fs p data_sp s start globals_size heap_len hcfg hmc hinit hisa hwtw
    hwts hnodup hpm' hgi hsdm' hpi hbase hlt hlo hhi hheap hheapLt halign hbe hffi hheapLen
    hglobLe hmemaddrs htop hstart hsize hparams halloc hcode hglobals hlocals heids heshapes hfail
  have hA := panToTargetFullMakeInitAssumptions (C := LabToTarget.Config) c mc ffi t m bitmapPtr
    bitmapsDm sdm ms (LabToTarget.compile mc.target.config) bytes cbspace ltconf pan_code col wprog
    bitmaps wconf fs p data_sp hcfg hmc hinit hisa hwtw hwts hnodup hpi
  have hne_src : panEntryClass res_src ≠ .RunError := by
    rw [hclass_src]; intro herr; cases herr
  let regNames := c.stackConf.regNames
  let r1 := StackNames.findNameSpt regNames 2
  let r2 := StackNames.findNameSpt regNames 4
  let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
  let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
  let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
  let k_reg := mc.target.config.regCount - (5 + mc.target.config.avoidRegs.length)
  let worac : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec width)) :=
    fun _ => ((bitmaps.length, ltconf), [])
  obtain ⟨k', t_word, res_word, hrun_w0, hio_w0, hclass_w0⟩ :=
    pan_to_target_pan_to_word_stage_lab_clocked_sim (C := LabToTarget.Config) mc ffi t m
      (fun w => heapStackDm w || bitmapsDm w)
      (fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2) || bitmapsDm w) sdm ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      (LabToTarget.compile mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
      bytes mc.target.config k_reg (sptFromAList wprog) worac s mc.target.config.isa pan_code start
      globals_size heap_len hA hfmi hmc hpm' hgi hsdm' hbase hlt hlo hhi hheap hheapLt
      halign hbe hffi hheapLen hglobLe hmemaddrs htop hstart hsize hparams hnodup halloc hcode
      hglobals hlocals heids heshapes hfail stCtxt s_decls hst hev_decls k_pan res_src s_src_post
      hev_call hne_src
  have hcw : wordEntryClass res_word = .CompleteResult outcome := hclass_w0.trans hclass_src
  obtain ⟨k_target, ms2, ffi2, htarget, hio_target⟩ :=
    pan_to_target_backend_clocked_halt c mc ffi t m bitmapPtr bitmapsDm sdm ms bytes cbspace
      ltconf pan_code col wprog bitmaps wconf fs p data_sp stack_max
      hcfg hmc hinit hisa hwtw hwts hlab hmax hnodup hffiOk hgi hffiN hmmio hgood hpi
      hlo hhi hheap hheapLt halign hresLimit (hsemEq ▸ hfail)
      ((k_pan + 1) + k') res_word outcome t_word
      (by
        rcases res_word with _ | r_val
        · cases hcw
        · cases r_val with
          | finalFfi e => simp [wordEntryClass] at hcw; exact hcw.symm
          | result ret vals =>
            by_cases hret : ret = WordLocW.loc 1 0
            · subst hret; simp [wordEntryClass] at hcw; exact hcw.symm
            · simp [wordEntryClass, hret] at hcw
          | notEnoughSpace => simp [wordEntryClass] at hcw; exact hcw.symm
          | timeOut | «break» _ | «continue» _ | exception _ _ | error =>
            simp [wordEntryClass] at hcw)
      hrun_w0
  exact ⟨k_target, ms2, ffi2, htarget, hio_target.trans hio_w0⟩

open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.Pancake.PanToTarget in
/-- Clocked counterpart of `oracle_baseline_behaviour_eq`: for any validated allocation
oracles and certified compiler depth `≤ 7480`, if `sourceDeclarations` evaluates
declarations on `sourceInitialState input` to `s_decls` and `s_decls` runs `"main"`
at clock `k_pan` with `panEntryClass res_src = .CompleteResult outcome`, then there exists
`k_target` such that `evaluateTargetHOL mc (sourceFfi input) k_target ms` halts with
`outcome` and identical FFI I/O events! -/
theorem oracle_baseline_clocked_halt (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ms : RiscV.L3.riscv_state) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c : Backend.Config) (depth heapLen : Nat) (adj2 adj4 : BitVec 64)
    (cbspace dataSp : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (bytes, bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input mc ms bytes bitmaps c heapLen adj2 adj4 cbspace dataSp)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact 64))
    (s_src_post : PanSemStateFiniteExact 64 Guest.HostMemory) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome) :
    ∃ k_target ms2 ffi2,
      evaluateTargetHOL mc (sourceFfi input) k_target ms = (.halt outcome, ms2, ffi2) ∧
      ffi2.ioEvents = s_src_post.ffi.ioEvents := by
  obtain ⟨hmc, hpositive, hsplit, hbase, hlen, htop, hglobals, hdomain,
    haligned, hadj2, hadj4, hleft, hright, hmax, hendian, hinstalled, hlimits⟩ := installed
  have hconfig : mc.target.config = riscvConfig := by rw [hmc.1]; rfl
  have hcomp := compiled
  rw [← hconfig, compileProgMaxAsmExecutable_eq] at hcomp
  have hcfg := oracleBackendConfigOk oracles
  rw [← hconfig] at hcfg
  have hinit := oracleMachineInitOk oracles mc hmc
  rw [← hconfig] at hinit
  have hsem := semanticsDecls_mainFirstHOL (sourceInitialState input) (ofString "main")
    (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have nonfail' : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations ≠ HolBehaviour.fail := by
    change PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) ≠ HolBehaviour.fail at nonfail
    rwa [← hsem] at nonfail
  have hprecise : optionLt (some depth)
      (some (readLimits mc.target.config (oracleCompilerConfig oracles) mc ms).1) = true := by
    change optionLt (some depth)
      (some (readLimits mc.target.config pancakeRiscVBackendConfig mc ms).1) = true
    rw [hlimits]
    simpa only [optionLt, decide_eq_true_eq] using
      (Nat.lt_of_le_of_lt depthBound oracle_stack_bound_fits)
  exact pan_to_target_compile_clocked_halt (oracleCompilerConfig oracles) mc
    sourceDeclarations bytes bitmaps c (some depth) (sourceInitialState input)
    (sourceFfi input) ms globalsWords heapLen adj2 adj4 cbspace dataSp (ofString "main")
    ⟨hcomp, sourceGoodCode, sourceDistinctParams, sourceDistinctFunctions,
      rfl, rfl, rfl, sourceExceptionBound, rfl, hcfg, riscvMachineConfigOk mc hmc,
      hinit, by rw [hconfig]; decide, hpositive,
      by simpa only [sourceDeclarations, globalsWords] using sourceGlobalsSize.symm,
      hsplit, hbase, source_globals_allocatable input,
      hlen, htop, hglobals, hdomain, haligned, hadj2, hadj4, hleft, hright, hmax,
      oracleHeapLimit_lt oracles, rfl, hendian, trivial, hinstalled, rfl, nonfail'⟩
    hprecise stCtxt s_decls hst hev_decls k_pan res_src s_src_post outcome hev_call hclass_src

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target in
/-- Clocked endpoint halt theorem for `baselineMachineConfig` at any post-bootstrap state `ms`
related to `installedAsm`, parameterized only by the oracle compilation equation and stack bound! -/
theorem oracle_baseline_endpoint_clocked_halt (oracles : List (Option (Spt Nat)))
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
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact 64))
    (s_src_post : PanSemStateFiniteExact 64 Guest.HostMemory) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome) :
    ∃ k_target ms2 ffi2,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) k_target ms = (.halt outcome, ms2, ffi2) ∧
      ffi2.ioEvents = s_src_post.ffi.ioEvents :=
  oracle_baseline_clocked_halt oracles input baselineMachineConfig ms
    InitECandidate.nativeCode InitECandidate.bitmaps c depth baselineHeapLen
    baselineAdj2 baselineAdj4 3788 0 compiled depthBound
    (oracle_baseline_installation_transport input c ms related installed) nonfail
    stCtxt s_decls hst hev_decls k_pan res_src s_src_post outcome hev_call hclass_src

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig in
/-- Full end-to-end clocked halt from `baselineInitialState input` (including the 23,132-step
bootstrap): if `sourceDeclarations` halts on `sourceInitialState input` at clock `k_pan` with
`outcome`, then `baselineInitialState input` halts at `bootstrapSteps + k_target` with `outcome`
and the exact same I/O events! -/
theorem oracle_full_baseline_clocked_halt (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact 64))
    (s_src_post : PanSemStateFiniteExact 64 Guest.HostMemory) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome) :
    ∃ k_target ms2 ffi2,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        (bootstrapSteps + k_target)
        (baselineInitialState input) = (.halt outcome, ms2, ffi2) ∧
      ffi2.ioEvents = s_src_post.ffi.ioEvents := by
  obtain ⟨post, shift, related⟩ := full_baseline_evaluator_exact input
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ :=
    oracle_baseline_endpoint_clocked_halt oracles input c depth post related
      compiled depthBound installed nonfail stCtxt s_decls hst hev_decls
      k_pan res_src s_src_post outcome hev_call hclass_src
  exact ⟨k_target, ms2, ffi2, (shift k_target).trans htarget, hio⟩

open Classical in
/-- If `PanSemStateFiniteExact.semanticsDecls s start decls = .terminate outcome events`,
then declaration evaluation succeeds (`stCtxt`, `s_decls`), no clock ever produces `.RunError`,
and there exists a finite clock `k_pan` at which `evaluateHOLFiniteState { s_decls with clock := k_pan }`
completes with `panEntryClass res_src = .CompleteResult outcome` and `s_src_post.ffi.ioEvents = events`. -/
theorem semanticsDecls_terminate_extract {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (start : MlS) (decls : List (DeclHOL width))
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hterm : PanSemStateFiniteExact.semanticsDecls s start decls = .terminate outcome events) :
    ∃ stCtxt s_decls,
      decsStcnamesHOLExact [] decls = some stCtxt ∧
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
        decls = some s_decls ∧
      (∀ k, panEntryClass (PanSemStateFiniteExact.evaluateHOLFiniteState
        { s_decls with clock := k } (.call none start [] : ProgHOL width)).1 ≠ .RunError) ∧
      ∃ k_pan res_src s_src_post,
        PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
          (.call none start [] : ProgHOL width) = (res_src, s_src_post) ∧
        panEntryClass res_src = .CompleteResult outcome ∧
        s_src_post.ffi.ioEvents = events := by
  unfold PanSemStateFiniteExact.semanticsDecls at hterm
  cases hst : decsStcnamesHOLExact [] decls with
  | none => rw [hst] at hterm; cases hterm
  | some stCtxt =>
    rw [hst] at hterm
    dsimp only at hterm
    have hdec_eq : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { s with structs := stCtxt } (Classical.decPred _) decls =
      @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a)) decls := by
      congr
    rw [hdec_eq] at hterm
    cases hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
        { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a)) decls with
    | none => rw [hev_decls] at hterm; cases hterm
    | some s_decls =>
      rw [hev_decls] at hterm
      dsimp only at hterm
      rw [panSemIsWrapper] at hterm
      unfold crepToLoopSemanticsWrapper at hterm
      by_cases herr : ∃ k v,
          (Prod.map panEntryClass (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘
            fun k => PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
              (.call none start [] : ProgHOL width)) k = (.RunError, v)
      · rw [if_pos herr] at hterm; cases hterm
      · rw [if_neg herr] at hterm
        cases hsome : holOptionSome (fun res => ∃ k r ev,
            (Prod.map panEntryClass (fun t : PanSemStateFiniteExact width σ => t.ffi.ioEvents) ∘
              fun k => PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
                (.call none start [] : ProgHOL width)) k = (.CompleteResult r, ev) ∧
            res = HolBehaviour.terminate r ev) with
        | none => rw [hsome] at hterm; cases hterm
        | some res =>
          rw [hsome] at hterm
          subst hterm
          obtain ⟨k_pan, r, ev, hk, heq⟩ := holOptionSome_some hsome
          injection heq with hr hev
          subst hr hev
          refine ⟨stCtxt, s_decls, rfl, hev_decls, ?_, ?_⟩
          · intro k hk_err
            apply herr
            exact ⟨k, (PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
              (.call none start [])).2.ffi.ioEvents, Prod.ext hk_err rfl⟩
          · rcases hrun : PanSemStateFiniteExact.evaluateHOLFiniteState
              { s_decls with clock := k_pan } (.call none start []) with ⟨res_src, s_src_post⟩
            simp only [Function.comp_apply, Prod.map, hrun, Prod.mk.injEq] at hk
            exact ⟨k_pan, res_src, s_src_post, hrun, hk.1, hk.2⟩

open Classical in
/-- Under `PanSemStateFiniteExact.semanticsDecls s start decls = .terminate outcome events`,
any clock `K_pan` at which `{ s_decls with clock := K_pan }` does not time out (`res_src ≠ some .timeOut`)
necessarily completes with `panEntryClass res_src = .CompleteResult outcome` and
`s_src_post.ffi.ioEvents = events`! -/
theorem semanticsDecls_terminate_at_clock {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (start : MlS) (decls : List (DeclHOL width))
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hterm : PanSemStateFiniteExact.semanticsDecls s start decls = .terminate outcome events)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] decls = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
      decls = some s_decls)
    (K_pan : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hnt : res_src ≠ some .timeOut) :
    panEntryClass res_src = .CompleteResult outcome ∧
    s_src_post.ffi.ioEvents = events := by
  obtain ⟨stCtxt', s_decls', hst', hev_decls', _, k_pan, res0, post0, hev0, hclass0, hio0⟩ :=
    semanticsDecls_terminate_extract s start decls outcome events hterm
  rw [hst] at hst'; cases hst'
  rw [hev_decls] at hev_decls'; cases hev_decls'
  have hnt0 : res0 ≠ some .timeOut := by
    intro h; subst h; cases hclass0
  have hadd0 := panPropsEvaluateAddClockEq (.call none start [])
    { s_decls with clock := k_pan } res0 post0 K_pan ⟨hev0, hnt0⟩
  have haddK := panPropsEvaluateAddClockEq (.call none start [])
    { s_decls with clock := K_pan } res_src s_src_post k_pan ⟨hev_call, hnt⟩
  simp only [ Nat.add_comm K_pan k_pan ] at haddK
  rw [hadd0] at haddK
  injection haddK with hres hpost
  have hffi : s_src_post.ffi = post0.ffi := by
    have := congrArg PanSemStateFiniteExact.ffi hpost
    exact this.symm
  exact ⟨hres ▸ hclass0, (congrArg HolFfiState.ioEvents hffi).trans hio0⟩

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL) in
/-- Direct clocked target halt from `sourceBehaviour input = .terminate outcome events`
and any clock `K_pan` at which `{ s_decls with clock := K_pan }` does not time out! -/
theorem oracle_full_baseline_clocked_halt_at (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (K_pan : Nat) (res_src : Option (PanSemResultExact 64))
    (s_src_post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := K_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post))
    (hnt : res_src ≠ some .timeOut) :
    ∃ k_target ms2 ffi2,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        (bootstrapSteps + k_target)
        (baselineInitialState input) = (.halt outcome, ms2, ffi2) ∧
      ffi2.ioEvents = events := by
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]; intro h; cases h
  have hsem := semanticsDecls_mainFirstHOL (sourceInitialState input) (ofString "main")
    (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have hterm : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations = .terminate outcome events :=
    hsem.trans source
  obtain ⟨hclass_src, hio_src⟩ :=
    semanticsDecls_terminate_at_clock (sourceInitialState input) (ofString "main")
      sourceDeclarations outcome events hterm stCtxt s_decls hst hev_decls
      K_pan res_src s_src_post hev_call hnt
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ :=
    oracle_full_baseline_clocked_halt oracles input c depth compiled depthBound installed
      nonfail stCtxt s_decls hst hev_decls K_pan res_src s_src_post outcome hev_call hclass_src
  exact ⟨k_target, ms2, ffi2, htarget, hio.trans hio_src⟩

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL) in
/-- Direct constructive target halt witness from `sourceBehaviour input = .terminate outcome events`
through the complete 14-pass clocked compiler chain (`oracle_full_baseline_clocked_halt`),
bypassing `target_has_behaviour` completely! -/
theorem oracle_full_baseline_terminate_clocked_halt (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events) :
    ∃ k_target ms2 ffi2,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        (bootstrapSteps + k_target)
        (baselineInitialState input) = (.halt outcome, ms2, ffi2) ∧
      ffi2.ioEvents = events := by
  have hsem := semanticsDecls_mainFirstHOL (sourceInitialState input) (ofString "main")
    (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have hterm : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations = .terminate outcome events :=
    hsem.trans source
  obtain ⟨stCtxt, s_decls, hst, hev_decls, _, k_pan, res_src, s_src_post, hev_call, hclass_src, _⟩ :=
    semanticsDecls_terminate_extract (sourceInitialState input) (ofString "main")
      sourceDeclarations outcome events hterm
  have hnt : res_src ≠ some .timeOut := by
    intro h; subst h; cases hclass_src
  exact oracle_full_baseline_clocked_halt_at oracles input c depth compiled depthBound installed
    outcome events source stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hnt

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanToTarget (semanticsDecls_mainFirstHOL) in
/-- Constructive post-bootstrap target halt witness from `sourceBehaviour input = .terminate outcome events`
through `oracle_baseline_endpoint_clocked_halt`, bypassing `target_has_behaviour` completely! -/
theorem oracle_baseline_endpoint_terminate_clocked_halt (oracles : List (Option (Spt Nat)))
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
    ∃ k_target ms2 ffi2,
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) k_target ms = (.halt outcome, ms2, ffi2) ∧
      ffi2.ioEvents = events := by
  have nonfail : sourceBehaviour input ≠ HolBehaviour.fail := by
    rw [source]; intro h; cases h
  have hsem := semanticsDecls_mainFirstHOL (sourceInitialState input) (ofString "main")
    (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) sourceHasMain
  have hterm : PanSemStateFiniteExact.semanticsDecls (sourceInitialState input)
      (ofString "main") sourceDeclarations = .terminate outcome events :=
    hsem.trans source
  obtain ⟨stCtxt, s_decls, hst, hev_decls, _, k_pan, res_src, s_src_post, hev_call, hclass_src, hio_src⟩ :=
    semanticsDecls_terminate_extract (sourceInitialState input) (ofString "main")
      sourceDeclarations outcome events hterm
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ :=
    oracle_baseline_endpoint_clocked_halt oracles input c depth ms related compiled depthBound
      installed nonfail stCtxt s_decls hst hev_decls k_pan res_src s_src_post outcome hev_call hclass_src
  exact ⟨k_target, ms2, ffi2, htarget, hio.trans hio_src⟩

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig in
/-- Constructive `matchingExecutionAt` witness directly from `oracle_full_baseline_terminate_clocked_halt`,
bypassing `target_has_behaviour`, `machineSemHOL`, and `OracleBaselineCorrectness` completely! -/
theorem oracle_full_baseline_matchingExecutionAt_of_clocked_halt (submission : Submission)
    (hmc : submission.machineConfig = baselineMachineConfig)
    (hinit : submission.initialState = baselineInitialState)
    (oracles : List (Option (Spt Nat)))
    (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (input : Guest.InputBlob) (outcome : HolOutcome) (events : List HolIoEvent)
    (source : sourceBehaviour input = .terminate outcome events)
    (covered : coveredOutcome outcome) :
    ∃ k_target, matchingExecutionAt submission input outcome events (bootstrapSteps + k_target) := by
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact baseline_pan_installed input
  have hinst := oracle_baseline_installation input c hmem
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ :=
    oracle_full_baseline_terminate_clocked_halt oracles input c depth compiled depthBound
      hinst outcome events source
  refine ⟨k_target, outcome, ms2, ffi2, ?_, ?_⟩
  · rw [hmc, hinit]
    exact htarget
  · rw [← hio]
    exact matchingResult_refl input outcome ffi2.ioEvents covered

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig in
/-- Direct `InitE.Certificate submission .infinity` proved constructively from
`oracle_full_baseline_matchingExecutionAt_of_clocked_halt` without `target_has_behaviour`! -/
theorem oracle_full_baseline_certificate_infinity_of_clocked_halt (submission : Submission)
    (score : submission.K = .infinity)
    (admitted : submission.Admitted)
    (hmc : submission.machineConfig = baselineMachineConfig)
    (hinit : submission.initialState = baselineInitialState)
    (oracles : List (Option (Spt Nat)))
    (c : Backend.Config) (depth : Nat)
    (hlab : c.labConf = baselineLabConfig)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480) :
    InitE.Certificate submission .infinity := by
  refine ⟨score, admitted, ?_⟩
  intro input _ outcome events source covered
  obtain ⟨k_target, hmatch⟩ :=
    oracle_full_baseline_matchingExecutionAt_of_clocked_halt submission hmc hinit oracles c depth
      hlab compiled depthBound input outcome events source covered
  exact ⟨bootstrapSteps + k_target, trivial, hmatch⟩

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target in
/-- Direct finite-`K` `InitE.Certificate submission (.finite K)` proved constructively from
`oracle_baseline_endpoint_terminate_clocked_halt` + `evaluateTarget_halt_of_not_timeOut_and_halt`,
bypassing `target_has_behaviour` and `machineSemHOL` completely! -/
theorem oracle_full_baseline_certificate_of_clocked_halt_and_not_timeOut (submission : Submission)
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
  refine certificate_of_bounded_behaviour submission K score admitted ?_
  intro input hgas outcome events source covered
  obtain ⟨post, shift, related⟩ := full_baseline_evaluator_exact input
  have hmem : panInstalled InitECandidate.nativeCode 3788 InitECandidate.bitmaps 0
      c.labConf.ffiNames (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      baselineMachineConfig c.labConf.shmemExtra baselineInstalledState
      (wlabWlocExact ∘ (sourceInitialState input).memory)
      (sourceInitialState input).memaddrs (sourceInitialState input).shMemaddrs := by
    rw [hlab]
    exact baseline_pan_installed input
  have hinst := oracle_baseline_installation input c hmem
  obtain ⟨k0, ms0, ffi0, hhalt0, hio0⟩ :=
    oracle_baseline_endpoint_terminate_clocked_halt oracles input c depth post related
      compiled depthBound hinst outcome events source
  have hnt := not_timeOut_post input hgas outcome events source covered post related
  obtain ⟨ms1, hhaltK⟩ := evaluateTarget_halt_of_not_timeOut_and_halt
    baselineMachineConfig (sourceFfi input) post k0 K_post outcome ms0 ffi0 hhalt0 hnt
  refine ⟨bootstrapSteps + K_post, hK, outcome, ms1, ffi0, ?_, ?_⟩
  · rw [hmc, hinit]
    exact (shift K_post).trans hhaltK
  · rw [← hio0]
    exact matchingResult_refl input outcome ffi0.ioEvents covered

/-- Same-clock `CrepToLoop` non-timeout run agreement: if the compiled `LoopSem` entry call
does not time out at clock `k`, then its result and FFI state agree with the source `CrepSem`
entry call at the exact same clock `k`! -/
theorem crep_to_loop_run_agree_of_not_timeOut {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (t : LoopSemStateFiniteExact width σ)
    (crep_code : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (lc : Nat) (c : AsmArchitecture)
    (prog : CrepProgHOL width) (k : Nat)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (res_loop : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (t1 : LoopSemStateFiniteExact width σ)
    (hmd : s.memaddrs = (fun address => t.mdomain address = true))
    (hbe : s.be = t.be)
    (hsh : s.shMemaddrs = (fun address => t.shMdomain address = true))
    (hffi : s.ffi = t.ffi)
    (hbase : s.baseAddr = t.baseAddr)
    (htop : s.topAddr = t.topAddr)
    (hmem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hglob : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hdist : (crep_code.map Prod.fst).Nodup)
    (hscode : s.code = alistToFmapCodeExact crep_code)
    (htcode : t.code = sptFromAList (compileProgHOLExact c crep_code))
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hmf : (crepToLoopMakeFuncsExactHOL crep_code).lookup start = some (lc, 0))
    (hprog : holAlookup crep_code start = some ([], prog))
    (hev : evalCrepSemHOLProgExact { s with clock := k } (.call none start []) = (res, s1))
    (hne : res ≠ some .error)
    (hev_t : LoopSemStateFiniteExact.evaluate
      (.call none (some lc) [] none : HolLoopProg width)
      { t with clock := k } = (res_loop, t1))
    (hnt : res_loop ≠ some .timeOut) :
    res_loop = Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res ∧
      t1.ffi = s1.ffi := by
  obtain ⟨k', t', hrun', hffi'⟩ := crep_to_loop_clocked_sim s t crep_code start lc c prog k
    res s1 hmd hbe hsh hffi hbase htop hmem hglob hdist hscode htcode hloc hmf hprog hev hne
  have hadd := LoopSemStateFiniteExact.evaluate_add_clock_eq
    (.call none (some lc) [] none : HolLoopProg width)
    { t with clock := k } res_loop t1 k' hev_t hnt
  simp only at hadd
  rw [hadd] at hrun'
  injection hrun' with hr hpost
  exact ⟨hr, (congrArg LoopSemStateFiniteExact.ffi hpost).trans hffi'.symm⟩

open LoopToWordStateRelImpSemanticsSupport in
/-- Same-clock `PanToWord` non-timeout run agreement: under the 24 hypotheses of
`panToWordStateRelImpSemantics`, if `code` evaluates declarations to `s_decls`,
`s_decls` runs `start` at clock `k` without `.RunError`, and `target` (`WordSem`) does
not time out at clock `k + 1`, then `target` at clock `k + 1` has `wordEntryClass res_word =
panEntryClass res_src` and the exact same FFI I/O events `s_src_post.ffi.ioEvents`! -/
theorem pan_to_word_run_agree_of_not_timeOut {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (h : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
      noLabelsHOL target.memory (fun address => target.mdomain address = true) ∧
      start = ofString "main" ∧
      globalsSize = ((decShapesHOL code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum ∧
      distinctParamsHOL (functionsHOL code) ∧
      (fun address => target.mdomain address = true) =
        (fun address => source.memaddrs address ∨ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (fun address => target.shMdomain address = true) = source.shMemaddrs ∧
      target.be = source.be ∧ target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word heapLen) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * heapLen - panBytesInWord width * BitVec.ofNat width globalsSize ∧
      ((functionsHOL code).map Prod.fst).Nodup ∧ panGlobalsByteAlignedHOL source.topAddr ∧
      globalsAllocatableHOL source code ∧ source.code = HolFiniteMapExact.empty ∧
      target.code = sptFromAList (panToWordCompileProgHOL arch code) ∧
      source.globals = HolFiniteMapExact.empty ∧ source.locals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL code < 2 ^ width ∧ source.eshapes = HolFiniteMapExact.empty ∧
      sptLookup 0 target.locals = some (WordLocW.loc 1 0) ∧ goodDimindex width ∧
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError)
    (res_word : Option (WordSemResult width))
    (t_word : WordSemStateFiniteExact width C σ)
    (hrun_w : WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      { target with clock := k + 1 } = (res_word, t_word))
    (hnt_w : res_word ≠ some .timeOut) :
    wordEntryClass res_word = panEntryClass res_src ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents := by
  obtain ⟨k', t_word', res_word', hrun_w', hio_w', hclass_w'⟩ :=
    pan_to_word_clocked_sim source target arch code start globalsSize heapLen h
      stCtxt s_decls hst hev_decls k res_src s_src_post hev_call hne_src
  have hadd := WordSemStateFiniteExact.evaluate_add_clock k'
    (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
    { target with clock := k + 1 } res_word t_word ⟨hrun_w, hnt_w⟩
  simp only at hadd
  rw [hadd] at hrun_w'
  injection hrun_w' with hr hpost
  subst hr
  have hffi_eq : t_word.ffi = t_word'.ffi := by rw [← hpost]
  exact ⟨hclass_w', (congrArg HolFfiState.ioEvents hffi_eq).trans hio_w'⟩

open Classical Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Pancake.Proofs.PanToTarget LoopToWordStateRelImpSemanticsSupport in
/-- Non-timeout target halt agreement for the complete 14-pass `PanToTarget` compiler:
under the 35 hypotheses of `panToTargetCompileSemantics` and the resource-limit guard,
if `pan_code` evaluates declarations to `s_decls`, `s_decls` runs `start` at clock `k_pan`
with `panEntryClass res_src = .CompleteResult outcome`, and `evaluateTargetHOL mc ffi K ms`
does not time out at clock `K`, then `evaluateTargetHOL mc ffi K ms` halts with `outcome`
and the exact same FFI I/O events `s_src_post.ffi.ioEvents`! -/
theorem pan_to_target_compile_halt_agree_of_not_timeOut {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (pan_code : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stack_max : Option Nat) (s : PanSemStateFiniteExact width σ) (ffi : HolFfiState σ)
    (ms : S) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec width)
    (cbspace data_sp : Nat) (start : MlS)
    (h :
      let getReg := mc.target.getReg ms
      compileProgMax c mc pan_code = (some (bytes, bitmaps, c'), stack_max) ∧
      pancakeGoodCodeHOL pan_code = true ∧
      distinctParamsHOL (functionsHOL pan_code) ∧
      ((functionsHOL pan_code).map Prod.fst).Nodup ∧
      s.code = HolFiniteMapExact.empty ∧
      s.locals = HolFiniteMapExact.empty ∧
      s.globals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL pan_code < 2 ^ width ∧
      s.eshapes = HolFiniteMapExact.empty ∧
      backendConfigOk mc.target.config c ∧ LabToTarget.mcConfOk mc ∧
      mcInitOk mc.target.config c mc ∧ mc.target.config.isa ≠ .ag32 ∧
      (0 : BitVec width) < getReg mc.lenReg ∧
      globals_size =
        (let dec_shs := decShapesHOL pan_code
         let struct_ctxt := decsStcnamesHOLExact (width := width) [] pan_code
         (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
      getReg mc.lenReg < getReg mc.ptr2Reg ∧
      getReg mc.lenReg = s.baseAddr ∧
      globalsAllocatableHOL s pan_code ∧
      heap_len = (getReg mc.ptr2Reg + -1 * s.baseAddr).toNat / (width / 8) ∧
      s.topAddr = s.baseAddr + StackRemove.bytesInWord width * BitVec.ofNat width heap_len -
        BitVec.ofNat width (globals_size * width / 8) ∧
      globals_size ≤ heap_len ∧
      s.memaddrs = StackRemove.addresses (getReg mc.lenReg) (heap_len - globals_size) ∧
      holAligned (wordShiftAmount width + 1) (getReg mc.ptr2Reg + -1 * getReg mc.lenReg) = true ∧
      adj_ptr2 = getReg mc.lenReg +
        StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ∧
      adj_ptr4 = getReg mc.len2Reg -
        StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ∧
      adj_ptr2 ≤ getReg mc.ptr2Reg ∧
      getReg mc.ptr2Reg ≤ adj_ptr4 ∧
      (getReg mc.ptr2Reg + -1 * getReg mc.lenReg).toNat ≤
        (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) ∧
      (StackRemove.bytesInWord width).toNat * (2 * DataToWord.maxHeapLimit width c.dataConf - 1) <
        2 ^ width ∧
      s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
      (match c.labConf.ffiNames with
        | none => True
        | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s) ∧
      panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
        (heapRegs c.stackConf.regNames) mc c'.labConf.shmemExtra ms
        (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
      start = ofString "main" ∧
      PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail)
    (hresLimit : optionLt stack_max (some (readLimits mc.target.config c mc ms).1) = true)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] pan_code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
      pan_code = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome)
    (K : Nat)
    (hnt : (evaluateTargetHOL mc ffi K ms).1 ≠ .timeOut) :
    (evaluateTargetHOL mc ffi K ms).1 = .halt outcome ∧
      (evaluateTargetHOL mc ffi K ms).2.2.ioEvents = s_src_post.ffi.ioEvents := by
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ :=
    pan_to_target_compile_clocked_halt c mc pan_code bytes bitmaps c' stack_max s ffi ms
      globals_size heap_len adj_ptr2 adj_ptr4 cbspace data_sp start h hresLimit
      stCtxt s_decls hst hev_decls k_pan res_src s_src_post outcome hev_call hclass_src
  obtain ⟨ms1, hhaltK⟩ := evaluateTarget_halt_of_not_timeOut_and_halt
    mc ffi ms k_target K outcome ms2 ffi2 htarget hnt
  rw [hhaltK]
  exact ⟨rfl, hio⟩

open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.Pancake.PanToTarget in
/-- Non-timeout target halt agreement for `oracle_baseline_clocked_halt`:
for any validated allocation oracles and certified compiler depth `≤ 7480`, if
`sourceDeclarations` runs `"main"` at clock `k_pan` with `.CompleteResult outcome` and
`evaluateTargetHOL mc (sourceFfi input) K ms` does not time out at clock `K`, then
`evaluateTargetHOL mc (sourceFfi input) K ms` halts with `outcome` and identical I/O events! -/
theorem oracle_baseline_halt_agree_of_not_timeOut (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (ms : RiscV.L3.riscv_state) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c : Backend.Config) (depth heapLen : Nat) (adj2 adj4 : BitVec 64)
    (cbspace dataSp : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (bytes, bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input mc ms bytes bitmaps c heapLen adj2 adj4 cbspace dataSp)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact 64))
    (s_src_post : PanSemStateFiniteExact 64 Guest.HostMemory) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome)
    (K : Nat)
    (hnt : (evaluateTargetHOL mc (sourceFfi input) K ms).1 ≠ .timeOut) :
    (evaluateTargetHOL mc (sourceFfi input) K ms).1 = .halt outcome ∧
      (evaluateTargetHOL mc (sourceFfi input) K ms).2.2.ioEvents = s_src_post.ffi.ioEvents := by
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ :=
    oracle_baseline_clocked_halt oracles input mc ms bytes bitmaps c depth heapLen adj2 adj4
      cbspace dataSp compiled depthBound installed nonfail stCtxt s_decls hst hev_decls
      k_pan res_src s_src_post outcome hev_call hclass_src
  obtain ⟨ms1, hhaltK⟩ := evaluateTarget_halt_of_not_timeOut_and_halt
    mc (sourceFfi input) ms k_target K outcome ms2 ffi2 htarget hnt
  rw [hhaltK]
  exact ⟨rfl, hio⟩

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig in
/-- Full end-to-end non-timeout target halt agreement from `baselineInitialState input`
(including the 23,132-step bootstrap): if `sourceDeclarations` halts on `sourceInitialState input`
at clock `k_pan` with `outcome`, and `baselineInitialState input` does not time out at
`bootstrapSteps + K_post`, then `baselineInitialState input` halts at `bootstrapSteps + K_post`
with `outcome` and the exact same I/O events! -/
theorem oracle_full_baseline_halt_agree_of_not_timeOut (oracles : List (Option (Spt Nat)))
    (input : Guest.InputBlob)
    (c : Backend.Config) (depth : Nat)
    (compiled : compileProgMaxAsmExecutable (oracleCompilerConfig oracles) riscvConfig
      sourceDeclarations = (some (InitECandidate.nativeCode, InitECandidate.bitmaps, c), some depth))
    (depthBound : depth ≤ 7480)
    (installed : OracleBaselineInstallation input baselineMachineConfig
      baselineInstalledState InitECandidate.nativeCode InitECandidate.bitmaps
      c baselineHeapLen baselineAdj2 baselineAdj4 3788 0)
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact 64))
    (s_src_post : PanSemStateFiniteExact 64 Guest.HostMemory) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome)
    (K_post : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input)).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
      (bootstrapSteps + K_post) (baselineInitialState input)).1 = .halt outcome ∧
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input)
        (bootstrapSteps + K_post) (baselineInitialState input)).2.2.ioEvents =
        s_src_post.ffi.ioEvents := by
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ :=
    oracle_full_baseline_clocked_halt oracles input c depth compiled depthBound installed
      nonfail stCtxt s_decls hst hev_decls k_pan res_src s_src_post outcome hev_call hclass_src
  obtain ⟨ms1, hhaltK⟩ := evaluateTarget_halt_of_not_timeOut_and_halt
    baselineMachineConfig (sourceFfi input) (baselineInitialState input)
    (bootstrapSteps + k_target) (bootstrapSteps + K_post) outcome ms2 ffi2 htarget hnt
  rw [hhaltK]
  exact ⟨rfl, hio⟩

open InitECandidate.Proofs Flapjack.Compiler.Backend Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.RiscV.Target in
/-- Non-timeout post-bootstrap target halt agreement for `oracle_baseline_endpoint_clocked_halt`:
at any post-bootstrap state `ms` related to `installedAsm`, if `sourceDeclarations` halts on
`sourceInitialState input` at clock `k_pan` with `outcome`, and `evaluateTargetHOL baselineMachineConfig
(sourceFfi input) K ms` does not time out at clock `K`, then it halts with `outcome` and the exact
same I/O events! -/
theorem oracle_baseline_endpoint_halt_agree_of_not_timeOut (oracles : List (Option (Spt Nat)))
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
    (nonfail : sourceBehaviour input ≠ HolBehaviour.fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact 64))
    (s_src_post : PanSemStateFiniteExact 64 Guest.HostMemory) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome)
    (K : Nat)
    (hnt : (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K ms).1 ≠ .timeOut) :
    (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K ms).1 = .halt outcome ∧
      (evaluateTargetHOL baselineMachineConfig (sourceFfi input) K ms).2.2.ioEvents =
        s_src_post.ffi.ioEvents := by
  obtain ⟨k_target, ms2, ffi2, htarget, hio⟩ :=
    oracle_baseline_endpoint_clocked_halt oracles input c depth ms related compiled depthBound
      installed nonfail stCtxt s_decls hst hev_decls k_pan res_src s_src_post outcome hev_call hclass_src
  obtain ⟨ms1, hhaltK⟩ := evaluateTarget_halt_of_not_timeOut_and_halt
    baselineMachineConfig (sourceFfi input) ms k_target K outcome ms2 ffi2 htarget hnt
  rw [hhaltK]
  exact ⟨rfl, hio⟩

open Classical Flapjack.Compiler.Backend Flapjack.Pancake.Proofs.PanToTarget
open StackToLab.Proofs.FullMakeInitSemantics LoopToWordStateRelImpSemanticsSupport in
/-- Non-timeout `WordSem` run agreement for the `PanToWord` stage (`wst0`) inside `PanToTarget`:
under the hypotheses of `pan_to_target_pan_to_word_stage_lab_clocked_sim`, if `s_decls` runs `start`
at clock `k_pan` without `.RunError`, and `wst0` does not time out at clock `K_word`, then `wst0`
at clock `K_word` has `wordEntryClass res_word = panEntryClass res_src` and identical I/O events! -/
theorem pan_to_target_pan_to_word_stage_lab_run_agree_of_not_timeOut
    {width : Nat} [NeZero width] {S Q C σ : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C σ}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (tAsm : AsmState width)
    (m : BitVec width → WordLocW width) (dm dm' sdm : BitVec width → Bool) (ms : S)
    (lcode : LabSem.LabProgHOL width)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (lorac : Nat → C × LabSem.LabProgHOL width)
    (bytes : List (BitVec 8))
    (ac : AsmConfigExact width) (k_reg : Nat) (wcode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : PanSemStateFiniteExact width σ) (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS) (globalsSize heapLen : Nat)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code
      (LabToTarget.makeInit (C := C) mc ffi tAsm m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms lcode comp cbpos cbspace lorac)
      saveRegs dataSp coracle)
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset
      bitmaps code
      (LabToTarget.makeInit (C := C) mc ffi tAsm m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms lcode comp cbpos cbspace lorac)
      saveRegs dataSp coracle = (sst, some x))
    (hmc : LabToTarget.mcConfOk mc)
    (hpm : ∀ a, decide (s.memaddrs a) = true → m a = wlabWlocExact (s.memory a))
    (hgi : goodInitState mc ms bytes cbspace tAsm m dm' sdm)
    (hsdm : (fun a => decide (s.shMemaddrs a)) = fun a => sdm a && holByteAligned a)
    (hbase : mc.target.getReg ms mc.lenReg = s.baseAddr)
    (hlt : mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg)
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * maxHeap)
    (hheapLt : (StackRemove.bytesInWord width).toNat * maxHeap < 2 ^ width)
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
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
    (hfail : PanSemStateFiniteExact.semanticsDecls s start panCode ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { s with structs := stCtxt } (fun a => Classical.propDecidable (s.memaddrs a))
      panCode = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError)
    (res_word : Option (WordSemResult width))
    (t_word : WordSemStateFiniteExact width (Nat × C) σ)
    (hrun_w : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec width))
      { { WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac with
          code := sptFromAList (panToWordCompileProgHOL isa panCode) } with clock := k_pan + 1 } =
      (res_word, t_word))
    (hnt_w : res_word ≠ some .timeOut) :
    wordEntryClass res_word = panEntryClass res_src ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents := by
  obtain ⟨k', t_word', res_word', hrun_w', hio_w', hclass_w'⟩ :=
    pan_to_target_pan_to_word_stage_lab_clocked_sim mc ffi tAsm m dm dm' sdm ms lcode comp
      cbpos cbspace lorac bytes ac k_reg wcode worac s isa panCode start globalsSize heapLen
      hA hfmi hmc hpm hgi hsdm hbase hlt hlo hhi hheap hheapLt halign hbe hffi hheapLen hglobLe
      hmemaddrs htop hstart hsize hparams hnodup halloc hcode hglobals hlocals heids heshapes
      hfail stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src
  have hadd := WordSemStateFiniteExact.evaluate_add_clock k'
    (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec width))
    { { WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac with
        code := sptFromAList (panToWordCompileProgHOL isa panCode) } with clock := k_pan + 1 }
    res_word t_word ⟨hrun_w, hnt_w⟩
  simp only at hadd
  rw [hadd] at hrun_w'
  injection hrun_w' with hr hpost
  subst hr
  have hffi_eq : t_word.ffi = t_word'.ffi := by rw [← hpost]
  exact ⟨hclass_w', (congrArg HolFfiState.ioEvents hffi_eq).trans hio_w'⟩

open Classical Flapjack.Compiler.Backend Flapjack.Pancake.Proofs.PanToTarget
open StackToLab.Proofs.FullMakeInitSemantics LoopToWordStateRelImpSemanticsSupport in
/-- Arbitrary-clock `WordSem` halt agreement for the `PanToWord` stage (`wst0`) inside `PanToTarget`:
under the hypotheses of `pan_to_target_pan_to_word_stage_lab_clocked_sim`, if `s_decls` runs `start`
at clock `k_pan` with `panEntryClass res_src = .CompleteResult outcome`, and `wst0` does not time out
at any clock `K_word`, then `wst0` at clock `K_word` completes with `wordEntryClass res_word =
.CompleteResult outcome` and identical I/O events! -/
theorem pan_to_target_pan_to_word_stage_lab_halt_of_word_not_timeOut
    {width : Nat} [NeZero width] {S Q C σ : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × StackLang.HolProg width)} {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × StackLang.HolProg width) × List (BitVec width)}
    {sst x : StackSemStateFiniteExact width C σ}
    (mc : MachineConfig width S Q) (ffi : HolFfiState σ) (tAsm : AsmState width)
    (m : BitVec width → WordLocW width) (dm dm' sdm : BitVec width → Bool) (ms : S)
    (lcode : LabSem.LabProgHOL width)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (lorac : Nat → C × LabSem.LabProgHOL width)
    (bytes : List (BitVec 8))
    (ac : AsmConfigExact width) (k_reg : Nat) (wcode : Spt (Nat × WordLangProgHOL (BitVec width)))
    (worac : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : PanSemStateFiniteExact width σ) (isa : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS) (globalsSize heapLen : Nat)
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code
      (LabToTarget.makeInit (C := C) mc ffi tAsm m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms lcode comp cbpos cbspace lorac)
      saveRegs dataSp coracle)
    (hfmi : StackToLab.Proofs.FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset
      bitmaps code
      (LabToTarget.makeInit (C := C) mc ffi tAsm m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms lcode comp cbpos cbspace lorac)
      saveRegs dataSp coracle = (sst, some x))
    (hmc : LabToTarget.mcConfOk mc)
    (hpm : ∀ a, decide (s.memaddrs a) = true → m a = wlabWlocExact (s.memory a))
    (hgi : goodInitState mc ms bytes cbspace tAsm m dm' sdm)
    (hsdm : (fun a => decide (s.shMemaddrs a)) = fun a => sdm a && holByteAligned a)
    (hbase : mc.target.getReg ms mc.lenReg = s.baseAddr)
    (hlt : mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg)
    (hlo : mc.target.getReg ms mc.lenReg +
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc ≤
        mc.target.getReg ms mc.ptr2Reg)
    (hhi : mc.target.getReg ms mc.ptr2Reg ≤ mc.target.getReg ms mc.len2Reg -
      StackRemove.bytesInWord width * BitVec.ofNat width StackRemove.maxStackAlloc)
    (hheap : (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (StackRemove.bytesInWord width).toNat * maxHeap)
    (hheapLt : (StackRemove.bytesInWord width).toNat * maxHeap < 2 ^ width)
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
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (halloc : globalsAllocatableHOL s panCode) (hcode : s.code = HolFiniteMapExact.empty)
    (hglobals : s.globals = HolFiniteMapExact.empty)
    (hlocals : s.locals = HolFiniteMapExact.empty) (heids : sizeOfEidsHOL panCode < 2 ^ width)
    (heshapes : s.eshapes = HolFiniteMapExact.empty)
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
    (K_word : Nat)
    (res_word : Option (WordSemResult width))
    (t_word : WordSemStateFiniteExact width (Nat × C) σ)
    (hrun_w : WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec width))
      { { WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac with
          code := sptFromAList (panToWordCompileProgHOL isa panCode) } with clock := K_word } =
      (res_word, t_word))
    (hnt_w : res_word ≠ some .timeOut) :
    wordEntryClass res_word = .CompleteResult outcome ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents := by
  have hne_src : panEntryClass res_src ≠ .RunError := by
    rw [hclass_src]; intro herr; cases herr
  obtain ⟨k', t_word', res_word', hrun_w', hio_w', hclass_w'⟩ :=
    pan_to_target_pan_to_word_stage_lab_clocked_sim mc ffi tAsm m dm dm' sdm ms lcode comp
      cbpos cbspace lorac bytes ac k_reg wcode worac s isa panCode start globalsSize heapLen
      hA hfmi hmc hpm hgi hsdm hbase hlt hlo hhi hheap hheapLt halign hbe hffi hheapLen hglobLe
      hmemaddrs htop hstart hsize hparams hnodup halloc hcode hglobals hlocals heids heshapes
      hfail stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src
  have hcw' : wordEntryClass res_word' = .CompleteResult outcome := hclass_w'.trans hclass_src
  have hnt_w' : res_word' ≠ some .timeOut := by
    intro h; subst h; cases hcw'
  obtain ⟨hr, hffi_eq⟩ := wordEvaluateIgnoreClocks
    (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
    { WordToStack.Native.Initialization.makeInit ac k_reg sst wcode worac with
      code := sptFromAList (panToWordCompileProgHOL isa panCode) }
    K_word ((k_pan + 1) + k') res_word res_word' t_word t_word'
    hrun_w hnt_w hrun_w' hnt_w'
  subst hr
  exact ⟨hcw', (congrArg HolFfiState.ioEvents hffi_eq).trans hio_w'⟩

open LoopToWordStateRelImpSemanticsSupport in
/-- Arbitrary-clock `WordSem` halt agreement for `pan_to_word_clocked_sim`:
under the 24 hypotheses of `panToWordStateRelImpSemantics`, if `code` evaluates declarations to
`s_decls`, `s_decls` runs `start` at clock `k` with `panEntryClass res_src = .CompleteResult outcome`,
and `target` (`WordSem`) does not time out at any clock `K_word` (`res_word ≠ some .timeOut`), then
`target` at clock `K_word` completes with `wordEntryClass res_word = .CompleteResult outcome` and
identical I/O events! -/
theorem pan_to_word_halt_of_word_not_timeOut {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (h : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
      noLabelsHOL target.memory (fun address => target.mdomain address = true) ∧
      start = ofString "main" ∧
      globalsSize = ((decShapesHOL code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum ∧
      distinctParamsHOL (functionsHOL code) ∧
      (fun address => target.mdomain address = true) =
        (fun address => source.memaddrs address ∨ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (fun address => target.shMdomain address = true) = source.shMemaddrs ∧
      target.be = source.be ∧ target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word heapLen) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * heapLen - panBytesInWord width * BitVec.ofNat width globalsSize ∧
      ((functionsHOL code).map Prod.fst).Nodup ∧ panGlobalsByteAlignedHOL source.topAddr ∧
      globalsAllocatableHOL source code ∧ source.code = HolFiniteMapExact.empty ∧
      target.code = sptFromAList (panToWordCompileProgHOL arch code) ∧
      source.globals = HolFiniteMapExact.empty ∧ source.locals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL code < 2 ^ width ∧ source.eshapes = HolFiniteMapExact.empty ∧
      sptLookup 0 target.locals = some (WordLocW.loc 1 0) ∧ goodDimindex width ∧
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ) (outcome : HolOutcome)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hclass_src : panEntryClass res_src = .CompleteResult outcome)
    (K_word : Nat) (res_word : Option (WordSemResult width))
    (t_word : WordSemStateFiniteExact width C σ)
    (hrun_w : WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      { target with clock := K_word } = (res_word, t_word))
    (hnt_w : res_word ≠ some .timeOut) :
    wordEntryClass res_word = .CompleteResult outcome ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents := by
  have hne_src : panEntryClass res_src ≠ .RunError := by
    rw [hclass_src]; intro herr; cases herr
  obtain ⟨k', t_word', res_word', hrun_w', hio_w', hclass_w'⟩ :=
    pan_to_word_clocked_sim source target arch code start globalsSize heapLen h stCtxt s_decls
      hst hev_decls k res_src s_src_post hev_call hne_src
  have hcw' : wordEntryClass res_word' = .CompleteResult outcome := hclass_w'.trans hclass_src
  have hnt_w' : res_word' ≠ some .timeOut := by
    intro ht; subst ht; cases hcw'
  obtain ⟨hr, hffi_eq⟩ := wordEvaluateIgnoreClocks
    (.call none (some firstLoopName) [0] none) target K_word ((k + 1) + k')
    res_word res_word' t_word t_word' hrun_w hnt_w hrun_w' hnt_w'
  subst hr
  exact ⟨hcw', (congrArg HolFfiState.ioEvents hffi_eq).trans hio_w'⟩

/-- Two non-`.timeOut` `evalCrepSemHOLProgExact` runs on the same program and state
(at clocks `k` and `k'`) produce the exact same result and FFI state (`evalCrepSemHOLProgExact_add_clock_eq`). -/
theorem crepEvaluateIgnoreClocks {width : Nat} [NeZero width] {σ : Type}
    (prog : CrepProgHOL width)
    (s : CrepSemHOLState width σ)
    (k k' : Nat) (r1 r2 : Option (CrepResultHOLExact width))
    (post1 post2 : CrepSemHOLState width σ)
    (h1 : evalCrepSemHOLProgExact { s with clock := k } prog = (r1, post1))
    (hnt1 : r1 ≠ some .timeOut)
    (h2 : evalCrepSemHOLProgExact { s with clock := k' } prog = (r2, post2))
    (hnt2 : r2 ≠ some .timeOut) :
    r1 = r2 ∧ post1.ffi = post2.ffi := by
  have ha1 := evalCrepSemHOLProgExact_add_clock_eq prog { s with clock := k } r1 post1 k' h1 hnt1
  have ha2 := evalCrepSemHOLProgExact_add_clock_eq prog { s with clock := k' } r2 post2 k h2 hnt2
  have heq1 : ({ { s with clock := k } with clock := k + k' } : CrepSemHOLState width σ) =
      { s with clock := k + k' } := by cases s; rfl
  have heq2 : ({ { s with clock := k' } with clock := k' + k } : CrepSemHOLState width σ) =
      { s with clock := k + k' } := by
    have hc : k' + k = k + k' := Nat.add_comm k' k
    cases s; simp [hc]
  simp only at ha1 ha2
  rw [heq1] at ha1
  rw [heq2] at ha2
  rw [ha1] at ha2
  injection ha2 with hr hpost
  have hffi : ({ post1 with clock := post1.clock + k' } : CrepSemHOLState width σ).ffi =
      ({ post2 with clock := post2.clock + k } : CrepSemHOLState width σ).ffi :=
    congrArg CrepSemHOLState.ffi hpost
  exact ⟨hr, hffi⟩

/-- Two non-`.timeOut` `LoopSemStateFiniteExact.evaluate` runs on the same program and state
(at clocks `k` and `k'`) produce the exact same result and FFI state (`LoopSemStateFiniteExact.evaluate_add_clock_eq`). -/
theorem loopEvaluateIgnoreClocks {width : Nat} [NeZero width] {F : Type}
    (prog : HolLoopProg width)
    (s : LoopSemStateFiniteExact width F)
    (k k' : Nat) (r1 r2 : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (post1 post2 : LoopSemStateFiniteExact width F)
    (h1 : LoopSemStateFiniteExact.evaluate prog { s with clock := k } = (r1, post1))
    (hnt1 : r1 ≠ some .timeOut)
    (h2 : LoopSemStateFiniteExact.evaluate prog { s with clock := k' } = (r2, post2))
    (hnt2 : r2 ≠ some .timeOut) :
    r1 = r2 ∧ post1.ffi = post2.ffi := by
  have ha1 := LoopSemStateFiniteExact.evaluate_add_clock_eq prog { s with clock := k } r1 post1 k' h1 hnt1
  have ha2 := LoopSemStateFiniteExact.evaluate_add_clock_eq prog { s with clock := k' } r2 post2 k h2 hnt2
  have heq1 : ({ { s with clock := k } with clock := k + k' } : LoopSemStateFiniteExact width F) =
      { s with clock := k + k' } := by cases s; rfl
  have heq2 : ({ { s with clock := k' } with clock := k' + k } : LoopSemStateFiniteExact width F) =
      { s with clock := k + k' } := by
    have hc : k' + k = k + k' := Nat.add_comm k' k
    cases s; simp [hc]
  simp only at ha1 ha2
  rw [heq1] at ha1
  rw [heq2] at ha2
  rw [ha1] at ha2
  injection ha2 with hr hpost
  have hffi : ({ post1 with clock := post1.clock + k' } : LoopSemStateFiniteExact width F).ffi =
      ({ post2 with clock := post2.clock + k } : LoopSemStateFiniteExact width F).ffi :=
    congrArg LoopSemStateFiniteExact.ffi hpost
  exact ⟨hr, hffi⟩

/-- Arbitrary-clock `CrepToLoop` non-timeout run agreement: if `s` (`CrepSem`) runs `start`
at clock `k` without `.error`, and `t` (`LoopSem`) does not time out at any clock `K_loop`,
then `t` at clock `K_loop` produces `resultToLoop res` and identical FFI state `s1.ffi`! -/
theorem crep_to_loop_halt_of_loop_not_timeOut {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (t : LoopSemStateFiniteExact width σ)
    (crep_code : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (lc : Nat) (c : AsmArchitecture)
    (prog : CrepProgHOL width) (k : Nat)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (K_loop : Nat)
    (res_loop : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (t1 : LoopSemStateFiniteExact width σ)
    (hmd : s.memaddrs = (fun address => t.mdomain address = true))
    (hbe : s.be = t.be)
    (hsh : s.shMemaddrs = (fun address => t.shMdomain address = true))
    (hffi : s.ffi = t.ffi)
    (hbase : s.baseAddr = t.baseAddr)
    (htop : s.topAddr = t.topAddr)
    (hmem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hglob : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hdist : (crep_code.map Prod.fst).Nodup)
    (hscode : s.code = alistToFmapCodeExact crep_code)
    (htcode : t.code = sptFromAList (compileProgHOLExact c crep_code))
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hmf : (crepToLoopMakeFuncsExactHOL crep_code).lookup start = some (lc, 0))
    (hprog : holAlookup crep_code start = some ([], prog))
    (hev : evalCrepSemHOLProgExact { s with clock := k } (.call none start []) = (res, s1))
    (hne : res ≠ some .error)
    (hnt_src : res ≠ some .timeOut)
    (hev_t : LoopSemStateFiniteExact.evaluate
      (.call none (some lc) [] none : HolLoopProg width)
      { t with clock := K_loop } = (res_loop, t1))
    (hnt : res_loop ≠ some .timeOut) :
    res_loop = Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res ∧
      t1.ffi = s1.ffi := by
  obtain ⟨k', t', hrun', hffi'⟩ := crep_to_loop_clocked_sim s t crep_code start lc c prog k
    res s1 hmd hbe hsh hffi hbase htop hmem hglob hdist hscode htcode hloc hmf hprog hev hne
  have hnt' : Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res ≠ some .timeOut := by
    rcases res with _ | r_val
    · intro h; cases h
    · cases r_val <;> intro h <;> first | exact hnt_src rfl | cases h
  obtain ⟨hr, hffi_eq⟩ := loopEvaluateIgnoreClocks
    (.call none (some lc) [] none) t K_loop (k + k')
    res_loop (Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res)
    t1 t' hev_t hnt hrun' hnt'
  exact ⟨hr, hffi_eq.trans hffi'.symm⟩

/-- Two non-`.timeOut` `PanSemStateFiniteExact.evaluateHOLFiniteState` runs on the same program and state
(at clocks `k` and `k'`) produce the exact same result and FFI state (`panPropsEvaluateAddClockEq`). -/
theorem panEvaluateIgnoreClocks {width : Nat} [NeZero width] {σ : Type}
    (prog : ProgHOL width)
    (s : PanSemStateFiniteExact width σ)
    (k k' : Nat) (r1 r2 : Option (PanSemResultExact width))
    (post1 post2 : PanSemStateFiniteExact width σ)
    (h1 : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k } prog = (r1, post1))
    (hnt1 : r1 ≠ some .timeOut)
    (h2 : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k' } prog = (r2, post2))
    (hnt2 : r2 ≠ some .timeOut) :
    r1 = r2 ∧ post1.ffi = post2.ffi := by
  have ha1 := panPropsEvaluateAddClockEq prog { s with clock := k } r1 post1 k' ⟨h1, hnt1⟩
  have ha2 := panPropsEvaluateAddClockEq prog { s with clock := k' } r2 post2 k ⟨h2, hnt2⟩
  simp only [Nat.add_comm k' k] at ha2
  rw [ha1] at ha2
  injection ha2 with hr hpost
  have hffi : ({ post1 with clock := post1.clock + k' } : PanSemStateFiniteExact width σ).ffi =
      ({ post2 with clock := post2.clock + k } : PanSemStateFiniteExact width σ).ffi :=
    congrArg PanSemStateFiniteExact.ffi hpost
  exact ⟨hr, hffi⟩

open Classical in
/-- Under `crepSemantics s start = .terminate outcome events`, any clock `k`
at which `(evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ≠ some .timeOut`
completes with `crepResultOutcome res = some outcome` and `post.ffi.ioEvents = events`! -/
theorem crep_halt_of_not_timeOut {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (start : MlString)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hsem : crepSemantics s start = .terminate outcome events)
    (k : Nat) (res : Option (CrepResultHOLExact width))
    (post : CrepSemHOLState width σ)
    (hrun : evalCrepSemHOLProgExact { s with clock := k } (.call none start []) = (res, post))
    (hnt : res ≠ some .timeOut) :
    crepResultOutcome res = some outcome ∧
    post.ffi.ioEvents = events := by
  rw [crepSemIsWrapper] at hsem
  unfold crepToLoopSemanticsWrapper at hsem
  dsimp only at hsem
  split at hsem
  · cases hsem
  · rename_i hnoerr
    split at hsem
    · rename_i b hsome
      subst hsem
      obtain ⟨k0, out0, ev0, hk0, heq⟩ := holOptionSome_some hsome
      injection heq with hout0 hev0
      subst hout0 hev0
      simp only [Function.comp_apply, Prod.map] at hk0
      rcases hrun0 : evalCrepSemHOLProgExact { s with clock := k0 }
        (.call none start []) with ⟨res0, post0⟩
      rw [hrun0] at hk0
      simp only [Prod.mk.injEq] at hk0
      obtain ⟨hclass0, rfl⟩ := hk0
      have hnt0 : res0 ≠ some .timeOut := by
        intro h; subst h; cases hclass0
      obtain ⟨hr, hffi⟩ := crepEvaluateIgnoreClocks (.call none start [])
        s k k0 res res0 post post0 hrun hnt hrun0 hnt0
      subst hr
      refine ⟨?_, congrArg HolFfiState.ioEvents hffi⟩
      rcases res with _ | (_ | _ | _ | _ | _ | _) <;>
        simp [crepResultOutcome] at hclass0 ⊢ <;> exact hclass0
    · cases hsem

open Classical in
/-- Under `LoopSemStateFiniteExact.semantics s start = .terminate outcome events`, any clock `k`
at which `(LoopSemStateFiniteExact.evaluate (.call none (some start) [] none) { s with clock := k }).1 ≠ some .timeOut`
completes with `outcome` and `post.ffi.ioEvents = events`! -/
theorem loop_halt_of_not_timeOut {width : Nat} [NeZero width] {F : Type}
    (s : LoopSemStateFiniteExact width F) (start : Nat)
    (outcome : HolOutcome) (events : List HolIoEvent)
    (hsem : LoopSemStateFiniteExact.semantics s start = .terminate outcome events)
    (k : Nat) (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (post : LoopSemStateFiniteExact width F)
    (hrun : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none)
      { s with clock := k } = (res, post))
    (hnt : res ≠ some .timeOut) :
    (match res with
      | some (.finalFfi e) => outcome = .ffiOutcome e
      | some (.result _) => outcome = .success
      | _ => False) ∧
    post.ffi.ioEvents = events := by
  rw [loopSemIsWrapper] at hsem
  unfold crepToLoopSemanticsWrapper at hsem
  dsimp only at hsem
  split at hsem
  · cases hsem
  · rename_i hnoerr
    split at hsem
    · rename_i b hsome
      subst hsem
      obtain ⟨k0, out0, ev0, hk0, heq⟩ := holOptionSome_some hsome
      injection heq with hout0 hev0
      subst hout0 hev0
      simp only [Function.comp_apply, Prod.map] at hk0
      rcases hrun0 : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none)
        { s with clock := k0 } with ⟨res0, post0⟩
      rw [hrun0] at hk0
      simp only [Prod.mk.injEq] at hk0
      obtain ⟨hclass0, rfl⟩ := hk0
      have hnt0 : res0 ≠ some .timeOut := by
        intro h; subst h; cases hclass0
      obtain ⟨hr, hffi⟩ := loopEvaluateIgnoreClocks (.call none (some start) [] none)
        s k k0 res res0 post post0 hrun hnt hrun0 hnt0
      subst hr
      refine ⟨?_, congrArg HolFfiState.ioEvents hffi⟩
      rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;>
        simp at hclass0 ⊢ <;> exact hclass0.symm
    · cases hsem

mutual
/-- Exact structural count of `.cmp` nodes in a `CrepExpHOL` expression (and expression list).
Every `.cmp` node compiles via `progIfHOLExact` (`.ite`), whose exit `cutRes` consumes
at most 1 clock tick in `LoopSemStateFiniteExact.evaluate`; all other expression
constructors consume 0 clock ticks. -/
def crepExpCmpCount {width : Nat} [NeZero width] : CrepExpHOL width → Nat
  | .baseAddr | .topAddr | .const _ | .var _ | .loadGlob _ => 0
  | .load a | .load32 a | .loadByte a => crepExpCmpCount a
  | .op _ es | .crepOp _ es => crepExpsCmpCount es
  | .cmp _ e1 e2 => crepExpCmpCount e1 + crepExpCmpCount e2 + 1
  | .shift _ e1 e2 => crepExpCmpCount e1 + crepExpCmpCount e2
termination_by e => sizeOf e

/-- Exact structural count of `.cmp` nodes across a `List (CrepExpHOL width)`. -/
def crepExpsCmpCount {width : Nat} [NeZero width] : List (CrepExpHOL width) → Nat
  | [] => 0
  | e :: es => crepExpCmpCount e + crepExpsCmpCount es
termination_by es => sizeOf es
end

mutual
/-- `crepExpCmpCount e` is bounded by `sizeOf e`. -/
theorem crepExpCmpCount_le_sizeOf {width : Nat} [NeZero width] :
    ∀ e : CrepExpHOL width, crepExpCmpCount e ≤ sizeOf e
  | .baseAddr | .topAddr | .const _ | .var _ | .loadGlob _ => by simp [crepExpCmpCount]
  | .load a => by have := crepExpCmpCount_le_sizeOf a; simp [crepExpCmpCount]; omega
  | .load32 a => by have := crepExpCmpCount_le_sizeOf a; simp [crepExpCmpCount]; omega
  | .loadByte a => by have := crepExpCmpCount_le_sizeOf a; simp [crepExpCmpCount]; omega
  | .op _ es => by have := crepExpsCmpCount_le_sizeOf es; simp [crepExpCmpCount]; omega
  | .crepOp _ es => by have := crepExpsCmpCount_le_sizeOf es; simp [crepExpCmpCount]; omega
  | .cmp _ e1 e2 => by
      have h1 := crepExpCmpCount_le_sizeOf e1
      have h2 := crepExpCmpCount_le_sizeOf e2
      simp [crepExpCmpCount]; omega
  | .shift _ e1 e2 => by
      have h1 := crepExpCmpCount_le_sizeOf e1
      have h2 := crepExpCmpCount_le_sizeOf e2
      simp [crepExpCmpCount]; omega
termination_by e => sizeOf e

/-- `crepExpsCmpCount es` is bounded by `sizeOf es`. -/
theorem crepExpsCmpCount_le_sizeOf {width : Nat} [NeZero width] :
    ∀ es : List (CrepExpHOL width), crepExpsCmpCount es ≤ sizeOf es
  | [] => by simp [crepExpsCmpCount]
  | e :: es => by
      have h1 := crepExpCmpCount_le_sizeOf e
      have h2 := crepExpsCmpCount_le_sizeOf es
      simp [crepExpsCmpCount]; omega
termination_by es => sizeOf es
end

/-- Exact structural count of `.ite` nodes in a loop-free `HolLoopProg` (such as
any program produced by `compileExpHOLExact`). -/
def loopProgIteCount {width : Nat} [NeZero width] : HolLoopProg width → Nat
  | .seq c1 c2 => loopProgIteCount c1 + loopProgIteCount c2
  | .ite _ _ _ c1 c2 _ => loopProgIteCount c1 + loopProgIteCount c2 + 1
  | _ => 0

theorem loopProgIteCount_nestedSeq_append {width : Nat} [NeZero width] :
    ∀ (p q : List (HolLoopProg width)),
      loopProgIteCount (loopNestedSeqHOL (p ++ q)) =
        loopProgIteCount (loopNestedSeqHOL p) + loopProgIteCount (loopNestedSeqHOL q)
  | [], q => by simp [loopNestedSeqHOL, loopProgIteCount]
  | c :: p, q => by
      simp only [List.cons_append, loopNestedSeqHOL, loopProgIteCount,
        loopProgIteCount_nestedSeq_append p q]
      omega

theorem loopProgIteCount_zipWith_assign {width : Nat} [NeZero width] (m : Nat) :
    ∀ (is : List Nat) (vs : List (HolLoopExp width)),
      loopProgIteCount (loopNestedSeqHOL
        (List.zipWith (fun i v => HolLoopProg.assign (m + i) v) is vs)) = 0
  | [], _ => by simp [loopNestedSeqHOL, loopProgIteCount]
  | _ :: _, [] => by simp [loopNestedSeqHOL, loopProgIteCount]
  | _ :: is, _ :: vs => by
      simp [List.zipWith_cons_cons, loopNestedSeqHOL, loopProgIteCount,
        loopProgIteCount_zipWith_assign m is vs]

mutual
/-- The number of `.ite` nodes in the compiled `HolLoopProg` of `e`
equals `crepExpCmpCount e`. -/
theorem compileExpHOLExact_iteCount {width : Nat} [NeZero width]
    (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ e : CrepExpHOL width,
      loopProgIteCount (loopNestedSeqHOL (compileExpHOLExact ct tmp l e).1) =
        crepExpCmpCount e
  | .baseAddr | .topAddr | .const _ | .var _ | .loadGlob _ => by
      simp [compileExpHOLExact, loopNestedSeqHOL, loopProgIteCount, crepExpCmpCount]
  | .load a => by
      have ih := compileExpHOLExact_iteCount ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp [compileExpHOLExact, hA, crepExpCmpCount, ih]
  | .load32 a | .loadByte a => by
      have ih := compileExpHOLExact_iteCount ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih
      simp [compileExpHOLExact, hA, crepExpCmpCount, loopProgIteCount_nestedSeq_append,
        loopNestedSeqHOL, loopProgIteCount, ih]
  | .op o es => by
      have ih := compileExpsHOLExact_iteCount ct tmp l es
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp [compileExpHOLExact, hA, crepExpCmpCount, ih]
  | .crepOp o es => by
      have ih := compileExpsHOLExact_iteCount ct tmp l es
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih
      cases o
      simp only [compileExpHOLExact, hA, compileCrepopHOLExact, crepExpCmpCount]
      split <;>
        simp [loopProgIteCount_nestedSeq_append, loopProgIteCount_zipWith_assign,
          loopNestedSeqHOL, loopProgIteCount, ih]
  | .cmp o a b => by
      have iha := compileExpHOLExact_iteCount ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha
      have ihb := compileExpHOLExact_iteCount ct m ol b
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb
      simp [compileExpHOLExact, hA, hB, progIfHOLExact, crepExpCmpCount,
        loopProgIteCount_nestedSeq_append, loopNestedSeqHOL, loopProgIteCount, iha, ihb]
      omega
  | .shift o a b => by
      have iha := compileExpHOLExact_iteCount ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha
      have ihb := compileExpHOLExact_iteCount ct m ol b
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb
      simp [compileExpHOLExact, hA, hB, crepExpCmpCount,
        loopProgIteCount_nestedSeq_append, iha, ihb]
termination_by e => sizeOf e

/-- The number of `.ite` nodes in the compiled `HolLoopProg` of `es`
equals `crepExpsCmpCount es`. -/
theorem compileExpsHOLExact_iteCount {width : Nat} [NeZero width]
    (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ es : List (CrepExpHOL width),
      loopProgIteCount (loopNestedSeqHOL (compileExpsHOLExact ct tmp l es).1) =
        crepExpsCmpCount es
  | [] => by simp [compileExpsHOLExact, loopNestedSeqHOL, loopProgIteCount, crepExpsCmpCount]
  | e :: es => by
      have iha := compileExpHOLExact_iteCount ct tmp l e
      rcases hA : compileExpHOLExact ct tmp l e with ⟨c, v, m, ol⟩
      rw [hA] at iha
      have ihb := compileExpsHOLExact_iteCount ct m ol es
      rcases hB : compileExpsHOLExact ct m ol es with ⟨c', vs', m', ol'⟩
      rw [hB] at ihb
      simp [compileExpsHOLExact, hA, hB, crepExpsCmpCount,
        loopProgIteCount_nestedSeq_append, iha, ihb]
termination_by es => sizeOf es
end

/-- Exact structural predicate for loop-free `HolLoopProg` programs whose only
clock-consuming construct is `.ite` (via `cutRes`). -/
def loopProgExpOnly {width : Nat} [NeZero width] : HolLoopProg width → Bool
  | .skip | .assign _ _ | .arith _ | .load32 _ _ | .loadByte _ _
  | .store _ _ | .store32 _ _ | .storeByte _ _ | .setGlobal _ _ | .shMem _ _ _ => true
  | .seq c1 c2 => loopProgExpOnly c1 && loopProgExpOnly c2
  | .ite _ _ _ c1 c2 _ => loopProgExpOnly c1 && loopProgExpOnly c2
  | _ => false

theorem loopProgExpOnly_nestedSeq_append {width : Nat} [NeZero width] :
    ∀ (p q : List (HolLoopProg width)),
      loopProgExpOnly (loopNestedSeqHOL (p ++ q)) =
        (loopProgExpOnly (loopNestedSeqHOL p) && loopProgExpOnly (loopNestedSeqHOL q))
  | [], q => by simp [loopNestedSeqHOL, loopProgExpOnly]
  | c :: p, q => by
      simp only [List.cons_append, loopNestedSeqHOL, loopProgExpOnly,
        loopProgExpOnly_nestedSeq_append p q, Bool.and_assoc]

theorem loopProgExpOnly_zipWith_assign {width : Nat} [NeZero width] (m : Nat) :
    ∀ (is : List Nat) (vs : List (HolLoopExp width)),
      loopProgExpOnly (loopNestedSeqHOL
        (List.zipWith (fun i v => HolLoopProg.assign (m + i) v) is vs)) = true
  | [], _ => by simp [loopNestedSeqHOL, loopProgExpOnly]
  | _ :: _, [] => by simp [loopNestedSeqHOL, loopProgExpOnly]
  | _ :: is, _ :: vs => by
      simp [List.zipWith_cons_cons, loopNestedSeqHOL, loopProgExpOnly,
        loopProgExpOnly_zipWith_assign m is vs]

mutual
/-- Every compiled expression `compileExpHOLExact` produces a `loopProgExpOnly` program. -/
theorem compileExpHOLExact_expOnly {width : Nat} [NeZero width]
    (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ e : CrepExpHOL width,
      loopProgExpOnly (loopNestedSeqHOL (compileExpHOLExact ct tmp l e).1) = true
  | .baseAddr | .topAddr | .const _ | .var _ | .loadGlob _ => by
      simp [compileExpHOLExact, loopNestedSeqHOL, loopProgExpOnly]
  | .load a => by
      have ih := compileExpHOLExact_expOnly ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih; simp [compileExpHOLExact, hA, ih]
  | .load32 a | .loadByte a => by
      have ih := compileExpHOLExact_expOnly ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, o⟩
      rw [hA] at ih
      simp [compileExpHOLExact, hA, loopProgExpOnly_nestedSeq_append,
        loopNestedSeqHOL, loopProgExpOnly, ih]
  | .op o es => by
      have ih := compileExpsHOLExact_expOnly ct tmp l es
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih; simp [compileExpHOLExact, hA, ih]
  | .crepOp o es => by
      have ih := compileExpsHOLExact_expOnly ct tmp l es
      rcases hA : compileExpsHOLExact ct tmp l es with ⟨c, vs, m, ol⟩
      rw [hA] at ih
      cases o
      simp only [compileExpHOLExact, hA, compileCrepopHOLExact]
      split <;>
        simp [loopProgExpOnly_nestedSeq_append, loopProgExpOnly_zipWith_assign,
          loopNestedSeqHOL, loopProgExpOnly, ih]
  | .cmp o a b => by
      have iha := compileExpHOLExact_expOnly ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha
      have ihb := compileExpHOLExact_expOnly ct m ol b
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb
      simp [compileExpHOLExact, hA, hB, progIfHOLExact,
        loopProgExpOnly_nestedSeq_append, loopNestedSeqHOL, loopProgExpOnly, iha, ihb]
  | .shift o a b => by
      have iha := compileExpHOLExact_expOnly ct tmp l a
      rcases hA : compileExpHOLExact ct tmp l a with ⟨c, v, m, ol⟩
      rw [hA] at iha
      have ihb := compileExpHOLExact_expOnly ct m ol b
      rcases hB : compileExpHOLExact ct m ol b with ⟨c', v', m', ol'⟩
      rw [hB] at ihb
      simp [compileExpHOLExact, hA, hB,
        loopProgExpOnly_nestedSeq_append, iha, ihb]
termination_by e => sizeOf e

/-- Every compiled expression list `compileExpsHOLExact` produces a `loopProgExpOnly` program. -/
theorem compileExpsHOLExact_expOnly {width : Nat} [NeZero width]
    (ct : CrepToLoopContextExact) (tmp : Nat) (l : NumSet) :
    ∀ es : List (CrepExpHOL width),
      loopProgExpOnly (loopNestedSeqHOL (compileExpsHOLExact ct tmp l es).1) = true
  | [] => by simp [compileExpsHOLExact, loopNestedSeqHOL, loopProgExpOnly]
  | e :: es => by
      have iha := compileExpHOLExact_expOnly ct tmp l e
      rcases hA : compileExpHOLExact ct tmp l e with ⟨c, v, m, ol⟩
      rw [hA] at iha
      have ihb := compileExpsHOLExact_expOnly ct m ol es
      rcases hB : compileExpsHOLExact ct m ol es with ⟨c', vs', m', ol'⟩
      rw [hB] at ihb
      simp [compileExpsHOLExact, hA, hB,
        loopProgExpOnly_nestedSeq_append, iha, ihb]
termination_by es => sizeOf es
end

/-- `cutRes` decreases the clock by at most 1 tick. -/
theorem loop_cutRes_clock_bound {width : Nat} [NeZero width] {F : Type} (live : NumSet)
    (r : Option (LoopSemStateFiniteExact.LoopResultExact width) × LoopSemStateFiniteExact width F) :
    r.2.clock ≤ (LoopSemStateFiniteExact.cutRes live r).2.clock + 1 := by
  obtain ⟨res, s⟩ := r
  cases res with
  | some _ => simp [LoopSemStateFiniteExact.cutRes]
  | none =>
    simp only [LoopSemStateFiniteExact.cutRes]
    cases hc : LoopSemStateFiniteExact.cutState live s with
    | none => simp
    | some s1 =>
      simp only; have := LoopSemStateFiniteExact.cutState_clock hc
      split <;> simp [LoopSemStateFiniteExact.decClock] <;> omega

/-- Every `loopProgExpOnly` program consumes at most `loopProgIteCount p` clock ticks
(`s.clock ≤ (evaluate p s).2.clock + loopProgIteCount p`). -/
theorem loop_evaluate_clock_bound_of_expOnly {width : Nat} [NeZero width] {F : Type} :
    ∀ (p : HolLoopProg width) (s : LoopSemStateFiniteExact width F),
      loopProgExpOnly p = true →
      s.clock ≤ (LoopSemStateFiniteExact.evaluate p s).2.clock + loopProgIteCount p
  | .skip, s, _ => by simp [LoopSemStateFiniteExact.evaluate, loopProgIteCount]
  | .assign v exp, s, _ => by
      rw [LoopSemStateFiniteExact.evaluate]
      split <;> simp [LoopSemStateFiniteExact.setVar, loopProgIteCount]
  | .arith arith, s, _ => by
      rw [LoopSemStateFiniteExact.evaluate]
      cases ha : LoopSemStateFiniteExact.loopArith s arith with
      | none => simp [loopProgIteCount]
      | some s' =>
        have hc := LoopSemStateFiniteExact.loopArith_clock ha
        simp [loopProgIteCount, hc]
  | .load32 a v, s, _ => by
      rw [LoopSemStateFiniteExact.evaluate]
      repeat' split
      all_goals simp [LoopSemStateFiniteExact.setVar, loopProgIteCount]
  | .loadByte a v, s, _ => by
      rw [LoopSemStateFiniteExact.evaluate]
      repeat' split
      all_goals simp [LoopSemStateFiniteExact.setVar, loopProgIteCount]
  | .store exp v, s, _ => by
      rw [LoopSemStateFiniteExact.evaluate]
      repeat' split
      · have hc := LoopSemStateFiniteExact.memStore_clock ‹_›
        simp [loopProgIteCount, hc]
      all_goals simp [loopProgIteCount]
  | .store32 a w, s, _ => by
      rw [LoopSemStateFiniteExact.evaluate]
      repeat' split
      all_goals simp [loopProgIteCount]
  | .storeByte a w, s, _ => by
      rw [LoopSemStateFiniteExact.evaluate]
      repeat' split
      all_goals simp [loopProgIteCount]
  | .setGlobal dst exp, s, _ => by
      rw [LoopSemStateFiniteExact.evaluate]
      repeat' split
      all_goals simp [LoopSemStateFiniteExact.setGlobals, loopProgIteCount]
  | .shMem op v ad, s, _ => by
      rw [LoopSemStateFiniteExact.evaluate]
      repeat' split
      all_goals simp [LoopSemStateFiniteExact.shMemOp_clock, loopProgIteCount]
  | .seq c1 c2, s, hok => by
      rw [loopProgExpOnly, Bool.and_eq_true] at hok
      rw [LoopSemStateFiniteExact.evaluate_seq]
      have hb1 := loop_evaluate_clock_bound_of_expOnly c1 s hok.1
      rcases he1 : LoopSemStateFiniteExact.evaluate c1 s with ⟨r1, s1⟩
      rw [he1] at hb1
      cases r1 with
      | some _ => simp only [loopProgIteCount] at hb1 ⊢; omega
      | none =>
        have hb2 := loop_evaluate_clock_bound_of_expOnly c2 s1 hok.2
        simp only [loopProgIteCount] at hb1 hb2 ⊢
        omega
  | .ite cmp r1 ri c1 c2 live, s, hok => by
      rw [loopProgExpOnly, Bool.and_eq_true] at hok
      rw [LoopSemStateFiniteExact.evaluate]
      split
      · split
        · have hb1 := loop_evaluate_clock_bound_of_expOnly c1 s hok.1
          have hcr := loop_cutRes_clock_bound live (LoopSemStateFiniteExact.evaluate c1 s)
          simp only [loopProgIteCount]
          omega
        · have hb2 := loop_evaluate_clock_bound_of_expOnly c2 s hok.2
          have hcr := loop_cutRes_clock_bound live (LoopSemStateFiniteExact.evaluate c2 s)
          simp only [loopProgIteCount]
          omega
      · simp [loopProgIteCount]
  | .fail, _, hok | .primitive _ _ _, _, hok | .mark _, _, hok
  | .break _, _, hok | .continue _, _, hok | .loop _ _ _, _, hok
  | .raise _, _, hok | .return _, _, hok | .tick, _, hok
  | .locValue _ _, _, hok | .call _ _ _ _, _, hok
  | .ffi _ _ _ _ _ _, _, hok => by simp [loopProgExpOnly] at hok

/-- Quantitative bound on `crepToLoop_comp_exp_preserves_eval`: the clock witness
`ck` returned by `crepToLoop_comp_exp_preserves_eval` satisfies
`ck ≤ crepExpCmpCount e` (and hence `ck ≤ sizeOf e`), so running at any clock
`t.clock + B` with `crepExpCmpCount e ≤ B` succeeds and preserves all state/memory/globals/code/locals relations! -/
theorem crepToLoop_comp_exp_preserves_eval_clock_bound {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (e : CrepExpHOL width)
    (v : HolWordLab width) (t : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (le : HolLoopExp width) (ntmp : Nat) (nl : NumSet)
    (h : evalCrepSemHOLExp s e = some v ∧
      crepToLoopStateRelExact s t ∧
      crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
      crepToLoopCodeRelExact ctxt s.code t.code ∧
      crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
      compileExpHOLExact ctxt tmp l e = (p, le, ntmp, nl) ∧
      ctxt.vmax < tmp) :
    ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
      ck ≤ crepExpCmpCount e ∧
      LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
          { t with clock := t.clock + ck } = (none, st) ∧
      LoopSemStateFiniteExact.eval st le = some (wlabWlocExact v) ∧
      crepToLoopStateRelExact s st ∧
      crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
      crepToLoopCodeRelExact ctxt s.code st.code ∧
      crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  obtain ⟨ck, st, heval, hle, hsr, hmr, hgr, hcr, hlr⟩ :=
    crepToLoop_comp_exp_preserves_eval s e v t ctxt tmp l p le ntmp nl h
  have hexp : loopProgExpOnly (loopNestedSeqHOL p) = true := by
    have := compileExpHOLExact_expOnly ctxt tmp l e
    rw [h.2.2.2.2.2.2.1] at this
    exact this
  have hite : loopProgIteCount (loopNestedSeqHOL p) = crepExpCmpCount e := by
    have := compileExpHOLExact_iteCount ctxt tmp l e
    rw [h.2.2.2.2.2.2.1] at this
    exact this
  have hb := loop_evaluate_clock_bound_of_expOnly (loopNestedSeqHOL p)
    { t with clock := t.clock + ck } hexp
  have hclk : s.clock = t.clock ∧ s.clock = st.clock := ⟨h.2.1.2.2.1, hsr.2.2.1⟩
  have hck : ck ≤ crepExpCmpCount e := by
    rw [heval, hite] at hb
    simp only at hb
    omega
  exact ⟨ck, st, hck, heval, hle, hsr, hmr, hgr, hcr, hlr⟩

/-- Quantitative bound on `crepToLoop_comp_exps_preserves_eval`: the clock witness
`ck` satisfies `ck ≤ crepExpsCmpCount es` (and hence `ck ≤ sizeOf es`). -/
theorem crepToLoop_comp_exps_preserves_eval_clock_bound {width : Nat} [NeZero width] {σ : Type}
    (es : List (CrepExpHOL width)) (s : CrepSemHOLState width σ)
    (vs : List (HolWordLab width)) (t : LoopSemStateFiniteExact width σ)
    (ctxt : CrepToLoopContextExact) (tmp : Nat) (l : NumSet)
    (p : List (HolLoopProg width)) (les : List (HolLoopExp width)) (ntmp : Nat) (nl : NumSet)
    (h : es.mapM (evalCrepSemHOLExp s) = some vs ∧
      crepToLoopStateRelExact s t ∧
      crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals t.globals ∧
      crepToLoopCodeRelExact ctxt s.code t.code ∧
      crepToLoopLocalsRelExact ctxt l s.locals t.locals ∧
      compileExpsHOLExact ctxt tmp l es = (p, les, ntmp, nl) ∧
      ctxt.vmax < tmp) :
    ∃ (ck : Nat) (st : LoopSemStateFiniteExact width σ),
      ck ≤ crepExpsCmpCount es ∧
      LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL p)
          { t with clock := t.clock + ck } = (none, st) ∧
      les.mapM (LoopSemStateFiniteExact.eval st) = some (vs.map wlabWlocExact) ∧
      crepToLoopStateRelExact s st ∧
      crepToLoopMemRelHOLExact s.memory st.memory s.memaddrs ∧
      crepToLoopGlobalsRelHOLExact s.globals st.globals ∧
      crepToLoopCodeRelExact ctxt s.code st.code ∧
      crepToLoopLocalsRelExact ctxt nl s.locals st.locals := by
  obtain ⟨ck, st, heval, hles, hsr, hmr, hgr, hcr, hlr⟩ :=
    crepToLoop_comp_exps_preserves_eval es s vs t ctxt tmp l p les ntmp nl h
  have hexp : loopProgExpOnly (loopNestedSeqHOL p) = true := by
    have := compileExpsHOLExact_expOnly ctxt tmp l es
    rw [h.2.2.2.2.2.2.1] at this
    exact this
  have hite : loopProgIteCount (loopNestedSeqHOL p) = crepExpsCmpCount es := by
    have := compileExpsHOLExact_iteCount ctxt tmp l es
    rw [h.2.2.2.2.2.2.1] at this
    exact this
  have hb := loop_evaluate_clock_bound_of_expOnly (loopNestedSeqHOL p)
    { t with clock := t.clock + ck } hexp
  have hclk : s.clock = t.clock ∧ s.clock = st.clock := ⟨h.2.1.2.2.1, hsr.2.2.1⟩
  have hck : ck ≤ crepExpsCmpCount es := by
    rw [heval, hite] at hb
    simp only at hb
    omega
  exact ⟨ck, st, hck, heval, hles, hsr, hmr, hgr, hcr, hlr⟩


end InitE
