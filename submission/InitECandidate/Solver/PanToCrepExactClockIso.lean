import InitECandidate.Solver.SelfContainedStageBounds
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Assembly
import Flapjack.Pancake.Proofs.CrepInline.InlineProgCorrect


set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

/-!
# `InitECandidate.Solver.PanToCrepExactClockIso` — Wave 5 Atomic Worker `W5_12`

Self-contained exact clock isometry (`C_pc = 1, D_pc = 0`) for the `PanToCrep` and
`CrepInline` compiler passes inside `Solver/`, without importing any `Proofs/Bounded*`
module:

1. **Exact Clock Isometry Parameters (`C_pc = 1, D_pc = 0`)**:
   - Defines `C_pc := 1`, `D_pc := 0`, and `panToCrepClockBudget k := C_pc * k + D_pc = k`.
   - Proves exact identity, strict monotonicity, and affine budget laws (`pan_to_crep_budget_iso`).

2. **State Relation Exact Clock Equality (`panToCrepStateRelFiniteExact_clock_eq`)**:
   - In Flapjack, `panToCrepStateRelFiniteExact s t` imposes `s.clock = t.clock` directly,
     and is preserved under synchronized clock updates `{ s with clock := k }` and
     `{ t with clock := k }`.

3. **Constructor-Universal 1-for-1 Clock Isometry (`pan_to_crep_clock_iso`)**:
   - For every `ProgHOL width` constructor `v` and source state `s` with `localisedProgHOL v = true`
     and `res ≠ some .error`, `pcCompileCorrect` produces a target `CrepSem` run at the
     exact same initial clock (`t.clock = panToCrepClockBudget s.clock = s.clock`) whose
     post-state clock equals the source post-state clock (`t1.clock = s1.clock`) and whose
     consumed clock delta is identical (`t.clock - t1.clock = s.clock - s1.clock`).

4. **Non-Expiration (`pan_to_crep_not_timeOut`) & Non-FinalFFI Preservation**:
   - Proves that `res1 = some .timeOut ↔ res = some .timeOut` and
     `res1 = some (.finalFfi f) ↔ res = some (.finalFfi f)`, so any non-`timeOut` source
     execution is guaranteed not to `timeOut` in `CrepSem` at the identical clock budget `k`.

5. **Whole-Pass Entry Call & `CrepInline` Clock Isometry (`pan_to_crep_full_entry_clock_iso`)**:
   - Combines `compileToCrepExactHOLW` (`pan_to_crep_clocked_agree`) and `CrepInline`
     (`crep_inline_clocked_agree` / `inlineProgCorrectExact`) to show 1-for-1 clock isometry
     across the entire `PanToCrep` pass (`compileProgDeclsHOLW`).

6. **Composition with `CrepToLoop` (`pan_to_crep_to_loop_clock_comp` & `pan_to_crep_to_loop_entry_sim`)**:
   - Composes `pan_to_crep_clock_iso` with `crepToLoop_ncompile_correct` (and at the entry
     call level with `crep_to_loop_clocked_sim`) so that `PanSem -> CrepSem -> LoopSem`
     consumes `panToCrepClockBudget k + ck = k + ck` ticks with `0` overhead from `PanToCrep`.
-/

namespace InitECandidate.Solver.PanToCrepExactClockIso

open Classical
open InitE
open InitECandidate.Solver.SelfContainedStageBounds
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect
open Flapjack.PanToCrepStateRelImpSemanticsTop

/-- Multiplicative clock factor for `PanToCrep` (`1`). -/
def C_pc : Nat := 1

/-- Additive clock offset for `PanToCrep` (`0`). -/
def D_pc : Nat := 0

/-- Exact affine clock budget for `PanToCrep`: `C_pc * k + D_pc = k`. -/
def panToCrepClockBudget (k : Nat) : Nat :=
  C_pc * k + D_pc

/-- 1. Exact algebraic clock isometry of `panToCrepClockBudget` (`C_pc = 1, D_pc = 0`):
the affine budget `C_pc * k + D_pc` is strictly isometric to `k` on all `Nat` inputs. -/
theorem pan_to_crep_budget_iso (k1 k2 : Nat) :
    C_pc = 1 ∧
      D_pc = 0 ∧
      panToCrepClockBudget k1 = k1 ∧
      panToCrepClockBudget (k1 + k2) = panToCrepClockBudget k1 + panToCrepClockBudget k2 ∧
      (panToCrepClockBudget k1 ≤ panToCrepClockBudget k2 ↔ k1 ≤ k2) ∧
      (panToCrepClockBudget k1 < panToCrepClockBudget k2 ↔ k1 < k2) := by
  unfold panToCrepClockBudget C_pc D_pc
  omega

/-- 2. Exact clock projection and synchronized clock update for `panToCrepStateRelFiniteExact`:
`panToCrepStateRelFiniteExact s t` forces `s.clock = t.clock`, `t.clock = panToCrepClockBudget s.clock`,
and is invariant under setting both clocks to any `k`. -/
theorem panToCrepStateRelFiniteExact_clock_eq {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ) (k : Nat)
    (hsr : panToCrepStateRelFiniteExact s t) :
    s.clock = t.clock ∧
      t.clock = panToCrepClockBudget s.clock ∧
      s.ffi = t.ffi ∧
      panToCrepStateRelFiniteExact { s with clock := k } { t with clock := k } := by
  rcases hsr with ⟨h1, h2, h3, h4, h5, hclk, h7, hffi, h9, h10⟩
  refine ⟨hclk, ?_, hffi, ⟨h1, h2, h3, h4, h5, rfl, h7, hffi, h9, h10⟩⟩
  unfold panToCrepClockBudget C_pc D_pc
  omega

/-- 3. Exact bijective classification of `timeOut` and `finalFfi` across `pcCompileCorrectResultRel`:
a compiled `CrepSem` execution times out iff the source `PanSem` execution times out, and produces
`finalFfi` iff the source produces `finalFfi`. -/
theorem pcCompileCorrectResultRel_not_timeOut_iff {width : Nat} [NeZero width] {σ : Type}
    (ctxt : PanToCrepContextExact width)
    (s1 : PanSemStateFiniteExact width σ) (t1 : CrepSemHOLState width σ)
    (res : Option (PanSemResultExact width)) (res1 : Option (CrepResultHOLExact width))
    (hrel : pcCompileCorrectResultRel ctxt s1 t1 res res1) :
    res1 ≠ some .error ∧
      (res1 = some .timeOut ↔ res = some .timeOut) ∧
      (res1 ≠ some .timeOut ↔ res ≠ some .timeOut) ∧
      (∀ f, res1 = some (.finalFfi f) ↔ res = some (.finalFfi f)) := by
  rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;>
    simp only [pcCompileCorrectResultRel] at hrel <;>
    (try split at hrel) <;>
    simp_all

/-- 4. Constructor-universal 1-for-1 clock isometry (`C_pc = 1, D_pc = 0`) for `PanToCrep`
(`compileProgExactHOLW`) on all `ProgHOL width` programs:
whenever `s.evaluateHOLFiniteState prog = (res, s1)` with `res ≠ some .error` and
`localisedProgHOL prog = true`, `compileProgExactHOLW ctxt prog` executes from `t`
at the identical initial clock `t.clock = panToCrepClockBudget s.clock = s.clock` to
`(res1, t1)` with exact post-clock equality `t1.clock = s1.clock` and identical clock
consumption `t.clock - t1.clock = s.clock - s1.clock`. -/
theorem pan_to_crep_clock_iso {width : Nat} [NeZero width] {σ : Type}
    (prog : ProgHOL width) (s s1 : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width))
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width)
    (hev : s.evaluateHOLFiniteState prog = (res, s1))
    (hne : res ≠ some .error)
    (hsr : panToCrepStateRelFiniteExact s t)
    (hcode : codeRelExactHOLW ctxt s.code t.code)
    (hexcp : panToCrepExcpRelFiniteExact ctxt.eids s.eshapes)
    (hlocals : panToCrepLocalsRelFiniteExact ctxt s.locals t.locals)
    (hloc : localisedProgHOL prog = true) :
    ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact { t with clock := panToCrepClockBudget s.clock }
          (compileProgExactHOLW ctxt prog) = (res1, t1) ∧
        t.clock = panToCrepClockBudget s.clock ∧
        t1.clock = panToCrepClockBudget s1.clock ∧
        t1.clock = s1.clock ∧
        t.clock - t1.clock = s.clock - s1.clock ∧
        t1.ffi = s1.ffi ∧
        panToCrepStateRelFiniteExact s1 t1 ∧
        codeRelExactHOLW ctxt s1.code t1.code ∧
        panToCrepExcpRelFiniteExact ctxt.eids s1.eshapes ∧
        pcCompileCorrectResultRel ctxt s1 t1 res res1 := by
  obtain ⟨res1, t1, hrun, hsr1, hcode1, hexcp1, hres⟩ :=
    pcCompileCorrect prog s res s1 t ctxt ⟨hev, hne, hsr, hcode, hexcp, hlocals, hloc⟩
  have hclk0 : t.clock = panToCrepClockBudget s.clock :=
    (panToCrepStateRelFiniteExact_clock_eq s t s.clock hsr).2.1
  have hclk1 : t1.clock = s1.clock := hsr1.2.2.2.2.2.1.symm
  have hclk1_b : t1.clock = panToCrepClockBudget s1.clock := by
    rw [hclk1]; exact (pan_to_crep_budget_iso s1.clock 0).2.2.1.symm
  have ht_eq : ({ t with clock := panToCrepClockBudget s.clock } : CrepSemHOLState width σ) = t := by
    rw [← hclk0]
  rw [ht_eq]
  have hres_rel : pcCompileCorrectResultRel ctxt s1 t1 res res1 := by
    rcases res with _ | (_ | _ | _ | _ | _ | ⟨eid, v'⟩ | _)
    · exact hres
    · exact hres
    · exact hres
    · exact hres
    · exact hres
    · exact hres
    · dsimp [pcCompileCorrectResultRel] at hres ⊢
      cases hlk : ctxt.eids.lookup eid <;> rw [hlk] at hres <;> exact hres
    · exact hres
  refine ⟨res1, t1, hrun, hclk0, hclk1_b, hclk1, ?_, hsr1.2.2.2.2.2.2.2.1.symm,
    hsr1, hcode1, hexcp1, hres_rel⟩
  rw [hsr.2.2.2.2.2.1, hclk1]

/-- 5. Non-expiration theorem (`pan_to_crep_not_timeOut`):
for any source program `prog` that neither errors nor times out at clock `k`
(and optionally does not trigger `finalFfi`), the compiled `CrepSem` program at the
exact same clock `panToCrepClockBudget k = k` neither errors nor times out, preserves
post-clock equality `t1.clock = s1.clock`, and preserves non-`finalFfi` termination. -/
theorem pan_to_crep_not_timeOut {width : Nat} [NeZero width] {σ : Type}
    (prog : ProgHOL width) (s s1 : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width))
    (t : CrepSemHOLState width σ) (ctxt : PanToCrepContextExact width) (k : Nat)
    (hev : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k } prog = (res, s1))
    (hne : res ≠ some .error)
    (hnt : res ≠ some .timeOut)
    (hsr : panToCrepStateRelFiniteExact s t)
    (hcode : codeRelExactHOLW ctxt s.code t.code)
    (hexcp : panToCrepExcpRelFiniteExact ctxt.eids s.eshapes)
    (hlocals : panToCrepLocalsRelFiniteExact ctxt s.locals t.locals)
    (hloc : localisedProgHOL prog = true) :
    ∃ (res1 : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ),
      evalCrepSemHOLProgExact { t with clock := panToCrepClockBudget k }
          (compileProgExactHOLW ctxt prog) = (res1, t1) ∧
        res1 ≠ some .error ∧
        res1 ≠ some .timeOut ∧
        ((∀ f, res ≠ some (.finalFfi f)) → ∀ f, res1 ≠ some (.finalFfi f)) ∧
        t1.clock = s1.clock ∧
        t1.ffi = s1.ffi ∧
        panToCrepStateRelFiniteExact s1 t1 ∧
        pcCompileCorrectResultRel ctxt s1 t1 res res1 := by
  have hsr_k : panToCrepStateRelFiniteExact { s with clock := k } { t with clock := k } :=
    (panToCrepStateRelFiniteExact_clock_eq s t k hsr).2.2.2
  obtain ⟨res1, t1, hrun, _, _, hclk1, _, hffi1, hsr1, _, _, hres⟩ :=
    pan_to_crep_clock_iso prog { s with clock := k } s1 res { t with clock := k } ctxt
      hev hne hsr_k hcode hexcp hlocals hloc
  have hiff := pcCompileCorrectResultRel_not_timeOut_iff ctxt s1 t1 res res1 hres
  have htk : ({ { t with clock := k } with clock := panToCrepClockBudget ({ s with clock := k } : PanSemStateFiniteExact width σ).clock } :
      CrepSemHOLState width σ) = { t with clock := panToCrepClockBudget k } := by
    cases t; rfl
  rw [htk] at hrun
  refine ⟨res1, t1, hrun, hiff.1, hiff.2.2.1.mpr hnt, ?_, hclk1, hffi1, hsr1, hres⟩
  intro hnffi f hf
  exact hnffi f ((hiff.2.2.2 f).mp hf)

/-- 6. Whole-pass `PanToCrep` (`compileToCrepExactHOLW` + `CrepInline`) entry-call clock isometry
and non-`timeOut` preservation (`C_pc = 1, D_pc = 0`):
at any clock `k`, the full `PanToCrep` pass (`compileProgDeclsHOLW pan_code`) runs at
`{ t with clock := panToCrepClockBudget k }` (`= { t with clock := k }`) with the exact same
result classification, FFI state, and non-`timeOut` behavior as the source `PanSem` entry call. -/
theorem pan_to_crep_full_entry_clock_iso {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
    (pan_code : List (DeclHOL width)) (start : MlS) (k : Nat)
    (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (hsr : panToCrepStateRelFiniteExact s t)
    (hdist : ((functionsHOL pan_code).map Prod.fst).Nodup)
    (hscode : s.code = HolFiniteMapExact.empty.updateList (functionsHOL pan_code).reverse)
    (htcode : t.code = alistToFmapCodeExact (compileProgDeclsHOLW pan_code))
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hlocal : ∀ entry ∈ functionsHOL pan_code, localisedProgHOL entry.2.2.1 = true)
    (hsize : sizeOfEidsHOL pan_code < 2 ^ width)
    (hdom : ∀ key, (s.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL pan_code).lookup key).isSome)
    (hev : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none start [] : ProgHOL width) = (res, s1))
    (hne : res ≠ some .error) :
    ∃ res_crep t_crep,
      evalCrepSemHOLProgExact { t with clock := panToCrepClockBudget k }
        (.call none start [] : CrepProgHOL width) = (res_crep, t_crep) ∧
      res_crep ≠ some .error ∧
      (res ≠ some .timeOut → res_crep ≠ some .timeOut) ∧
      t_crep.ffi = s1.ffi ∧
      (match res_crep with
       | some .timeOut => .Incomplete
       | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
       | some (.return _) => .CompleteResult HolOutcome.success
       | _ => .RunError) = panEntryClass res := by
  let t_pre : CrepSemHOLState width σ :=
    { t with code := HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse }
  have hsr_pre : panToCrepStateRelFiniteExact s t_pre := hsr
  obtain ⟨res1, t1, hrun1, hne1, hffi1, hclass1⟩ :=
    pan_to_crep_clocked_agree s t_pre pan_code start k res s1
      hsr_pre hdist hscode rfl hloc hlocal hsize hdom hev hne
  have hne1' : (evalCrepSemHOLProgExact { t_pre with clock := k }
      (.call none start [])).1 ≠ some .error := by
    rw [hrun1]; exact hne1
  have hinl := crep_inline_clocked_agree t_pre t
    (compileToCrepExactHOLW pan_code) start
    ((functionsHOL (pan_code.filter inlinableHOL)).map Prod.fst) k
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
    (firstCompileToCrepAllDistinctExact pan_code hdist) rfl
    (by simpa [compileProgDeclsHOLW] using htcode)
    hne1'
  rcases hrun_t : evalCrepSemHOLProgExact { t with clock := k }
      (.call none start [] : CrepProgHOL width) with ⟨res_crep, t_crep⟩
  have hres_eq : res_crep = res1 := by
    have h1 := hinl.1
    rw [hrun_t, hrun1] at h1
    exact h1
  have hffi_eq : t_crep.ffi = t1.ffi := by
    have h2 := hinl.2
    rw [hrun_t, hrun1] at h2
    exact h2
  have hbud : panToCrepClockBudget k = k := (pan_to_crep_budget_iso k 0).2.2.1
  rw [← hbud] at hrun_t
  subst res_crep
  refine ⟨res1, t_crep, hrun_t, hne1, ?_, hffi_eq.trans hffi1, hclass1⟩
  intro hnt ht
  subst ht
  rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;>
    simp [panEntryClass] at hclass1 hnt

/-- 7. Statement-level composition of `PanToCrep` (`C_pc = 1, D_pc = 0`) with `CrepToLoop`
(`crepToLoop_ncompile_correct`):
for any `ProgHOL width` program `prog` whose compiled `CrepProgHOL` is further compiled by
`CrepToLoop.compileHOLExact ctxt_loop l`, the two-stage `PanSem -> CrepSem -> LoopSem`
simulation runs at clock `panToCrepClockBudget s.clock + ck = s.clock + ck` (zero extra ticks
from `PanToCrep`) and preserves all state/memory/globals/code/locals invariants. -/
theorem pan_to_crep_to_loop_clock_comp {width : Nat} [NeZero width] {σ : Type}
    (prog : ProgHOL width) (s s1 : PanSemStateFiniteExact width σ)
    (res : Option (PanSemResultExact width))
    (t : CrepSemHOLState width σ) (ctxt_pc : PanToCrepContextExact width)
    (u : LoopSemStateFiniteExact width σ) (ctxt_loop : CrepToLoopContextExact) (l : NumSet)
    (hev : s.evaluateHOLFiniteState prog = (res, s1))
    (hne : res ≠ some .error)
    (hsr_pc : panToCrepStateRelFiniteExact s t)
    (hcode_pc : codeRelExactHOLW ctxt_pc s.code t.code)
    (hexcp_pc : panToCrepExcpRelFiniteExact ctxt_pc.eids s.eshapes)
    (hlocals_pc : panToCrepLocalsRelFiniteExact ctxt_pc s.locals t.locals)
    (hloc_pc : localisedProgHOL prog = true)
    (hsr_cl : crepToLoopStateRelExact t u)
    (hmem_cl : crepToLoopMemRelHOLExact t.memory u.memory t.memaddrs)
    (hglob_cl : crepToLoopGlobalsRelHOLExact t.globals u.globals)
    (hcode_cl : crepToLoopCodeRelExact ctxt_loop t.code u.code)
    (hlocals_cl : crepToLoopLocalsRelExact ctxt_loop l t.locals u.locals) :
    ∃ (res_crep : Option (CrepResultHOLExact width)) (t1 : CrepSemHOLState width σ)
      (ck : Nat) (res_loop : Option (LoopSemStateFiniteExact.LoopResultExact width))
      (u1 : LoopSemStateFiniteExact width σ),
      evalCrepSemHOLProgExact { t with clock := panToCrepClockBudget s.clock }
          (compileProgExactHOLW ctxt_pc prog) = (res_crep, t1) ∧
        LoopSemStateFiniteExact.evaluate
          (compileHOLExact ctxt_loop l (compileProgExactHOLW ctxt_pc prog))
          { u with clock := panToCrepClockBudget s.clock + ck } = (res_loop, u1) ∧
        t1.clock = s1.clock ∧
        u1.clock = s1.clock ∧
        u1.ffi = s1.ffi ∧
        panToCrepStateRelFiniteExact s1 t1 ∧
        crepToLoopStateRelExact t1 u1 ∧
        pcCompileCorrectResultRel ctxt_pc s1 t1 res res_crep ∧
        res_loop = resultToLoop res_crep ∧
        (res ≠ some .timeOut → res_loop ≠ some .timeOut) := by
  obtain ⟨res_crep, t1, hrun_pc, hclk0_pc, _, hclk1_pc, _, hffi_pc, hsr1_pc, _, _, hres_pc⟩ :=
    pan_to_crep_clock_iso prog s s1 res t ctxt_pc
      hev hne hsr_pc hcode_pc hexcp_pc hlocals_pc hloc_pc
  have hiff := pcCompileCorrectResultRel_not_timeOut_iff ctxt_pc s1 t1 res res_crep hres_pc
  have ht_eq : ({ t with clock := panToCrepClockBudget s.clock } : CrepSemHOLState width σ) = t := by
    rw [← hclk0_pc]
  have hrun_pc' : evalCrepSemHOLProgExact t (compileProgExactHOLW ctxt_pc prog) = (res_crep, t1) := by
    rwa [ht_eq] at hrun_pc
  obtain ⟨ck, res_loop, u1, hrun_cl, hsr1_cl, _, _, _, hres_cl, _⟩ :=
    crepToLoop_ncompile_correct (compileProgExactHOLW ctxt_pc prog) t res_crep t1 u ctxt_loop l
      ⟨hrun_pc', hiff.1, hsr_cl, hmem_cl, hglob_cl, hcode_cl, hlocals_cl⟩
  have hu_clk : u.clock = panToCrepClockBudget s.clock := by
    rw [← hsr_cl.2.2.1, hclk0_pc]
  rw [hu_clk] at hrun_cl
  have hu1_clk : u1.clock = s1.clock := by
    rw [← hsr1_cl.2.2.1, hclk1_pc]
  have hu1_ffi : u1.ffi = s1.ffi := by
    rw [← hsr1_cl.2.2.2.2.1, hffi_pc]
  refine ⟨res_crep, t1, ck, res_loop, u1, hrun_pc, hrun_cl, hclk1_pc, hu1_clk, hu1_ffi,
    hsr1_pc, hsr1_cl, hres_pc, hres_cl, ?_⟩
  intro hnt hloop_to
  have hcrep_nt : res_crep ≠ some .timeOut := hiff.2.2.1.mpr hnt
  rw [hres_cl] at hloop_to
  rcases res_crep with _ | (_ | _ | _ | _ | _ | _) <;>
    simp [resultToLoop] at hloop_to hcrep_nt

/-- 8. Whole-program entry-call composition of `PanToCrep` (`C_pc = 1, D_pc = 0`) + `CrepInline`
+ `CrepToLoop` (`pan_to_crep_to_loop_entry_sim`):
given a source `PanSem` entry call `.call none start []` at clock `k`, the composed
`PanToCrep -> CrepInline -> CrepToLoop` pass produces a `LoopSem` entry call at clock
`panToCrepClockBudget k + k' = k + k'` with matching FFI state and non-`timeOut` preservation. -/
theorem pan_to_crep_to_loop_entry_sim {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
    (u : LoopSemStateFiniteExact width σ)
    (pan_code : List (DeclHOL width)) (start : MlS) (lc : Nat) (arch : AsmArchitecture)
    (prog_crep : CrepProgHOL width) (k : Nat)
    (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (hsr : panToCrepStateRelFiniteExact s t)
    (hdist : ((functionsHOL pan_code).map Prod.fst).Nodup)
    (hscode : s.code = HolFiniteMapExact.empty.updateList (functionsHOL pan_code).reverse)
    (htcode : t.code = alistToFmapCodeExact (compileProgDeclsHOLW pan_code))
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hlocal : ∀ entry ∈ functionsHOL pan_code, localisedProgHOL entry.2.2.1 = true)
    (hsize : sizeOfEidsHOL pan_code < 2 ^ width)
    (hdom : ∀ key, (s.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL pan_code).lookup key).isSome)
    (hmd : t.memaddrs = (fun address => u.mdomain address = true))
    (hbe : t.be = u.be)
    (hsh : t.shMemaddrs = (fun address => u.shMdomain address = true))
    (hffi : t.ffi = u.ffi)
    (hbase : t.baseAddr = u.baseAddr)
    (htop : t.topAddr = u.topAddr)
    (hmem : crepToLoopMemRelHOLExact t.memory u.memory t.memaddrs)
    (hglob : crepToLoopGlobalsRelHOLExact t.globals u.globals)
    (hucode : u.code = sptFromAList (compileProgHOLExact arch (compileProgDeclsHOLW pan_code)))
    (huloc : t.locals = HolFiniteMapExact.empty)
    (hmf : (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW pan_code)).lookup start = some (lc, 0))
    (hprog : holAlookup (compileProgDeclsHOLW pan_code) start = some ([], prog_crep))
    (hev : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none start [] : ProgHOL width) = (res, s1))
    (hne : res ≠ some .error) :
    ∃ res_crep k' u1,
      LoopSemStateFiniteExact.evaluate
        (.call none (some lc) [] none : HolLoopProg width)
        { u with clock := panToCrepClockBudget k + k' } =
        (resultToLoop res_crep, u1) ∧
      u1.ffi = s1.ffi ∧
      (res ≠ some .timeOut → resultToLoop res_crep ≠ some .timeOut) ∧
      (match res_crep with
       | some .timeOut => .Incomplete
       | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
       | some (.return _) => .CompleteResult HolOutcome.success
       | _ => .RunError) = panEntryClass res := by
  obtain ⟨res_crep, t_crep, hrun_crep, hne_crep, hnt_crep, hffi_crep, hclass_crep⟩ :=
    pan_to_crep_full_entry_clock_iso s t pan_code start k res s1
      hsr hdist hscode htcode hloc hlocal hsize hdom hev hne
  have hdist_crep : ((compileProgDeclsHOLW pan_code).map Prod.fst).Nodup :=
    panToCrepFirstCompileProgAllDistinctExact pan_code hdist
  obtain ⟨k', u1, hrun_loop, hffi_loop⟩ :=
    crep_to_loop_clocked_sim t u (compileProgDeclsHOLW pan_code) start lc arch prog_crep
      (panToCrepClockBudget k) res_crep t_crep
      hmd hbe hsh hffi hbase htop hmem hglob hdist_crep htcode hucode huloc hmf hprog
      hrun_crep hne_crep
  refine ⟨res_crep, k', u1, hrun_loop, hffi_loop.symm.trans hffi_crep, ?_, hclass_crep⟩
  intro hnt hloop_to
  have hcrep_nt := hnt_crep hnt
  rcases res_crep with _ | (_ | _ | _ | _ | _ | _) <;>
    simp [resultToLoop] at hloop_to hcrep_nt


end InitECandidate.Solver.PanToCrepExactClockIso
