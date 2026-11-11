import InitECandidate.Solver.GuestBound.LocalsFrame
import InitECandidate.Solver.GuestBound.Manual.Taylor
import InitECandidate.Solver.GuestBound.AndGuard

/-!
# `sort_elems`: the merge loop

`while (i < mid) && (j < right) { …; i or j += 1; k += 1 }`: while the guard
holds, `i` and `j` are below `mid` and `right` in the signed order, so the
increment cannot overflow and `(mid - i) + (right - j)` decreases.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Position of a word in the signed order. -/
def bias (w : Word) : Nat := (w.toNat + 2 ^ 63) % 2 ^ 64

theorem bias_lt (w : Word) : bias w < 2 ^ 64 := Nat.mod_lt _ (by decide)

theorem signedLess_iff (a b : Word) : RiscV.signedLess a b = true ↔ bias a < bias b := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [RiscV.signedLess, bias]
  have h63 : (2 : Nat) ^ (64 - 1) = 2 ^ 63 := by decide
  rw [h63]
  split <;> split <;> simp <;> omega

theorem bias_succ {w : Word} (h : bias w + 1 < 2 ^ 64) : bias (w + 1) = bias w + 1 := by
  have hw := w.isLt
  have hsum : (w + 1).toNat = (w.toNat + 1) % 2 ^ 64 := by simp [BitVec.toNat_add]
  unfold bias at h ⊢
  rw [hsum]
  omega

/-- A call without a destination ends the run, or leaves the locals alone. -/
theorem call_nodest_frame {f : FunName} {s : St σ} {arguments : List (Exp Word)}
    {r : Result σ} :
    Runs E s (.call (some (none, none)) f arguments) r →
    match r with
    | .normal l _ _ _ => l = s.locals
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  intro h
  rcases runs_call_inv (some none) h with herr | ⟨parameters, body, values, calleeLocals, rb,
    -, -, -, -, hout⟩
  · cases r <;> first | trivial | cases herr
  · cases rb with
    | returned l g m ffi values' =>
      simp only [CallOutcome] at hout
      rcases hout with herr | ⟨l', g', hassign, rfl⟩
      · cases r <;> first | trivial | cases herr
      · obtain ⟨-, hframe, -⟩ := assignResult_frame (structs := E.structs) (M := [])
          (by simp [destIn]) hassign
        funext x
        exact hframe x (by simp)
    | raised l g m ffi exception value =>
      simp only [CallOutcome] at hout
      subst hout
      trivial
    | finalFfi l g m ffi event =>
      simp only [CallOutcome] at hout
      subst hout
      trivial
    | _ =>
      simp only [CallOutcome] at hout
      cases r <;> first | trivial | cases hout

/-- `f(…); x = x + 1`: increments `x` and changes nothing else among the locals. -/
theorem incr_after_call (hE : GuestEnv E) {f : FunName} {arguments : List (Exp Word)}
    {x : VarName} {xv : Word} {s : St σ} {r : Result σ} (hx : s.locals x = some (.word xv)) :
    Runs E s (.seq (.call (some (none, none)) f arguments)
      (.assign .local x (.op .add [.var .local x, .const (BitVec.ofNat 64 1)]))) r →
    match r with
    | .normal l _ _ _ => l x = some (.word (xv + 1)) ∧ ∀ y, y ≠ x → l y = s.locals y
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  intro h
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp h
  have f1 := call_nodest_frame h₁
  cases r₁ with
  | normal l1 g1 m1 ff1 =>
    simp only at f1 hrest
    subst f1
    rw [runs_assign_local] at hrest
    simp only [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_local, eval_const, hx,
      wordsProj_cons, wordsProj_nil, wordOp, List.foldr, Option.map_some] at hrest
    split at hrest
    · subst hrest
      refine ⟨by simp [update_lookup], ?_⟩
      intro y hy
      have : (y == x) = false := by simpa using hy
      simp [update_lookup, this]
    · subst hrest
      simp [St.err]
  | continued l1 g1 m1 ff1 => exact f1.elim
  | broke l1 g1 m1 ff1 => exact f1.elim
  | _ =>
    simp only at hrest
    subst hrest
    trivial

/-- The body of the merge loop; the address expressions do not matter. -/
def mergeBody (ea eb : Exp Word) (argsA argsB : List (Exp Word)) : Prog Word :=
  .dec "a" .one ea
    (.dec "b" .one eb
      (.decCall "gt" .one "bal_sort_gt" [.var .local "a", .var .local "b", .var .local "kind"]
        (.seq
          (.ite (.cmp .equal (.var .local "gt") (.const (BitVec.ofNat 64 0)))
            (.seq (.call (some (none, none)) "memcpy" argsA)
              (.assign .local "i" (.op .add [.var .local "i", .const (BitVec.ofNat 64 1)])))
            (.seq (.call (some (none, none)) "memcpy" argsB)
              (.assign .local "j" (.op .add [.var .local "j", .const (BitVec.ofNat 64 1)]))))
          (.assign .local "k" (.op .add [.var .local "k", .const (BitVec.ofNat 64 1)])))))

/-- What one merge step does to the locals the guard reads. -/
def MergePost (iv jv : Word) (s : St σ) : Result σ → Prop
  | .normal l _ _ _ =>
      l "mid" = s.locals "mid" ∧ l "right" = s.locals "right" ∧
        ((l "i" = some (.word (iv + 1)) ∧ l "j" = some (.word jv)) ∨
          (l "i" = some (.word iv) ∧ l "j" = some (.word (jv + 1))))
  | .continued _ _ _ _ | .broke _ _ _ _ => False
  | _ => True

/-- After one branch of the merge step: `k = k + 1` and the restores keep the facts. -/
theorem merge_finish (hE : GuestEnv E) {iv jv iv' jv' : Word} {s : St σ}
    {va vb : PanValue Word} {l1 g1 : VarName → Option (PanValue Word)}
    {m1 : Word → Option (PanValue Word)} {f1 : FfiState σ} {r4 : Result σ}
    (hmid : l1 "mid" = s.locals "mid") (hright : l1 "right" = s.locals "right")
    (hi1 : l1 "i" = some (.word iv')) (hj1 : l1 "j" = some (.word jv'))
    (hcase : (iv' = iv + 1 ∧ jv' = jv) ∨ (iv' = iv ∧ jv' = jv + 1))
    (h : Runs E ⟨l1, g1, m1, f1⟩
      (.assign .local "k" (.op .add [.var .local "k", .const (BitVec.ofNat 64 1)])) r4) :
    MergePost iv jv s
      (restorePanValueFfiLocal "a" (s.locals "a")
        (restorePanValueFfiLocal "b" (updatePanValueMap s.locals "a" va "b")
          (restorePanValueFfiLocal "gt"
            (updatePanValueMap (updatePanValueMap s.locals "a" va) "b" vb "gt") r4))) := by
  rw [runs_assign_local] at h
  split at h
  · split at h
    · subst h
      simp only [restorePanValueFfiLocal, MergePost]
      refine ⟨?_, ?_, ?_⟩
      · simp (config := { decide := true }) only [restorePanValueLocal, update_lookup, if_false]
        exact hmid
      · simp (config := { decide := true }) only [restorePanValueLocal, update_lookup, if_false]
        exact hright
      · simp (config := { decide := true }) only [restorePanValueLocal, update_lookup, if_false]
        rw [hi1, hj1]
        rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
    · subst h
      simp only [St.err, restorePanValueFfiLocal, MergePost]
  · subst h
    simp only [St.err, restorePanValueFfiLocal, MergePost]

set_option maxHeartbeats 2000000 in
/-- One merge step increments exactly one of `i`, `j` and keeps `mid`, `right`. -/
theorem mergeBody_runs (hE : GuestEnv E) {ea eb : Exp Word} {argsA argsB : List (Exp Word)}
    {iv jv : Word} {s : St σ} {r : Result σ} (hi : s.locals "i" = some (.word iv))
    (hj : s.locals "j" = some (.word jv)) :
    Runs E s (mergeBody ea eb argsA argsB) r → MergePost iv jv s r := by
  intro h
  unfold mergeBody at h
  rw [runs_dec] at h
  split at h
  swap
  · subst h
    simp only [St.err, MergePost]
  split at h
  swap
  · subst h
    simp only [St.err, MergePost]
  rename_i va _ _
  obtain ⟨rb, hb, rfl⟩ := h
  rw [runs_dec] at hb
  split at hb
  swap
  · subst hb
    simp only [St.err, restorePanValueFfiLocal, MergePost]
  split at hb
  swap
  · subst hb
    simp only [St.err, restorePanValueFfiLocal, MergePost]
  rename_i vb _ _
  obtain ⟨rb2, hb2, rfl⟩ := hb
  rcases runs_decCall_inv hb2 with herr | ⟨parameters, cbody, values, cl, rb3, -, -, -, -, hout⟩
  · cases rb2 with
    | error l g m f => simp only [restorePanValueFfiLocal, MergePost]
    | _ => cases herr
  cases rb3 with
  | returned lr g m ffi vs =>
    cases vs with
    | nil => exact hout.elim
    | cons v rest =>
      cases rest with
      | cons v' rest' => exact hout.elim
      | nil =>
        obtain ⟨r4, -, hrun4, rfl⟩ := hout
        dsimp only at hrun4 ⊢
        obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp hrun4
        have hi3 : updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "a" va) "b" vb)
            "gt" v "i" = some (.word iv) := by
          simp (config := { decide := true }) only [update_lookup, if_false]
          exact hi
        have hj3 : updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "a" va) "b" vb)
            "gt" v "j" = some (.word jv) := by
          simp (config := { decide := true }) only [update_lookup, if_false]
          exact hj
        have hfr3 : ∀ y, y ≠ "a" → y ≠ "b" → y ≠ "gt" →
            updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "a" va) "b" vb)
              "gt" v y = s.locals y := by
          intro y h1 h2 h3
          simp [update_lookup, h1, h2, h3]
        rw [runs_ite] at h₁
        split at h₁
        swap
        · subst h₁
          simp only [St.err] at hrest
          subst hrest
          simp only [restorePanValueFfiLocal, MergePost]
        split at h₁
        · have f := incr_after_call hE (s := ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "a" va) "b" vb)
            "gt" v, g, m, ffi⟩) hj3 h₁
          cases r₁ with
          | normal l1 g1 m1 f1 =>
            obtain ⟨hj1, hfr⟩ := f
            simp only at hrest
            exact merge_finish hE (iv' := iv) (jv' := jv + 1)
              ((hfr "mid" (by decide)).trans (hfr3 "mid" (by decide) (by decide) (by decide)))
              ((hfr "right" (by decide)).trans
                (hfr3 "right" (by decide) (by decide) (by decide)))
              ((hfr "i" (by decide)).trans hi3) hj1 (Or.inr ⟨rfl, rfl⟩) hrest
          | continued l1 g1 m1 f1 => exact f.elim
          | broke l1 g1 m1 f1 => exact f.elim
          | _ =>
            simp only at hrest
            subst hrest
            simp only [restorePanValueFfiLocal, MergePost]
        · have f := incr_after_call hE (s := ⟨updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "a" va) "b" vb)
            "gt" v, g, m, ffi⟩) hi3 h₁
          cases r₁ with
          | normal l1 g1 m1 f1 =>
            obtain ⟨hi1, hfr⟩ := f
            simp only at hrest
            exact merge_finish hE (iv' := iv + 1) (jv' := jv)
              ((hfr "mid" (by decide)).trans (hfr3 "mid" (by decide) (by decide) (by decide)))
              ((hfr "right" (by decide)).trans
                (hfr3 "right" (by decide) (by decide) (by decide)))
              hi1 ((hfr "j" (by decide)).trans hj3) (Or.inl ⟨rfl, rfl⟩) hrest
          | continued l1 g1 m1 f1 => exact f.elim
          | broke l1 g1 m1 f1 => exact f.elim
          | _ =>
            simp only at hrest
            subst hrest
            simp only [restorePanValueFfiLocal, MergePost]
  | raised lr g m ffi ex v =>
    simp only at hout
    subst hout
    simp only [restorePanValueFfiLocal, MergePost]
  | finalFfi lr g m ffi ev =>
    simp only at hout
    subst hout
    simp only [restorePanValueFfiLocal, MergePost]
  | _ => exact hout.elim

/-- If `a && b` holds then `b` holds. -/
theorem and_second (hE : WordEnv E) {first second : Exp Word} {s : St σ}
    (h : CondTrue E s (.op .and [first, .cmp .notEqual (.const 0) second])) :
    CondTrue E s second := by
  obtain ⟨v, n, hcond, hv⟩ := h
  obtain ⟨va, vb, w, -, hb, hop, hw⟩ := eval_op2_inv hE (cond_of_eval hcond)
  simp only [PanValue.word.injEq] at hw
  subst hw
  obtain ⟨z, x, hz, hx, hcmp⟩ := cmp_eval hE hb
  simp only [PanValue.word.injEq] at hcmp
  change E.eval s (.const 0) = some (.word z) at hz
  change E.eval s second = some (.word x) at hx
  simp only [eval_const, Option.some.injEq, PanValue.word.injEq] at hz
  subst hz
  simp only [wordOp, Option.some.injEq, List.foldr] at hop
  subst hop
  have hxne : x ≠ 0 := by
    intro hx0
    subst hx0
    subst hcmp
    simp [evalPanCmp] at hv
    exact hv (by show (va &&& (0#64 &&& _)) = 0#64; simp)
  refine ⟨x, panValueExpStepCost second, ?_, by simpa using hxne⟩
  simp only [Env.cond, panValueIteCondition, evalPanValueExpCounted]
  rw [show evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
    E.bytesInWord second E.memoryAccess = some (.word x) from hx]
  rfl

/-- A true signed comparison of two locals: both are words, in signed order. -/
theorem less_true (hE : WordEnv E) {x y : VarName} {s : St σ}
    (h : CondTrue E s (.cmp .less (.var .local x) (.var .local y))) :
    ∃ xv yv, s.locals x = some (.word xv) ∧ s.locals y = some (.word yv) ∧ bias xv < bias yv := by
  obtain ⟨v, n, hcond, hv⟩ := h
  obtain ⟨xv, yv, hx, hy, hcmp⟩ := cmp_eval hE (cond_of_eval hcond)
  simp only [PanValue.word.injEq] at hcmp
  change E.eval s (.var .local x) = some (.word xv) at hx
  change E.eval s (.var .local y) = some (.word yv) at hy
  rw [evalF_local] at hx hy
  refine ⟨xv, yv, hx, hy, (signedLess_iff xv yv).mp ?_⟩
  by_cases hlt : RiscV.signedLess xv yv = true
  · exact hlt
  · subst hcmp
    simp [evalPanCmp, hlt] at hv

/-- The guard `(i < mid) && (j < right)`. -/
def mergeGuard : Exp Word :=
  .op .and [.cmp .notEqual (.const (BitVec.ofNat 64 0))
      (.cmp .less (.var .local "i") (.var .local "mid")),
    .cmp .notEqual (.const (BitVec.ofNat 64 0))
      (.cmp .less (.var .local "j") (.var .local "right"))]

/-- Remaining merge steps: the signed distances of `i` to `mid` and `j` to `right`. -/
def mergeMu (s : St σ) : Nat :=
  match s.locals "i", s.locals "mid", s.locals "j", s.locals "right" with
  | some (.word i), some (.word m), some (.word j), some (.word r) =>
      (bias m - bias i) + (bias r - bias j)
  | _, _, _, _ => 0

/-- The merge loop takes at most `2^65 + 1` iterations from any state. -/
theorem merge_loop (hE : GuestEnv E) {ea eb : Exp Word} {argsA argsB : List (Exp Word)}
    {b : Nat} (hb : Costs E (mergeBody ea eb argsA argsB) b) :
    Costs E (.while mergeGuard (mergeBody ea eb argsA argsB))
      ((36893488147419103232 + 1) * (panValueExpStepCost mergeGuard + b + 1)) := by
  refine (Triple.while (I := fun _ => True) (μ := mergeMu) (Q := fun _ => True)
    (e := panValueExpStepCost mergeGuard) (b := b) 36893488147419103232 (condCost _ _)
    (fun _ _ => trivial) ?_).consequence ?_ (Nat.le_refl _) (fun _ h => h)
  · intro k
    refine Triple.of_costs hb ?_
    intro fuel s r n hP hrun hne
    obtain ⟨-, hμ, hct⟩ := hP
    obtain ⟨iv, mv, hi, hmid, hlt1⟩ := less_true hE.word
      (and_first hE.word (c := mergeGuard) rfl hct)
    obtain ⟨jv, rv, hj, hright, hlt2⟩ := less_true hE.word (and_second hE.word hct)
    have hμs : mergeMu s = (bias mv - bias iv) + (bias rv - bias jv) := by
      simp [mergeMu, hi, hmid, hj, hright]
    have hbm := bias_lt mv
    have hbr := bias_lt rv
    have hp := mergeBody_runs hE hi hj (Runs.of_run hrun)
    cases r with
    | normal l g m f =>
      obtain ⟨hmid', hright', hcase⟩ := hp
      refine ⟨trivial, ?_⟩
      show mergeMu ⟨l, g, m, f⟩ < k
      rw [← hμ, hμs]
      rcases hcase with ⟨hi', hj'⟩ | ⟨hi', hj'⟩
      · have hb1 := bias_succ (w := iv) (by omega)
        simp only [mergeMu, hi', hj', hmid', hright', hmid, hright, hb1]
        omega
      · have hb1 := bias_succ (w := jv) (by omega)
        simp only [mergeMu, hi', hj', hmid', hright', hmid, hright, hb1]
        omega
    | continued l g m f => exact hp.elim
    | broke l g m f => exact hp.elim
    | _ => trivial
  · intro s _
    refine ⟨trivial, ?_⟩
    unfold mergeMu
    split
    · rename_i i m j r _ _ _ _
      have := bias_lt m
      have := bias_lt r
      omega
    · omega

/-- A loop whose guard evaluates to 0 ends normally in the same state. -/
theorem runs_while_false {s : St σ} {c : Exp Word} {body : Prog Word} {r : Result σ}
    (h : E.eval s c = some (.word 0)) :
    Runs E s (.while c body) r ↔ r = .normal s.locals s.globals s.memory s.ffi := by
  have hc := cond_eq (E := E) s c
  rw [h] at hc
  simp only [Env.cond] at hc
  constructor
  · rintro ⟨fuel, n, hrun⟩
    cases fuel with
    | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
    | succ fuel =>
      simp only [Env.run] at hrun
      rw [evalPanValueFfiProgSteps, hc] at hrun
      simp at hrun
      exact hrun.1.symm
  · rintro rfl
    refine runs_of_map (fuel := 1) ?_
    simp only [Env.run]
    rw [evalPanValueFfiProgSteps, hc]
    simp

/-- A loop whose body assigns only locals in `M` leaves the other locals alone
and never ends in `continued` or `broke`. -/
theorem while_locals {c : Exp Word} {body : Prog Word} {M : List VarName} {s : St σ}
    {r : Result σ} (hok : localsOk M body = true) (h : Runs E s (.while c body) r) :
    match r with
    | .normal l _ _ _ => ∀ x, x ∉ M → l x = s.locals x
    | .continued _ _ _ _ | .broke _ _ _ _ => False
    | _ => True := by
  obtain ⟨fuel, n, hrun⟩ := h
  have hl := locals_sound fuel M (.while c body) s r n (by simpa only [localsOk] using hok) hrun
  have hne := while_not_escape fuel s r n hrun
  cases r with
  | normal l g m f => exact hl
  | continued l g m f => exact hne.elim
  | broke l g m f => exact hne.elim
  | _ => trivial

/-- The block of a run-loop iteration after `mid` and `right` are computed:
three loops over `i`, `j`, `k`, then `left = right`. -/
def innerBlock (c2 c3 c4 : Exp Word) (b2 b3 b4 : Prog Word) : Prog Word :=
  .dec "i" .one (.var .local "left")
    (.dec "j" .one (.var .local "mid")
      (.dec "k" .one (.var .local "left")
        (.seq (.while c2 b2)
          (.seq (.while c3 b3)
            (.seq (.while c4 b4) (.assign .local "left" (.var .local "right")))))))

/-- The block moves `right` into `left` and changes no other local. -/
def InnerPost (s : St σ) : Result σ → Prop
  | .normal l _ _ _ => l "left" = s.locals "right" ∧ ∀ y, y ≠ "left" → l y = s.locals y
  | .continued _ _ _ _ | .broke _ _ _ _ => False
  | _ => True

set_option maxHeartbeats 2000000 in
theorem innerBlock_runs {c2 c3 c4 : Exp Word} {b2 b3 b4 : Prog Word}
    (h2 : localsOk ["i", "j", "k"] b2 = true) (h3 : localsOk ["i", "j", "k"] b3 = true)
    (h4 : localsOk ["i", "j", "k"] b4 = true) {s : St σ} {r : Result σ} :
    Runs E s (innerBlock c2 c3 c4 b2 b3 b4) r → InnerPost s r := by
  intro h
  unfold innerBlock at h
  rw [runs_dec] at h
  split at h
  swap
  · subst h
    simp only [St.err, InnerPost]
  split at h
  swap
  · subst h
    simp only [St.err, InnerPost]
  rename_i vi _ _
  obtain ⟨rb, hb, rfl⟩ := h
  rw [runs_dec] at hb
  split at hb
  swap
  · subst hb
    simp only [St.err, restorePanValueFfiLocal, InnerPost]
  split at hb
  swap
  · subst hb
    simp only [St.err, restorePanValueFfiLocal, InnerPost]
  rename_i vj _ _
  obtain ⟨rb2, hb2, rfl⟩ := hb
  rw [runs_dec] at hb2
  split at hb2
  swap
  · subst hb2
    simp only [St.err, restorePanValueFfiLocal, InnerPost]
  split at hb2
  swap
  · subst hb2
    simp only [St.err, restorePanValueFfiLocal, InnerPost]
  rename_i vk _ _
  obtain ⟨rb3, hb3, rfl⟩ := hb2
  dsimp only at hb3 ⊢
  have hs3 : ∀ y, y ≠ "i" → y ≠ "j" → y ≠ "k" →
      updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals "i" vi) "j" vj) "k" vk y =
        s.locals y := by
    intro y h1 h2 h3
    simp [update_lookup, h1, h2, h3]
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp hb3
  have f1 := while_locals h2 h₁
  cases r₁ with
  | normal l1 g1 m1 ff1 =>
    simp only at f1 hrest
    obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hrest
    have f2 := while_locals h3 h₂
    cases r₂ with
    | normal l2 g2 m2 ff2 =>
      simp only at f2 hrest₂
      obtain ⟨r₃, h₃', hrest₃⟩ := runs_seq.mp hrest₂
      have f3 := while_locals h4 h₃'
      cases r₃ with
      | normal l3 g3 m3 ff3 =>
        simp only at f3 hrest₃
        have hfr : ∀ y, y ≠ "i" → y ≠ "j" → y ≠ "k" → l3 y = s.locals y := by
          intro y h1 h2 h3
          have hm : y ∉ ["i", "j", "k"] := by simp [h1, h2, h3]
          rw [f3 y hm, f2 y hm, f1 y hm]
          exact hs3 y h1 h2 h3
        rw [runs_assign_local] at hrest₃
        simp only [evalF_local] at hrest₃
        split at hrest₃
        swap
        · subst hrest₃
          simp only [St.err, restorePanValueFfiLocal, InnerPost]
        rename_i v hv
        split at hrest₃
        swap
        · subst hrest₃
          simp only [St.err, restorePanValueFfiLocal, InnerPost]
        subst hrest₃
        simp only [restorePanValueFfiLocal, InnerPost]
        refine ⟨?_, ?_⟩
        · simp (config := { decide := true }) only [restorePanValueLocal, update_lookup,
            if_false, if_true]
          rw [← hv]
          exact hfr "right" (by decide) (by decide) (by decide)
        · intro y hy
          have hyl : (y == "left") = false := by simpa using hy
          by_cases hyi : y = "i"
          · subst hyi
            simp [restorePanValueLocal]
          · have hyi' : (y == "i") = false := by simpa using hyi
            by_cases hyj : y = "j"
            · subst hyj
              simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
            · have hyj' : (y == "j") = false := by simpa using hyj
              by_cases hyk : y = "k"
              · subst hyk
                simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
              · have hyk' : (y == "k") = false := by simpa using hyk
                simp only [restorePanValueLocal, update_lookup, hyi', hyj', hyk', hyl,
                  Bool.false_eq_true, if_false]
                exact hfr y hyi hyj hyk
      | continued l3 g3 m3 ff3 => exact f3.elim
      | broke l3 g3 m3 ff3 => exact f3.elim
      | _ =>
        simp only at hrest₃
        subst hrest₃
        simp only [restorePanValueFfiLocal, InnerPost]
    | continued l2 g2 m2 ff2 => exact f2.elim
    | broke l2 g2 m2 ff2 => exact f2.elim
    | _ =>
      simp only at hrest₂
      subst hrest₂
      simp only [restorePanValueFfiLocal, InnerPost]
  | continued l1 g1 m1 ff1 => exact f1.elim
  | broke l1 g1 m1 ff1 => exact f1.elim
  | _ =>
    simp only at hrest
    subst hrest
    simp only [restorePanValueFfiLocal, InnerPost]

/-- `x` clamped to at most `n` (unsigned). -/
def clampU (x n : Word) : Word := if n < x then n else x

/-- `if n <+ x { x = n; }`. -/
theorem clampIte_runs (hE : GuestEnv E) {x : VarName} {xv nw : Word} {s : St σ} {r : Result σ}
    (hx : s.locals x = some (.word xv)) (hn : s.locals "n" = some (.word nw)) :
    Runs E s (.ite (.cmp .lower (.var .local "n") (.var .local x))
      (.assign .local x (.var .local "n")) .skip) r →
    ∃ l, r = .normal l s.globals s.memory s.ffi ∧ l x = some (.word (clampU xv nw)) ∧
      ∀ y, y ≠ x → l y = s.locals y := by
  intro h
  rw [runs_ite] at h
  simp only [evalF_cmp hE.word, evalF_local, hx, hn] at h
  by_cases hlt : nw < xv
  · simp [evalPanCmp, hlt] at h
    rw [runs_assign_local] at h
    simp [evalF_local, hn, panValueAssignmentValid, hx, shape_word, shape_matches_self] at h
    subst h
    refine ⟨_, rfl, by simp [update_lookup, clampU, hlt], ?_⟩
    intro y hy
    have : (y == x) = false := by simpa using hy
    simp [update_lookup, this]
  · simp [evalPanCmp, hlt] at h
    rw [runs_skip] at h
    subst h
    exact ⟨_, rfl, by simp [clampU, hlt, hx], fun _ _ => rfl⟩

/-- One iteration of the run loop, around the inner block `blk`. -/
def runBody (blk : Prog Word) : Prog Word :=
  .dec "mid" .one (.op .add [.var .local "left", .var .local "width"])
    (.seq (.ite (.cmp .lower (.var .local "n") (.var .local "mid"))
        (.assign .local "mid" (.var .local "n")) .skip)
      (.dec "right" .one (.op .add [.var .local "mid", .var .local "width"])
        (.seq (.ite (.cmp .lower (.var .local "n") (.var .local "right"))
            (.assign .local "right" (.var .local "n")) .skip)
          blk)))

/-- The run-loop iteration moves `left` to the end of the merged runs. -/
def RunPost (lw ww nw : Word) (s : St σ) : Result σ → Prop
  | .normal l _ _ _ =>
      l "left" = some (.word (clampU (clampU (lw + ww) nw + ww) nw)) ∧
        ∀ y, y ≠ "left" → l y = s.locals y
  | .continued _ _ _ _ | .broke _ _ _ _ => False
  | _ => True

set_option maxHeartbeats 2000000 in
theorem runBody_runs (hE : GuestEnv E) {blk : Prog Word}
    (hblk : ∀ (s : St σ) (r : Result σ), Runs E s blk r → InnerPost s r) {lw ww nw : Word}
    {s : St σ} {r : Result σ} (hl : s.locals "left" = some (.word lw))
    (hw : s.locals "width" = some (.word ww)) (hn : s.locals "n" = some (.word nw)) :
    Runs E s (runBody blk) r → RunPost lw ww nw s r := by
  intro h
  unfold runBody at h
  rw [runs_dec] at h
  simp only [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_local, hl, hw, wordsProj_cons,
    wordsProj_nil, wordOp, List.foldr, Option.map_some, shape_word, shape_matches_self,
    if_true] at h
  obtain ⟨rb, hb, rfl⟩ := h
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp hb
  obtain ⟨l1, rfl, hmid1, hfr1⟩ := clampIte_runs hE (x := "mid") (xv := lw + (ww + 0))
    (s := ⟨updatePanValueMap s.locals "mid" (PanValue.word (lw + (ww + 0))), s.globals, s.memory,
      s.ffi⟩) (by simp [update_lookup])
    (by simp (config := { decide := true }) only [update_lookup, if_false]; exact hn) h₁
  simp only at hrest
  have hw1 : l1 "width" = some (.word ww) := by
    rw [hfr1 "width" (by decide)]
    simp (config := { decide := true }) only [update_lookup, if_false]
    exact hw
  have hn1 : l1 "n" = some (.word nw) := by
    rw [hfr1 "n" (by decide)]
    simp (config := { decide := true }) only [update_lookup, if_false]
    exact hn
  rw [runs_dec] at hrest
  simp only [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_local, hmid1, hw1,
    wordsProj_cons, wordsProj_nil, wordOp, List.foldr, Option.map_some, shape_word,
    shape_matches_self, if_true] at hrest
  obtain ⟨rb2, hb2, rfl⟩ := hrest
  obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hb2
  obtain ⟨l2, rfl, hright2, hfr2⟩ := clampIte_runs hE (x := "right")
    (xv := clampU (lw + (ww + 0)) nw + (ww + 0))
    (s := ⟨updatePanValueMap l1 "right"
      (PanValue.word (clampU (lw + (ww + 0)) nw + (ww + 0))), s.globals, s.memory, s.ffi⟩)
    (by simp [update_lookup])
    (by simp (config := { decide := true }) only [update_lookup, if_false]; exact hn1) h₂
  simp only at hrest₂
  have hp := hblk _ _ hrest₂
  dsimp only at hmid1 hfr1 hright2 hfr2
  cases rb2 with
  | normal l g m f =>
    obtain ⟨hleft, hfr⟩ := hp
    dsimp only at hleft hfr
    simp only [restorePanValueFfiLocal, RunPost]
    refine ⟨?_, ?_⟩
    · simp (config := { decide := true }) only [restorePanValueLocal, if_false]
      rw [hleft, hright2]
      simp
    · intro y hy
      by_cases hym : y = "mid"
      · subst hym
        simp [restorePanValueLocal]
      · have hym' : (y == "mid") = false := by simpa using hym
        by_cases hyr : y = "right"
        · subst hyr
          simp (config := { decide := true }) only [restorePanValueLocal, if_false, if_true]
          rw [hfr1 "right" (by decide)]
          simp (config := { decide := true }) only [update_lookup, if_false]
        · have hyr' : (y == "right") = false := by simpa using hyr
          simp only [restorePanValueLocal, hym', hyr', Bool.false_eq_true, if_false]
          rw [hfr y hy, hfr2 y hyr]
          simp only [update_lookup, hyr', Bool.false_eq_true, if_false]
          rw [hfr1 y hym]
          simp only [update_lookup, hym', Bool.false_eq_true, if_false]
  | continued l g m f => exact hp.elim
  | broke l g m f => exact hp.elim
  | _ => simp only [restorePanValueFfiLocal, RunPost]

/-- With `1 ≤ width ≤ 2^63` and `left < n < 2^63`, the clamped end is past
`left` and at most `n`; nothing wraps. -/
theorem clamp_progress {lw ww nw : Word} (hw1 : 1 ≤ ww.toNat) (hw2 : ww.toNat ≤ 2 ^ 63)
    (hn : nw.toNat < 2 ^ 63) (hl : lw.toNat < nw.toNat) :
    lw.toNat < (clampU (clampU (lw + ww) nw + ww) nw).toNat ∧
      (clampU (clampU (lw + ww) nw + ww) nw).toNat ≤ nw.toNat := by
  have := lw.isLt
  have := ww.isLt
  have := nw.isLt
  have h1 : (lw + ww).toNat = lw.toNat + ww.toNat := by
    rw [BitVec.toNat_add]
    omega
  by_cases c1 : nw < lw + ww
  · have hM : clampU (lw + ww) nw = nw := by simp [clampU, c1]
    rw [hM]
    have h2 : (nw + ww).toNat = nw.toNat + ww.toNat := by
      rw [BitVec.toNat_add]
      omega
    have c2 : nw < nw + ww := by
      rw [BitVec.lt_def, h2]
      omega
    have hR : clampU (nw + ww) nw = nw := by simp [clampU, c2]
    rw [hR]
    omega
  · have hM : clampU (lw + ww) nw = lw + ww := by simp [clampU, c1]
    rw [hM]
    have c1' : ¬ nw.toNat < lw.toNat + ww.toNat := by
      rw [BitVec.lt_def, h1] at c1
      exact c1
    have h2 : (lw + ww + ww).toNat = lw.toNat + ww.toNat + ww.toNat := by
      rw [BitVec.toNat_add, h1]
      omega
    by_cases c2 : nw < lw + ww + ww
    · have hR : clampU (lw + ww + ww) nw = nw := by simp [clampU, c2]
      rw [hR]
      omega
    · have hR : clampU (lw + ww + ww) nw = lw + ww + ww := by simp [clampU, c2]
      rw [hR, h2]
      have c2' : ¬ nw.toNat < lw.toNat + ww.toNat + ww.toNat := by
        rw [BitVec.lt_def, h2] at c2
        exact c2
      omega

theorem bias_small {x : Word} (h : x.toNat < 2 ^ 63) : bias x = x.toNat + 2 ^ 63 := by
  have := x.isLt
  unfold bias
  omega

theorem bias_large {x : Word} (h : 2 ^ 63 ≤ x.toNat) : bias x = x.toNat - 2 ^ 63 := by
  have := x.isLt
  unfold bias
  omega

/-- The guard `left < n`. -/
def runGuard : Exp Word := .cmp .less (.var .local "left") (.var .local "n")

/-- The run loop's invariant relative to the locals `L0` at entry. -/
def RunInv (nw : Word) (L0 : VarName → Option (PanValue Word)) (s : St σ) : Prop :=
  (∀ y, y ≠ "left" → s.locals y = L0 y) ∧
    ((nw.toNat < 2 ^ 63 ∧ ∃ lw : Word, s.locals "left" = some (.word lw) ∧
        lw.toNat ≤ nw.toNat) ∨
      (2 ^ 63 ≤ nw.toNat ∧ s.locals "left" = some (.word 0)))

/-- Elements left to merge. -/
def runMu (nw : Word) (s : St σ) : Nat :=
  match s.locals "left" with
  | some (.word lw) => nw.toNat - lw.toNat
  | _ => 0

/-- The run loop, entered with `left = 0`, ends within `2^64 + 1` iterations
and changes no local but `left`, for `1 ≤ width ≤ 2^63`. -/
theorem run_loop (hE : GuestEnv E) {blk : Prog Word}
    (hblk : ∀ (s : St σ) (r : Result σ), Runs E s blk r → InnerPost s r) {b : Nat}
    (hb : Costs E (runBody blk) b) (ww nw : Word) (hw1 : 1 ≤ ww.toNat)
    (hw2 : ww.toNat ≤ 2 ^ 63) (L0 : VarName → Option (PanValue Word))
    (hLw : L0 "width" = some (.word ww)) (hLn : L0 "n" = some (.word nw)) :
    Triple E (fun s => (∀ y, y ≠ "left" → s.locals y = L0 y) ∧
        s.locals "left" = some (.word 0))
      (.while runGuard (runBody blk))
      ((18446744073709551616 + 1) * (panValueExpStepCost runGuard + b + 1))
      (fun r => match r with
        | .normal l _ _ _ => ∀ y, y ≠ "left" → l y = L0 y
        | .continued _ _ _ _ | .broke _ _ _ _ => False
        | _ => True) := by
  refine (Triple.while (I := RunInv nw L0) (μ := runMu nw)
    (Q := fun r => match r with
      | .normal l _ _ _ => ∀ y, y ≠ "left" → l y = L0 y
      | .continued _ _ _ _ | .broke _ _ _ _ => False
      | _ => True)
    (e := panValueExpStepCost runGuard) (b := b) 18446744073709551616 (condCost _ _)
    (fun s hI => hI.1) ?_).consequence ?_ (Nat.le_refl _) (fun _ h => h)
  · intro k
    refine Triple.of_costs hb ?_
    intro fuel s r n hP hrun hne
    obtain ⟨⟨hfr, hcase⟩, hμ, hct⟩ := hP
    obtain ⟨lw, nw', hl, hn', hlt⟩ := less_true hE.word hct
    have hn : s.locals "n" = some (.word nw) := by rw [hfr "n" (by decide)]; exact hLn
    have hw : s.locals "width" = some (.word ww) := by rw [hfr "width" (by decide)]; exact hLw
    rw [hn] at hn'
    simp only [Option.some.injEq, PanValue.word.injEq] at hn'
    subst hn'
    have hnlt := nw.isLt
    have hllt := lw.isLt
    rcases hcase with ⟨hnsmall, lw', hl', hle⟩ | ⟨hnbig, hl0⟩
    · rw [hl] at hl'
      simp only [Option.some.injEq, PanValue.word.injEq] at hl'
      subst hl'
      have hlw : lw.toNat < nw.toNat := by
        rw [bias_small (by omega), bias_small hnsmall] at hlt
        omega
      have hprog := clamp_progress hw1 hw2 hnsmall hlw
      have hp := runBody_runs hE hblk hl hw hn (Runs.of_run hrun)
      cases r with
      | normal l g m f =>
        obtain ⟨hleft, hfr'⟩ := hp
        refine ⟨⟨fun y hy => (hfr' y hy).trans (hfr y hy),
          Or.inl ⟨hnsmall, _, hleft, hprog.2⟩⟩, ?_⟩
        show runMu nw ⟨l, g, m, f⟩ < k
        rw [← hμ]
        simp only [runMu, hleft, hl]
        omega
      | continued l g m f => exact hp.elim
      | broke l g m f => exact hp.elim
      | _ => trivial
    · rw [hl] at hl0
      simp only [Option.some.injEq, PanValue.word.injEq] at hl0
      subst hl0
      rw [bias_large hnbig, bias_small (by decide)] at hlt
      simp at hlt
      omega
  · intro s hP
    obtain ⟨hfr, hl⟩ := hP
    have hnlt := nw.isLt
    refine ⟨⟨hfr, ?_⟩, ?_⟩
    · by_cases hn : nw.toNat < 2 ^ 63
      · exact Or.inl ⟨hn, 0, hl, by simp⟩
      · exact Or.inr ⟨by omega, hl⟩
    · show runMu nw s ≤ 18446744073709551616
      simp only [runMu, hl]
      omega

/-- With `left = mid = right = 0` no inner loop runs, so the block ends normally. -/
theorem innerBlock_zero (hE : GuestEnv E) {b2 b3 b4 : Prog Word} {s : St σ} {r : Result σ}
    (hl : s.locals "left" = some (.word 0)) (hm : s.locals "mid" = some (.word 0))
    (hr : s.locals "right" = some (.word 0)) :
    Runs E s (innerBlock mergeGuard (.cmp .less (.var .local "i") (.var .local "mid"))
      (.cmp .less (.var .local "j") (.var .local "right")) b2 b3 b4) r →
    ∃ l g m f, r = .normal l g m f := by
  intro h
  unfold innerBlock at h
  rw [runs_dec] at h
  simp only [evalF_local, hl, shape_word, shape_matches_self, if_true] at h
  obtain ⟨rb, hb, rfl⟩ := h
  rw [runs_dec] at hb
  simp (config := { decide := true }) only [evalF_local, update_lookup, if_false, hm,
    shape_word, shape_matches_self, if_true] at hb
  obtain ⟨rb2, hb2, rfl⟩ := hb
  rw [runs_dec] at hb2
  simp (config := { decide := true }) only [evalF_local, update_lookup, if_false, hl,
    shape_word, shape_matches_self, if_true] at hb2
  obtain ⟨rb3, hb3, rfl⟩ := hb2
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp hb3
  rw [runs_while_false (by
    simp (config := { decide := true }) only [mergeGuard, evalF_op hE.word, evalArgs_cons,
      evalArgs_nil, evalF_cmp hE.word, evalF_local, eval_const, update_lookup, if_true,
      if_false, hm, hr, wordsProj_cons, wordsProj_nil, wordOp, List.foldr, Option.map_some]
    rfl)] at h₁
  subst h₁
  simp only at hrest
  obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hrest
  rw [runs_while_false (by
    simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      if_true, if_false, hm]
    rfl)] at h₂
  subst h₂
  simp only at hrest₂
  obtain ⟨r₃, h₃, hrest₃⟩ := runs_seq.mp hrest₂
  rw [runs_while_false (by
    simp (config := { decide := true }) only [evalF_cmp hE.word, evalF_local, update_lookup,
      if_true, if_false, hr]
    rfl)] at h₃
  subst h₃
  simp only at hrest₃
  rw [runs_assign_local] at hrest₃
  simp (config := { decide := true }) only [evalF_local, update_lookup, if_false, hr, hl,
    panValueAssignmentValid, shape_word, shape_matches_self, if_true] at hrest₃
  subst hrest₃
  exact ⟨_, _, _, _, rfl⟩

theorem clamp_zero (nw : Word) : clampU (0 + (0 + 0)) nw = 0 := by
  simp [clampU]

set_option maxHeartbeats 2000000 in
/-- With `left = width = 0` a run-loop iteration ends normally. -/
theorem runBody_zero_normal (hE : GuestEnv E) {blk : Prog Word}
    (hz : ∀ (s : St σ) (r : Result σ), s.locals "left" = some (.word 0) →
      s.locals "mid" = some (.word 0) → s.locals "right" = some (.word 0) →
      Runs E s blk r → ∃ l g m f, r = .normal l g m f)
    {nw : Word} {s : St σ} {r : Result σ} (hl : s.locals "left" = some (.word 0))
    (hw : s.locals "width" = some (.word 0)) (hn : s.locals "n" = some (.word nw)) :
    Runs E s (runBody blk) r → ∃ l g m f, r = .normal l g m f := by
  intro h
  unfold runBody at h
  rw [runs_dec] at h
  simp only [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_local, hl, hw, wordsProj_cons,
    wordsProj_nil, wordOp, List.foldr, Option.map_some, shape_word, shape_matches_self,
    if_true] at h
  obtain ⟨rb, hb, rfl⟩ := h
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp hb
  obtain ⟨l1, rfl, hmid1, hfr1⟩ := clampIte_runs hE (x := "mid") (xv := 0 + (0 + 0))
    (s := ⟨updatePanValueMap s.locals "mid" (PanValue.word (0 + (0 + 0))), s.globals, s.memory,
      s.ffi⟩) (by simp [update_lookup])
    (by simp (config := { decide := true }) only [update_lookup, if_false]; exact hn) h₁
  simp only at hrest
  dsimp only at hmid1 hfr1
  rw [clamp_zero] at hmid1
  have hw1 : l1 "width" = some (.word 0) := by
    rw [hfr1 "width" (by decide)]
    simp (config := { decide := true }) only [update_lookup, if_false]
    exact hw
  have hn1 : l1 "n" = some (.word nw) := by
    rw [hfr1 "n" (by decide)]
    simp (config := { decide := true }) only [update_lookup, if_false]
    exact hn
  have hl1 : l1 "left" = some (.word 0) := by
    rw [hfr1 "left" (by decide)]
    simp (config := { decide := true }) only [update_lookup, if_false]
    exact hl
  rw [runs_dec] at hrest
  simp only [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_local, hmid1, hw1,
    wordsProj_cons, wordsProj_nil, wordOp, List.foldr, Option.map_some, shape_word,
    shape_matches_self, if_true] at hrest
  obtain ⟨rb2, hb2, rfl⟩ := hrest
  obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hb2
  obtain ⟨l2, rfl, hright2, hfr2⟩ := clampIte_runs hE (x := "right") (xv := 0 + (0 + 0))
    (s := ⟨updatePanValueMap l1 "right" (PanValue.word (0 + (0 + 0))), s.globals, s.memory,
      s.ffi⟩) (by simp [update_lookup])
    (by simp (config := { decide := true }) only [update_lookup, if_false]; exact hn1) h₂
  simp only at hrest₂
  dsimp only at hright2 hfr2
  rw [clamp_zero] at hright2
  have hl2 : l2 "left" = some (.word 0) := by
    rw [hfr2 "left" (by decide)]
    simp (config := { decide := true }) only [update_lookup, if_false]
    exact hl1
  have hm2 : l2 "mid" = some (.word 0) := by
    rw [hfr2 "mid" (by decide)]
    simp (config := { decide := true }) only [update_lookup, if_false]
    exact hmid1
  obtain ⟨l, g, m, f, rfl⟩ := hz _ _ hl2 hm2 hright2 hrest₂
  exact ⟨_, _, _, _, rfl⟩

/-- With `width = 0` and `0 <s n`, the run loop entered at `left = 0` never returns. -/
theorem run_loop_zero (hE : GuestEnv E) {blk : Prog Word}
    (hblk : ∀ (s : St σ) (r : Result σ), Runs E s blk r → InnerPost s r)
    (hz : ∀ (s : St σ) (r : Result σ), s.locals "left" = some (.word 0) →
      s.locals "mid" = some (.word 0) → s.locals "right" = some (.word 0) →
      Runs E s blk r → ∃ l g m f, r = .normal l g m f)
    {nw : Word} (hpos : bias 0 < bias nw) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat)
    (hl : s.locals "left" = some (.word 0)) (hw : s.locals "width" = some (.word 0))
    (hn : s.locals "n" = some (.word nw))
    (hrun : E.run fuel s (.while runGuard (runBody blk)) = some (r, n)) :
    r.isError = true := by
  refine while_never (E := E)
    (Z := fun s => s.locals "left" = some (.word 0) ∧ s.locals "width" = some (.word 0) ∧
      s.locals "n" = some (.word nw)) (c := runGuard) (body := runBody blk) ?_ ?_ fuel s r n
    ⟨hl, hw, hn⟩ hrun
  · intro s hZ v k hcond
    obtain ⟨hl, -, hn⟩ := hZ
    have heval := cond_of_eval hcond
    simp only [runGuard, evalF_cmp hE.word, evalF_local, hl, hn, Option.some.injEq,
      PanValue.word.injEq] at heval
    subst heval
    have hsl := (signedLess_iff 0 nw).mpr hpos
    have hv : evalPanCmp Cmp.less (0 : Word) nw = 1 := by
      simp [evalPanCmp]
      exact hsl
    rw [hv]
    rfl
  · intro fuel s r n hZ hrun
    obtain ⟨hl, hw, hn⟩ := hZ
    obtain ⟨l, g, m, f, rfl⟩ := runBody_zero_normal hE hz hl hw hn (Runs.of_run hrun)
    obtain ⟨hleft, hfr⟩ := runBody_runs hE hblk hl hw hn (Runs.of_run hrun)
    refine Or.inr ⟨l, g, m, f, rfl, ?_, ?_, ?_⟩
    · show l "left" = _
      rw [hleft]
      simp [clampU]
    · show l "width" = _
      rw [hfr "width" (by decide)]
      exact hw
    · show l "n" = _
      rw [hfr "n" (by decide)]
      exact hn

/-- `width` is 0 or a power of two. -/
def WOk (ww : Word) : Prop := ww = 0 ∨ ∃ t, t ≤ 63 ∧ ww = BitVec.ofNat 64 (2 ^ t)

/-- Doublings left before `width` wraps to 0. -/
def wMu (ww : Word) : Nat := if ww = 0 then 0 else 65 - Nat.log2 ww.toNat

theorem pow_word_toNat {t : Nat} (ht : t ≤ 63) : (BitVec.ofNat 64 (2 ^ t)).toNat = 2 ^ t := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))

theorem pow_word_ne {t : Nat} (ht : t ≤ 63) : BitVec.ofNat 64 (2 ^ t) ≠ (0 : Word) := by
  intro h0
  have := congrArg BitVec.toNat h0
  rw [pow_word_toNat ht] at this
  exact absurd this (Nat.two_pow_pos t).ne'

theorem pow_word_double (t : Nat) :
    BitVec.ofNat 64 (2 ^ t) * (BitVec.ofNat 64 2 : Word) = BitVec.ofNat 64 (2 ^ (t + 1)) := by
  rw [Nat.pow_succ, BitVec.ofNat_mul]

theorem wOk_double {ww : Word} (h : WOk ww) : WOk (ww * BitVec.ofNat 64 2) := by
  rcases h with rfl | ⟨t, ht, rfl⟩
  · left
    simp
  · rw [pow_word_double]
    by_cases h63 : t = 63
    · subst h63
      left
      decide
    · right
      exact ⟨t + 1, by omega, rfl⟩

theorem wMu_double {ww : Word} (h : ∃ t, t ≤ 63 ∧ ww = BitVec.ofNat 64 (2 ^ t)) :
    wMu (ww * BitVec.ofNat 64 2) < wMu ww := by
  obtain ⟨t, ht, rfl⟩ := h
  rw [pow_word_double]
  unfold wMu
  rw [if_neg (pow_word_ne ht), pow_word_toNat ht, Nat.log2_two_pow]
  by_cases h63 : t = 63
  · subst h63
    have h0 : BitVec.ofNat 64 (2 ^ (63 + 1)) = (0 : Word) := by decide
    rw [if_pos h0]
    omega
  · have ht1 : t + 1 ≤ 63 := by omega
    rw [if_neg (pow_word_ne ht1), pow_word_toNat ht1, Nat.log2_two_pow]
    omega

/-- The end of an outer iteration: swap the buffers and double `width`. -/
def swapTail : Prog Word :=
  .dec "swap" .one (.var .local "src")
    (.seq (.assign .local "src" (.var .local "dst"))
      (.seq (.assign .local "dst" (.var .local "swap"))
        (.assign .local "width"
          (.panOp .mul [.var .local "width", .const (BitVec.ofNat 64 2)]))))

def SwapPost (ww nw : Word) : Result σ → Prop
  | .normal l _ _ _ =>
      l "width" = some (.word (ww * BitVec.ofNat 64 2)) ∧ l "n" = some (.word nw)
  | .continued _ _ _ _ | .broke _ _ _ _ => False
  | _ => True

set_option maxHeartbeats 2000000 in
theorem swapTail_runs (hE : GuestEnv E) {ww nw : Word} {s : St σ} {r : Result σ}
    (hw : s.locals "width" = some (.word ww)) (hn : s.locals "n" = some (.word nw)) :
    Runs E s swapTail r → SwapPost ww nw r := by
  intro h
  unfold swapTail at h
  rw [runs_dec] at h
  split at h
  swap
  · subst h
    simp only [St.err, SwapPost]
  split at h
  swap
  · subst h
    simp only [St.err, SwapPost]
  rename_i vs _ _
  obtain ⟨rb, hb, rfl⟩ := h
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp hb
  rw [runs_assign_local] at h₁
  split at h₁
  swap
  · subst h₁
    simp only [St.err] at hrest
    subst hrest
    simp only [restorePanValueFfiLocal, SwapPost]
  split at h₁
  swap
  · subst h₁
    simp only [St.err] at hrest
    subst hrest
    simp only [restorePanValueFfiLocal, SwapPost]
  subst h₁
  simp only at hrest
  obtain ⟨r₂, h₂, hrest₂⟩ := runs_seq.mp hrest
  rw [runs_assign_local] at h₂
  split at h₂
  swap
  · subst h₂
    simp only [St.err] at hrest₂
    subst hrest₂
    simp only [restorePanValueFfiLocal, SwapPost]
  split at h₂
  swap
  · subst h₂
    simp only [St.err] at hrest₂
    subst hrest₂
    simp only [restorePanValueFfiLocal, SwapPost]
  subst h₂
  simp only at hrest₂
  rw [runs_assign_local] at hrest₂
  simp (config := { decide := true }) only [evalF_panOp, evalArgs_cons, evalArgs_nil,
    evalF_local, eval_const, update_lookup, if_false, hw, Option.map_some, evalPanOp_mul,
    panValueAssignmentValid, shape_word, shape_matches_self, if_true] at hrest₂
  subst hrest₂
  simp only [restorePanValueFfiLocal, SwapPost]
  refine ⟨?_, ?_⟩
  · simp (config := { decide := true }) only [restorePanValueLocal, update_lookup, if_false,
      if_true]
  · simp (config := { decide := true }) only [restorePanValueLocal, update_lookup, if_false]
    exact hn

end InitECandidate.Solver.GuestBound
