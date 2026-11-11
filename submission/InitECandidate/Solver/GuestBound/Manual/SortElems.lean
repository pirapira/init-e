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

end InitECandidate.Solver.GuestBound
