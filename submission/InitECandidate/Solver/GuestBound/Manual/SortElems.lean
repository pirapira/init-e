import InitECandidate.Solver.GuestBound.LocalsFrame
import InitECandidate.Solver.GuestBound.Manual.Taylor

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

end InitECandidate.Solver.GuestBound
