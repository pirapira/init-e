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

end InitECandidate.Solver.GuestBound
