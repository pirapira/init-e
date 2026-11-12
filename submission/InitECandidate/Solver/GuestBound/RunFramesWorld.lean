import InitECandidate.Solver.GuestBound.WorldAssn
import InitECandidate.Solver.GuestBound.WorldRollback
import InitECandidate.Solver.GuestBound.DispatchC

/-!
# The `run_frames` bound over the concrete world assertion

`run_frames_bound_A`: the bound with `W := WorldA Rg`; `state_restore` is
discharged by `restore_spec`. What remains assumed: the unproved handlers,
the two cost bounds, and the `finish_child` branch (`ChildSpec`).

`rollback_framed`: `rollback_child_access(child)` in the form `ChildSpec`
needs, on the child's access cells and the world.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- What frames may know about the world with registry `Rg`. -/
def Reg.info (Rg : Reg) : WInfo := ⟨Rg.live, Rg.B⟩

/-- `run_frames` from a chain of frames over the world `WorldA Rg`, for a
registry `Rg` that may change from step to step. Assumed: the handlers not yet
proved (`hrest` for those that stay in their frame, `hcall` for the six that
may push a frame), the step costs of the two blocks, and the `finish_child`
branch. -/
theorem run_frames_bound_A (hE : GuestEnv E)
    (hrest : ∀ f, f ∈ restOpsM → f ∉ callOps → HandlerSpecM E f)
    (hcall : ∀ f, f ∈ callOps → HandlerSpecPush E WorldA Reg.info f) (BD BF : Nat)
    (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (hC : ChildSpec E WorldA Reg.info)
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (k : Nat) (hI : chainInv WorldA Reg.info k s.globals s.memory) (fuel : Nat)
    (r : Result σ) (n : Nat) (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (k + 1 + 1) * (expCost rfCond + (BD + BF + 200) + 1) + 10 :=
  run_frames_bound_chainC WorldA Reg.info hE hrest hcall BD BF costD costF
    (fun a n hI => finish_chain hE (restore_spec hE) hC a n hI) parameters body hlookup s k hI
    fuel r n hrun hne

theorem rollback_raises (hE : GuestEnv E) :
    FunRaises E (fun x => x == "TrapErr") "rollback_child_access" :=
  raiseFn_sound _ hE.functions 8 "rollback_child_access"
    (show raiseFn (fun x => x == "TrapErr") Guest.Software.guestAst 8 "rollback_child_access" =
      true by decide +kernel)

/-- `rollback_child_access(child)` on the child's access cells and the world. -/
theorem rollback_framed (hE : GuestEnv E) (Rg : Reg) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "rollback_child_access" E.functions = some (parameters, body))
    (s : St σ) (child : Word) (A : AccSt) (R : Assn)
    (hc : s.locals "child" = some (.word child)) (hlo : 2952790016 ≤ child.toNat)
    (hhi : child.toNat + 280 ≤ 2 ^ 62) (hD : Rg.live A.t1 ∧ Rg.live A.t2)
    (h : (AccCells child A ⋆ WorldA Rg ⋆ R).holds s) :
    WPr E s body (fun r => Trap r ∨ ∃ l g m, r = .returned l g m s.ffi [.word 0#64] ∧
      (AccCells child A ⋆ WorldA Rg ⋆ R).holds (⟨l, g, m, s.ffi⟩ : St σ)) := by
  intro r hr
  have hcells := h
  unfold AccCells at hcells
  have r1 : Rd s.memory (child + 168#64) A.t1 := Assn.mem_at hcells (by look)
  have r3 : Rd s.memory (child + 176#64) A.t2 := Assn.mem_at hcells (by look)
  have r2 : Rd s.memory (child + 264#64) A.n1 := Assn.mem_at hcells (by look)
  have r4 : Rd s.memory (child + 272#64) A.n2 := Assn.mem_at hcells (by look)
  have hw : (WorldA Rg ⋆ (AccCells child A ⋆ R)).holds s := Assn.holds_perm h (by ac_rfl)
  have hW : WorldTJ Rg s.globals s.memory := Assn.region_elim hw
  rcases rollback_raises hE parameters body hlookup s r hr with he | hra
  · exact Or.inl he
  rcases rollback_world hE parameters body hlookup Rg s r child A.t1 A.n1 A.t2 A.n2 hc hlo hhi r1
    r2 r3 r4 hD.1 hD.2 hW hr with hst | ⟨l, m', rfl, hW', hm⟩
  · cases r with
    | error l g m f => exact Or.inl rfl
    | raised l g m f e v =>
      have he : e = "TrapErr" := by simpa [RaiseIn] using hra
      exact Or.inr (Or.inl he)
    | finalFfi l g m f ev => exact Or.inr (Or.inl trivial)
    | _ => exact absurd hst (fun h => h)
  · refine Or.inr (Or.inr ⟨l, s.globals, m', rfl, ?_⟩)
    have hw' : (WorldA Rg ⋆ (AccCells child A ⋆ R)).holds (⟨l, s.globals, m', s.ffi⟩ : St σ) := by
      refine Assn.region_change hw (worldP_local Rg) (fun k hk => ?_) hW'
      cases k with
      | mem a =>
        show m' a = s.memory a
        refine hm a ?_
        by_contra hc'
        exact hk ⟨by omega, by omega⟩
      | glob x => rfl
    exact Assn.holds_perm hw' (by ac_rfl)

end InitECandidate.Solver.GuestBound
