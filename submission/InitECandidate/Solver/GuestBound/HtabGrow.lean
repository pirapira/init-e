import InitECandidate.Solver.GuestBound.HtabDel
import InitECandidate.Solver.GuestBound.MemCpy
import InitECandidate.Solver.GuestBound.HeapKeep
import InitECandidate.Solver.GuestBound.ShapeFrame

/-!
# Hash tables: `htab_grow`

The three blocks of a table are copied into fresh blocks of twice the node
capacity; the header then points at the copies.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `var x = alloc(e)`: the block starts at the old heap pointer. -/
theorem WPs.decCall_alloc (hE : GuestEnv E) {x : VarName} {e : Exp Word} {body : Prog Word}
    {pv nv : Word} (he : E.eval s e = some (.word nv))
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (h : ∀ qv : Word, pv.toNat + nv.toNat ≤ qv.toNat → InHeap qv →
      WPs E ⟨updatePanValueMap s.locals x (.word pv),
        updatePanValueMap s.globals "heap_ptr" (.word qv), s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "alloc" [e] body) Q := by
  intro r hr
  rcases InitECandidate.Solver.GuestBound.decCall_alloc hE he hp hpH.1 hr with hst | ⟨qv, r', h1, h2, h3, hrun, rfl⟩
  · exact Or.inl hst
  · rcases h qv h1 ⟨h2, h3⟩ r' hrun with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

/-- `memcpy(e1, e2, e3)` as a statement, on disjoint ranges. -/
theorem WPs.call_memcpy (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {dst src nW : Word}
    (h1 : E.eval s e1 = some (.word dst)) (h2 : ∀ y, E.eval s e2 = some y → y = .word src)
    (h3 : E.eval s e3 = some (.word nW)) (P : CpPre dst src nW)
    (h : ∀ m', CopyInv s.memory dst src nW.toNat m' → Q (.normal s.locals s.globals m' s.ffi)) :
    WPs E s (.call (some (none, none)) "memcpy" [e1, e2, e3]) Q := by
  intro r hr
  rcases runs_call_inv (some none) hr with herr | ⟨parameters, body, values, cl, rb, hlookup,
    hvalues, hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h3] at hvalues
  cases he2 : E.eval s e2 with
  | none => rw [he2] at hvalues; simp at hvalues
  | some v2 =>
    have := h2 v2 he2
    subst this
    rw [he2] at hvalues
    simp only [Option.map_some, Option.some.injEq] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    have hpost := memcpy_runs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ rb dst
      src nW (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) P hcallee
    rcases hpost with hst | ⟨l, m', rfl, hci⟩
    · cases rb with
      | raised lr g m f ex v =>
        simp only [CallOutcome] at hout
        subst hout
        exact Or.inl trivial
      | finalFfi lr g m f ev =>
        simp only [CallOutcome] at hout
        subst hout
        exact Or.inl trivial
      | error lr g m f =>
        simp only [CallOutcome] at hout
        exact Or.inl (Stopped.of_error hout)
      | _ => exact absurd hst (fun h => h)
    · simp only [CallOutcome] at hout
      rcases hout with herr | ⟨l', g', hassign, rfl⟩
      · exact Or.inl (Stopped.of_error herr)
      · obtain ⟨rfl, hl, -⟩ := assignResult_frame (M := []) (d := none) rfl hassign
        have : l' = s.locals := funext (fun x => hl x (by simp))
        subst this
        exact Or.inr (h m' hci)

end InitECandidate.Solver.GuestBound
