import InitECandidate.Solver.GuestBound.ScratchRuns
import InitECandidate.Solver.GuestBound.RlpTotal
import InitECandidate.Solver.GuestBound.CallHandler
import InitECandidate.Solver.GuestBound.HtabDelInv

/-!
# RLP validation writes only free scratch memory

`ScrKeep pv fv s g m ffi` relates a state `s` whose scratch pointer is `pv`
and frame-memory pointer is `fv` to later globals, memory and FFI state: the
scratch pointer stayed inside `[fv, pv]`, no other global changed, and memory
outside `[fv, pv)` is as it was. `_rlp_validate_items_body` satisfies it on
return (its continuation records are scratch blocks). First of the frame
facts under `rlp_list_count` for the witness-decoding loop (issue #21).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Only free scratch memory changed, and the scratch pointer moved inside the arena. -/
def ScrKeep (pv fv : Word) (s : St σ) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (ffi : FfiState σ) : Prop :=
  ffi = s.ffi ∧ (∀ x, x ≠ "scratch_ptr" → g x = s.globals x) ∧
    (∃ qv : Word, g "scratch_ptr" = some (.word qv) ∧ fv.toNat ≤ qv.toNat ∧
      qv.toNat ≤ pv.toNat) ∧
    ∀ x : Word, (x.toNat < fv.toNat ∨ pv.toNat ≤ x.toNat) → m x = s.memory x

/-- `x = lds 1 a;` for a word-valued local `x`. -/
theorem WPs.assign_load (hE : GuestEnv E) {x : VarName} {a : Exp Word} {old : Word}
    (hx : s.locals x = some (.word old))
    (h : ∀ w : Word, Q (.normal (updatePanValueMap s.locals x (.word w)) s.globals s.memory
      s.ffi)) :
    WPs E s (.assign .local x (.load .one a)) Q := by
  intro r hr
  rw [runs_assign_local] at hr
  cases hv : E.eval s (.load .one a) with
  | none => rw [hv] at hr; simp only at hr; subst hr; exact Or.inl (Stopped.err s)
  | some y =>
    obtain ⟨addr, v, -, rfl, -⟩ := eval_load_one hE.mem hv
    rw [hv] at hr
    simp only [panValueAssignmentValid, hx, shape_word, shape_matches_self, if_true] at hr
    subst hr
    exact Or.inr (h v)

/-- What a returning `rlp_item_header` leaves: nothing changed, and the value
is a header of two words and a flag. -/
theorem rlpheader_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {lenv : Word} {v : PanValue Word}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ}
    (h : CalleeRet E s "rlp_item_header" [e1, e2] [v] g m ffi)
    (h2 : E.eval s e2 = some (.word lenv)) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ a b c, v = .rStruct [.word a, .word b, c] := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, fuel, n, hrun⟩ := h
  have hq := keepFn_sound (quietKeeper E) hE.functions 3 "rlp_item_header"
    (show keepFn quietLeaf Guest.Software.guestAst 3 "rlp_item_header" = true by decide +kernel)
    parameters body hlookup fuel _ _ n hrun
  have hparams := (fun_of_index 109 hE.functions (by guest_decl_at 109) (by decide +kernel)
    hlookup).2
  obtain ⟨v1, hv1, hrest⟩ : ∃ v1, E.eval s e1 = some v1 ∧ values = [v1, .word lenv] := by
    simp only [evalArgs_cons, evalArgs_nil, h2] at hvalues
    cases he1 : E.eval s e1 with
    | none => rw [he1] at hvalues; simp at hvalues
    | some v1 =>
      rw [he1] at hvalues
      simp at hvalues
      exact ⟨v1, rfl, hvalues.symm⟩
  subst hrest
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := rlp_item_header_spec hE parameters body hlookup fuel
    ⟨cl, s.globals, s.memory, s.ffi⟩ _ n lenv hrun
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
  obtain ⟨a, b, c, hv, -⟩ := headerVals_inv hpost
  simp only [List.cons.injEq, and_true] at hv
  exact ⟨hq.1, hq.2.1, hq.2.2, a, b, c, hv⟩

/-- What a returning `scratch_alloc` leaves, when the arena pointers are in order. -/
theorem scratchalloc_ret (hE : GuestEnv E) {e : Exp Word} {pv fv nv : Word} {v : PanValue Word}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ}
    (h : CalleeRet E s "scratch_alloc" [e] [v] g m ffi) (he : E.eval s e = some (.word nv))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat) :
    m = s.memory ∧ ffi = s.ffi ∧ ∃ qv : Word, v = .word qv ∧
      g = updatePanValueMap s.globals "scratch_ptr" (.word qv) ∧
      fv.toNat ≤ qv.toNat ∧ qv.toNat + nv.toNat ≤ pv.toNat ∧ qv.toNat % 8 = 0 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 13 hE.functions (by guest_decl_at 13) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, he, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := scratch_alloc_runs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _
    pv fv nv (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hp hf
    hfp hrun
  obtain ⟨hm, hf', qv, hv, hg, h1, h2, h3⟩ := hpost
  simp only [List.cons.injEq, and_true] at hv
  exact ⟨hm, hf', qv, hv, hg, h1, h2, h3⟩

end InitECandidate.Solver.GuestBound
