import InitECandidate.Solver.GuestBound.SepTrap

/-!
# Calling trap-exempt callees; address ranges

The call rules of `SepCall.lean` / `SepPop.lean` for callees specified with
`WPFt`: the caller's postcondition must hold of every trap, and then only
returned results and raised exceptions other than `TrapErr` are left.

`Assn.Range a b` owns every address in `[a, b)`. An arena's free space is a
range, and an allocation splits it (`Assn.range_split`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- `var x = f(args); rest` for a callee with a trap-exempt framed specification. -/
theorem WPr.decCall_framedT {x : VarName} {sh : Shape} {f : FunName} {args : List (Exp Word)}
    {body : Prog Word} {P F : Assn} {Qc : Result σ → Assn} (hpre : (P ⋆ F).holds s)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody P Qc)
    (htrap : ∀ r, Trap r → Q r)
    (hret : ∀ l g m ffi v, (Qc (.returned l g m ffi [v]) ⋆ F).holds
        (⟨updatePanValueMap s.locals x v, g, m, ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x v, g, m, ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r')))
    (hraise : ∀ l g m ffi exc v, exc ≠ "TrapErr" → (Qc (.raised l g m ffi exc v) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.raised (fun _ => none) g m ffi exc v)) :
    WPr E s (.decCall x sh f args body) Q := by
  refine WPr.decCall_spec (fun rb => Trap rb ∨ (Qc rb ⋆ F).holds rb.st)
    (fun parameters cbody values cl hlk hvalues hbind =>
      hc parameters cbody values cl hlk hvalues hbind F (Assn.holds_congr rfl rfl hpre))
    ?_ ?_ ?_
  · rintro l g m ffi v (ht | hC)
    · exact ht.elim
    · exact hret l g m ffi v (Assn.holds_congr rfl rfl hC)
  · rintro l g m ffi exc v (ht | hC)
    · exact htrap _ ht
    · by_cases he : exc = "TrapErr"
      · exact htrap _ he
      · exact hraise l g m ffi exc v he (Assn.holds_congr rfl rfl hC)
  · intro l g m ffi ev _
    exact htrap _ trivial

/-- `f(args)` with no destination, for a callee with a trap-exempt framed specification. -/
theorem WPr.call_framedT {f : FunName} {args : List (Exp Word)} {P F : Assn}
    {Qc : Result σ → Assn} (hpre : (P ⋆ F).holds s)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody P Qc)
    (htrap : ∀ r, Trap r → Q r)
    (hret : ∀ l g m ffi vs, (Qc (.returned l g m ffi vs) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.normal s.locals g m ffi))
    (hraise : ∀ l g m ffi exc v, exc ≠ "TrapErr" → (Qc (.raised l g m ffi exc v) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.raised (fun _ => none) g m ffi exc v)) :
    WPr E s (.call (some (none, none)) f args) Q := by
  refine WPr.call_spec (fun rb => Trap rb ∨ (Qc rb ⋆ F).holds rb.st)
    (fun parameters cbody values cl hlk hvalues hbind =>
      hc parameters cbody values cl hlk hvalues hbind F (Assn.holds_congr rfl rfl hpre))
    ?_ ?_ ?_
  · rintro l g m ffi vs (ht | hC)
    · exact ht.elim
    · exact hret l g m ffi vs (Assn.holds_congr rfl rfl hC)
  · rintro l g m ffi exc v (ht | hC)
    · exact htrap _ ht
    · by_cases he : exc = "TrapErr"
      · exact htrap _ he
      · exact hraise l g m ffi exc v he (Assn.holds_congr rfl rfl hC)
  · intro l g m ffi ev _
    exact htrap _ trivial

/-- `f(args); rest` for a callee with a trap-exempt framed specification. -/
theorem WPr.seq_call_framedT {f : FunName} {args : List (Exp Word)} {q : Prog Word}
    {P F : Assn} {Qc : Result σ → Assn} (hpre : (P ⋆ F).holds s)
    (hc : ∀ parameters cbody values cl,
      lookupPanFunction f E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody P Qc)
    (htrap : ∀ r, Trap r → Q r)
    (hret : ∀ l g m ffi vs, (Qc (.returned l g m ffi vs) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → WPr E ⟨s.locals, g, m, ffi⟩ q Q)
    (hraise : ∀ l g m ffi exc v, exc ≠ "TrapErr" → (Qc (.raised l g m ffi exc v) ⋆ F).holds
      (⟨s.locals, g, m, ffi⟩ : St σ) → Q (.raised (fun _ => none) g m ffi exc v)) :
    WPr E s (.seq (.call (some (none, none)) f args) q) Q := by
  refine WPr.seq (fun s' => ∃ l g m ffi vs, s' = ⟨s.locals, g, m, ffi⟩ ∧
      (Qc (.returned l g m ffi vs) ⋆ F).holds s')
    (WPr.call_framedT hpre hc ?_ (fun l g m ffi vs h => ⟨l, g, m, ffi, vs, rfl, h⟩) hraise) ?_
  · intro r hr
    cases r <;> first | exact htrap _ hr | exact hr.elim
  · rintro _ ⟨l, g, m, ffi, vs, rfl, h⟩
    exact hret l g m ffi vs h

/-- `scratch_alloc(e)` at a call site where the argument evaluates to `n`. -/
theorem scratch_alloc_hc (hE : GuestEnv E) {args : List (Exp Word)} {nv : Word}
    (hargs : E.evalArgs s args = some [.word nv]) (pv fv : Word) (hfp : fv.toNat ≤ pv.toNat) :
    ∀ parameters cbody values cl,
      lookupPanFunction "scratch_alloc" E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (ArenaPtrs pv fv)
        (fun r => Assn.ex fun qv : Word =>
          ⌜(fv.toNat ≤ qv.toNat ∧ qv.toNat + nv.toNat ≤ pv.toNat ∧ qv.toNat % 8 = 0) ∧
            ∃ l g m, r = .returned l g m s.ffi [.word qv]⌝ ⋆ ArenaPtrs qv fv) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 13 hE.functions (by guest_decl_at 13) (by decide +kernel)
    hlk).2
  rw [hargs] at hvalues
  cases hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact scratch_alloc_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ pv fv nv
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hfp

/-- Every address in `[a, b)` is owned, with unknown content. -/
def Assn.Range (a b : Word) : Assn :=
  Assn.Owns (fun k => ∃ x : Word, k = .mem x ∧ a.toNat ≤ x.toNat ∧ x.toNat < b.toNat)

/-- A range splits at any point inside it. -/
theorem Assn.range_split {a q b : Word} (h1 : a.toNat ≤ q.toNat) (h2 : q.toNat ≤ b.toNat) :
    Assn.Range a b = (Assn.Range a q ⋆ Assn.Range q b) := by
  refine Assn.owns_split (fun k => ?_) (fun k => ?_)
  · constructor
    · rintro ⟨x, rfl, hx1, hx2⟩
      by_cases hq : x.toNat < q.toNat
      · exact Or.inl ⟨x, rfl, hx1, hq⟩
      · exact Or.inr ⟨x, rfl, by omega, hx2⟩
    · rintro (⟨x, rfl, hx1, hx2⟩ | ⟨x, rfl, hx1, hx2⟩)
      · exact ⟨x, rfl, hx1, by omega⟩
      · exact ⟨x, rfl, by omega, hx2⟩
  · rintro ⟨x, rfl, -, hx2⟩ ⟨y, hy, hy1, -⟩
    cases hy
    omega

/-- A store at an address inside an owned range. -/
theorem Step.range {a b addr : Word} {w : PanValue Word} (h1 : a.toNat ≤ addr.toNat)
    (h2 : addr.toNat < b.toNat) : Step (.mem addr) w (Assn.Range a b) (Assn.Range a b) :=
  Step.owns ⟨addr, rfl, h1, h2⟩

end InitECandidate.Solver.GuestBound
