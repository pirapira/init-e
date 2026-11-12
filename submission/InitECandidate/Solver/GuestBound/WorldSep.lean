import InitECandidate.Solver.GuestBound.WorldJset
import InitECandidate.Solver.GuestBound.SepCredit

/-!
# Heap buffers under the world assertion

Framed rules for code that allocates a heap buffer and writes into it while
other assertions (a frame) are held next to the world:

* `WPr.decCall_alloc_world` – `var x = alloc(e); rest`: the block is
  registered as free in the registry;
* `WPr.seq_memcpy_world` – `memcpy(dst, src, n); rest` with the destination in
  a registered block.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem alloc_raises (hE : GuestEnv E) : FunRaises E (fun x => x == "TrapErr") "alloc" :=
  raiseFn_sound _ hE.functions 3 "alloc"
    (show raiseFn (fun x => x == "TrapErr") Guest.Software.guestAst 3 "alloc" = true by
      decide +kernel)

/-- The registry with one more free block. -/
def Reg.addB (Rg : Reg) (lo hi : Word) : Reg :=
  { Rg with B := fun a b => Rg.B a b ∨ (a = lo ∧ b = hi) }

set_option maxHeartbeats 1000000 in
/-- `var x = alloc(e); rest` next to the world assertion. -/
theorem WPr.decCall_alloc_world (hE : GuestEnv E) {x : VarName} {e : Exp Word}
    {body : Prog Word} {nv : Word} {Rg : Reg} {F : Assn}
    (he : E.eval s e = some (.word nv)) (h : (WorldA Rg ⋆ F).holds s)
    (htrap : ∀ r, Trap r → Q r)
    (hk : ∀ (pv qv : Word) g, pv.toNat + nv.toNat ≤ qv.toNat → qv.toNat ≤ 2952790016 →
      pv.toNat % 8 = 0 → HBASE ≤ pv.toNat →
      (WorldA (Rg.addB pv qv) ⋆ F).holds
        (⟨updatePanValueMap s.locals x (.word pv), g, s.memory, s.ffi⟩ : St σ) →
      WPr E ⟨updatePanValueMap s.locals x (.word pv), g, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPr E s (.decCall x .one "alloc" [e] body) Q := by
  have hW : WorldTJ Rg s.globals s.memory := Assn.region_elim h
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, hBT, hCT, hNT⟩ := id hW
  have hbase : HBASE ≤ pv.toNat := by
    have := hHW.jrn.lo
    have := hHW.jrn.hi
    omega
  refine WPr.decCall_spec (fun rb => RaiseIn (fun x => x == "TrapErr") rb ∧
      AllocPost pv nv s rb) ?_ ?_ ?_ ?_
  · intro parameters cbody values cl hlk hvalues hbind rb hrun
    rcases alloc_raises hE parameters cbody hlk _ rb hrun with herr | hra
    · exact Or.inl herr
    have hparams := (fun_of_index 7 hE.functions (by guest_decl_at 7) (by decide +kernel)
      hlk).2
    simp only [evalArgs_cons, evalArgs_nil, he, Option.map_some, Option.some.injEq] at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    have hpost := alloc_runs hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ rb pv nv
      (by rw [← hbind]; simp [updatePanValueMap]) hp hpH.1 hrun
    refine Or.inr ⟨hra, ?_⟩
    cases rb <;> exact hpost
  · rintro l g m ffi v ⟨-, hv, hm, hf, qv, hg, h1, h2, h3⟩
    simp only [List.cons.injEq, and_true] at hv
    subst hv hm hf hg
    have hW' := WorldTJ.alloc (g' := updatePanValueMap s.globals "heap_ptr" (.word qv)) hW hp
      (by simp [updatePanValueMap]) ⟨h2, h3⟩ (by omega)
      (fun y hy => by simp [update_lookup, hy])
    refine hk pv qv _ h1 h2 hpH.2 hbase ?_
    refine Assn.region_change h (worldP_local (Rg.addB pv qv)) (fun k hk' => ?_) hW'
    cases k with
    | mem a => rfl
    | glob y =>
      show updatePanValueMap s.globals "heap_ptr" (.word qv) y = s.globals y
      have hy : y ≠ "heap_ptr" := by
        rintro rfl
        exact hk' (show "heap_ptr" ∈ worldGlobals by simp [worldGlobals])
      simp [update_lookup, hy]
  · rintro l g m ffi exc v ⟨hra, -⟩
    have he' : exc = "TrapErr" := by simpa [RaiseIn] using hra
    exact htrap _ he'
  · rintro l g m ffi ev _
    exact htrap _ trivial

set_option maxHeartbeats 1000000 in
/-- `memcpy(dst, src, n); rest` with the destination inside a registered free
block that holds no protected cell. -/
theorem WPr.seq_memcpy_world (hE : GuestEnv E) {e1 e2 e3 : Exp Word} {q : Prog Word}
    {dst nW lo hi : Word} {Rg : Reg} {F : Assn}
    (h1 : ∀ y, E.eval s e1 = some y → y = .word dst)
    (h3 : ∀ y, E.eval s e3 = some y → y = .word nW) (hb : Rg.B lo hi)
    (hlo : HBASE ≤ lo.toNat) (hlo8 : lo.toNat ≤ dst.toNat / 8 * 8)
    (hhi : dst.toNat + nW.toNat ≤ hi.toNat) (hhiE : hi.toNat ≤ 2952790016)
    (hcn : ∀ x w, Rg.Cn x w → ¬ (lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat))
    (h : (WorldA Rg ⋆ F).holds s) (htrap : ∀ r, Trap r → Q r)
    (hq : ∀ m, (WorldA Rg ⋆ F).holds (⟨s.locals, s.globals, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, s.globals, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "memcpy" [e1, e2, e3]) q) Q := by
  have hW : WorldTJ Rg s.globals s.memory := Assn.region_elim h
  refine WPr.seq (fun s' => ∃ m, s' = ⟨s.locals, s.globals, m, s.ffi⟩ ∧
      (WorldA Rg ⋆ F).holds s')
    (WPr.call_spec (fun rb => RaiseIn (fun _ => false) rb ∧ (Stopped rb ∨ ∃ l m',
      rb = .returned l s.globals m' s.ffi [.word 0#64] ∧ Hull s.memory dst nW m')) ?_ ?_ ?_ ?_) ?_
  · intro parameters cbody values cl hlk hvalues hbind r hr
    rcases memcpy_raises hE parameters cbody hlk _ r hr with he | hra
    · exact Or.inl he
    have hparams := (fun_of_index 16 hE.functions (by guest_decl_at 16) (by decide +kernel)
      hlk).2
    obtain ⟨v1, v2, v3, g1, g2, g3, rfl⟩ := evalArgs3_inv hvalues
    have := h1 _ g1
    subst this
    have := h3 _ g3
    subst this
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact Or.inr ⟨hra, memcpy_frame hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ r
      dst nW
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (by omega) hr⟩
  · rintro l g m ffi vs ⟨-, hst | ⟨l', m', heq, hinv⟩⟩
    · exact hst.elim
    injection heq with _ hg hm hf _
    subst hg hm hf
    have hW' : WorldTJ Rg s.globals m :=
      hW.write_free hb (fun a _ hn _ => hinv a (by omega))
        (fun a ha => hinv a (by unfold HBASE at ha hlo; omega)) hcn
    refine ⟨_, rfl, Assn.region_change h (worldP_local Rg) (fun k hk' => ?_) hW'⟩
    cases k with
    | mem a =>
      show m a = s.memory a
      refine hinv a ?_
      have hk'' : ¬ (HBASE < a.toNat + 8 ∧ a.toNat < 2952790016) := hk'
      unfold HBASE at hk'' hlo
      omega
    | glob y => rfl
  · rintro l g m ffi exc v ⟨hra, -⟩
    cases hra
  · intro l g m ffi ev _
    exact htrap _ trivial
  · rintro _ ⟨m, rfl, hm⟩
    exact hq m hm

end InitECandidate.Solver.GuestBound
