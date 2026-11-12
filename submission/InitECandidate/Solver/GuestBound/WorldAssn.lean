import InitECandidate.Solver.GuestBound.WorldRestore
import InitECandidate.Solver.GuestBound.SepWorld
import InitECandidate.Solver.GuestBound.SepFinish

/-!
# The world state as an owned assertion

`WorldA Rg` owns the heap `[HBASE - 7, HEAP_END)` and the globals `heap_ptr`,
`journal`, `journal_cap`, `journal_n`, with the invariant `WorldTJ Rg` (tables,
journal, trie nodes; the tables in `D` are live). `restore_spec`: `state_restore` keeps `WorldA` and whatever is
framed around it, which is the `RestoreSpec` hypothesis of
`run_frames_bound_world`.

More heap structures (tries, account data, per-transaction tables) are added
by strengthening `WorldTJ` and the list of owned globals; `Local` must then
be re-proved for the stronger predicate.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The tables only depend on aligned heap cells below the heap pointer. -/
theorem TabsOK.frame {m m' : Word → Option (PanValue Word)} {pv : Word}
    {T : Word → Option HtabV} (h : TabsOK m pv T)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → HBASE ≤ a.toNat → a.toNat < pv.toNat → m' a = m a) :
    TabsOK m' pv T := by
  refine ⟨fun t v ht => ?_, h.disj⟩
  have hat := h.at_ t v ht
  obtain ⟨kind, rep, hok⟩ := hat.ok
  exact ⟨⟨kind, rep, hok.frame hat.t8 (fun a ha => hm a ha.1 (hat.foot_lt ha).1
    (hat.foot_lt ha).2)⟩, hat.t8, hat.lo, hat.fin⟩

/-- The journal only depends on aligned heap cells below the heap pointer. -/
theorem JournalOK.frame {m m' : Word → Option (PanValue Word)} {pv : Word}
    {T : Word → Option HtabV} {J C n : Word} (h : JournalOK m pv T J C n)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → HBASE ≤ a.toNat → a.toNat < pv.toNat → m' a = m a) :
    JournalOK m' pv T J C n := by
  have hJhi := h.hi
  have hal := h.al
  have hlo := h.lo
  have hC := h.n_le
  have hpvlt := pv.isLt
  refine ⟨h.n_le, h.al, h.lo, h.hi, h.off, fun i hi => ?_⟩
  obtain ⟨t0, kc, fl, val, v0, r0, r1, r2, r3, hT0, hkf⟩ := h.entry i hi
  have hbase : (J + BitVec.ofNat 64 (32 * i)).toNat = J.toNat + 32 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have keep : ∀ (c : Nat) (a : Word), a.toNat = J.toNat + 32 * i + c → c % 8 = 0 → c < 32 →
      ∀ w, Rd m a w → Rd m' a w := by
    intro c a ha hc8 hc w hr
    unfold Rd at hr ⊢
    rw [hm a (by omega) (by omega) (by omega)]
    exact hr
  have b1 : (J + BitVec.ofNat 64 (32 * i) + 8#64).toNat = J.toNat + 32 * i + 8 := by
    rw [BitVec.toNat_add, hbase]
    simp
    omega
  have b2 : (J + BitVec.ofNat 64 (32 * i) + 16#64).toNat = J.toNat + 32 * i + 16 := by
    rw [BitVec.toNat_add, hbase]
    simp
    omega
  have b3 : (J + BitVec.ofNat 64 (32 * i) + 24#64).toNat = J.toNat + 32 * i + 24 := by
    rw [BitVec.toNat_add, hbase]
    simp
    omega
  exact ⟨t0, kc, fl, val, v0, keep 0 _ (by rw [hbase]; omega) (by omega) (by omega) _ r0,
    keep 8 _ b1 (by omega) (by omega) _ r1, keep 16 _ b2 (by omega) (by omega) _ r2,
    keep 24 _ b3 (by omega) (by omega) _ r3, hT0, hkf⟩

/-- Tables, journal and nodes only depend on aligned heap cells below the heap pointer. -/
theorem HeapW.frame {m m' : Word → Option (PanValue Word)} {pv : Word}
    {T : Word → Option HtabV} {N : Word → Option Word} {J C n : Word}
    (h : HeapW m pv T N J C n)
    (hm : ∀ a : Word, a.toNat % 8 = 0 → HBASE ≤ a.toNat → a.toNat < pv.toNat → m' a = m a) :
    HeapW m' pv T N J C n := by
  refine ⟨h.pvH, h.tabs.frame hm, h.jrn.frame hm, h.nodes.frame (Nat.le_refl _)
    (fun a k x hN hx => ?_), h.tn, h.jn⟩
  have hat := h.nodes.at_ a k hN
  have hin := hx.inside hat
  have := hat.lo
  have := hat.hi
  exact hm x (hx.aligned hat) (by omega) (by omega)

/-- The globals the world state owns. -/
def worldGlobals : List VarName := ["heap_ptr", "journal", "journal_cap", "journal_n"]

/-- The keys the world state owns: the heap and its globals. -/
def HeapKeys : Key → Prop
  | .mem a => HBASE < a.toNat + 8 ∧ a.toNat < 2952790016
  | .glob x => x ∈ worldGlobals

/-- The world invariant on a view. -/
def WorldP (Rg : Reg) (V : View) : Prop :=
  WorldTJ Rg (fun x => V (.glob x)) (fun a => V (.mem a))

theorem worldP_local (Rg : Reg) : Local HeapKeys (WorldP Rg) := by
  rintro V V' hV ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hW, hD, hB, hCn, hNd⟩
  have hg : ∀ x, x ∈ worldGlobals → V' (.glob x) = V (.glob x) := fun x hx => hV (.glob x) hx
  have hm : ∀ a : Word, a.toNat % 8 = 0 → HBASE ≤ a.toNat → a.toNat < pv.toNat →
      V' (.mem a) = V (.mem a) := by
    intro a _ h1 h2
    have := hpH.1
    exact hV (.mem a) ⟨by omega, by omega⟩
  refine ⟨pv, T, N, J, C, n, (hg _ (by simp [worldGlobals])).trans hp, hpH,
    (hg _ (by simp [worldGlobals])).trans hJg, (hg _ (by simp [worldGlobals])).trans hCg,
    (hg _ (by simp [worldGlobals])).trans hng, hW.frame hm, hD, hB, fun x w h => ?_, hNd⟩
  obtain ⟨hr, h8, hi, hhi, hf⟩ := hCn x w h
  refine ⟨?_, h8, hi, hhi, hf⟩
  show V' (.mem x) = _
  rw [hm x h8 hf.lo_ (by have := hf.hi_; omega)]
  exact hr

/-- The world state: owns the heap and its globals, with tables and journal well formed. -/
def WorldA (Rg : Reg) : Assn := Assn.Region HeapKeys (WorldP Rg)

theorem state_restore_raises (hE : GuestEnv E) :
    FunRaises E (fun x => x == "TrapErr") "state_restore" :=
  raiseFn_sound _ hE.functions 8 "state_restore"
    (show raiseFn (fun x => x == "TrapErr") Guest.Software.guestAst 8 "state_restore" = true by
      decide +kernel)

/-- `state_restore` keeps the world assertion and its frame. -/
theorem restore_spec (hE : GuestEnv E) (Rg : Reg) : RestoreSpec E (WorldA Rg) := by
  intro parameters body hlookup s R hh r hr
  have hW : WorldTJ Rg s.globals s.memory := Assn.region_elim hh
  rcases state_restore_raises hE parameters body hlookup s r hr with he | hra
  · exact Or.inl he
  rcases state_restore_world hE parameters body hlookup Rg s r hW hr with hst | ⟨l, g', m', rfl, hW',
    hg, hm⟩
  · cases r with
    | error l g m f => exact Or.inl rfl
    | raised l g m f e v =>
      have he : e = "TrapErr" := by simpa [RaiseIn] using hra
      exact Or.inr (Or.inl he)
    | finalFfi l g m f ev => exact Or.inr (Or.inl trivial)
    | _ => exact absurd hst (fun h => h)
  · refine Or.inr (Or.inr ⟨l, g', m', rfl, ?_⟩)
    refine Assn.region_change (s' := (⟨l, g', m', s.ffi⟩ : St σ)) hh (worldP_local Rg)
      (fun k hk => ?_)
      hW'
    cases k with
    | mem a =>
      show m' a = s.memory a
      refine hm a ?_
      by_contra hc
      exact hk ⟨by omega, by omega⟩
    | glob x =>
      show g' x = s.globals x
      refine hg x ?_ ?_
      · rintro rfl
        exact hk (show "heap_ptr" ∈ worldGlobals by simp [worldGlobals])
      · rintro rfl
        exact hk (show "journal_n" ∈ worldGlobals by simp [worldGlobals])

end InitECandidate.Solver.GuestBound
