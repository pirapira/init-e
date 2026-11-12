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

/-- What `htab_grow` did to memory: three block copies and five header stores. -/
structure GrowRel (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV)
    (pv N O q : Word) (mF : Word → Option (PanValue Word)) : Prop where
  hN : pv.toNat + (v.nc.toNat * 2 + 1) * v.st.toNat ≤ N.toNat
  inN : InHeap N
  hO : N.toNat + (v.nc.toNat * 2 + 1) * 32 ≤ O.toNat
  inO : InHeap O
  hq : O.toNat + (v.nc.toNat * 2 + 1) * 8 ≤ q.toNat
  inq : InHeap q
  mem : ∃ m1 m2 m3, CopyInv m pv v.keys ((v.nc.toNat + 1) * v.st.toNat) m1 ∧
    CopyInv (setCell m1 (t + 32#64) pv) N v.nodes ((v.nc.toNat + 1) * 32) m2 ∧
    CopyInv (setCell m2 (t + 40#64) N) O v.order ((v.nc.toNat + 1) * 8) m3 ∧
    mF = setCell (setCell (setCell m3 (t + 48#64) O) (t + 16#64) (v.cp * 2#64)) (t + 80#64)
      (v.nc * 2#64)

set_option maxHeartbeats 4000000 in
/-- `htab_grow(t)` on a well-formed table that lies below the heap pointer. -/
theorem htab_grow_exec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_grow" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (t pv : Word) (v : HtabV) (kind : Nat → NodeKind)
    (ht : s.locals "t" = some (.word t)) (hwf : HtabWF s.memory t v kind)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l N O q mF, r = .returned l
        (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word N))
          "heap_ptr" (.word O)) "heap_ptr" (.word q)) mF s.ffi [.word 0#64] ∧
      GrowRel s.memory t v pv N O q mF := by
  have hbody := (fun_of_index 137 hE.functions (by guest_decl_at 137) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l N O q mF, r = .returned l
      (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals "heap_ptr" (.word N))
        "heap_ptr" (.word O)) "heap_ptr" (.word q)) mF s.ffi [.word 0#64] ∧
      GrowRel s.memory t v pv N O q mF)) r h
  have hlay := hwf.layout
  obtain ⟨l1, l2, l3, l4⟩ := id hlay
  obtain ⟨hkl, hst, hcp, hcnt, hkeys, hnd, hord, hroot, hnext, hfree, hnc⟩ := hwf.hdr
  obtain ⟨hple, hp8⟩ := id hpH
  -- sizes
  have h1 : (1#64 : Word).toNat = 1 := by decide
  have h2 : (2#64 : Word).toNat = 2 := by decide
  have h32 : (32#64 : Word).toNat = 32 := by decide
  have h8 : (8#64 : Word).toNat = 8 := by decide
  have hncs : v.nc.toNat < 2 ^ 27 := by omega
  have hbig : (v.nc.toNat * 2 + 1) * v.st.toNat ≤ 2 * ((v.nc.toNat + 1) * v.st.toNat) := by
    calc (v.nc.toNat * 2 + 1) * v.st.toNat ≤ (v.nc.toNat * 2 + 2) * v.st.toNat :=
          Nat.mul_le_mul_right _ (by omega)
      _ = 2 * ((v.nc.toNat + 1) * v.st.toNat) := by ring
  have hnc2 : (v.nc * 2#64).toNat = v.nc.toNat * 2 := by
    rw [BitVec.toNat_mul, h2]
    exact Nat.mod_eq_of_lt (by omega)
  have hnc21 : (v.nc * 2#64 + 1#64).toNat = v.nc.toNat * 2 + 1 := by
    rw [BitVec.toNat_add, hnc2, h1]
    exact Nat.mod_eq_of_lt (by omega)
  have hnc1 : (v.nc + 1#64).toNat = v.nc.toNat + 1 := by
    rw [BitVec.toNat_add, h1]
    exact Nat.mod_eq_of_lt (by omega)
  have hsK : ((v.nc * 2#64 + 1#64) * v.st).toNat = (v.nc.toNat * 2 + 1) * v.st.toNat := by
    rw [BitVec.toNat_mul, hnc21]
    exact Nat.mod_eq_of_lt (by omega)
  have hcK : ((v.nc + 1#64) * v.st).toNat = (v.nc.toNat + 1) * v.st.toNat := by
    rw [BitVec.toNat_mul, hnc1]
    exact Nat.mod_eq_of_lt (by omega)
  have hsN : ((v.nc * 2#64 + 1#64) * 32#64).toNat = (v.nc.toNat * 2 + 1) * 32 := by
    rw [BitVec.toNat_mul, hnc21, h32]
    exact Nat.mod_eq_of_lt (by omega)
  have hcN : ((v.nc + 1#64) * 32#64).toNat = (v.nc.toNat + 1) * 32 := by
    rw [BitVec.toNat_mul, hnc1, h32]
    exact Nat.mod_eq_of_lt (by omega)
  have hsO : ((v.nc * 2#64 + 1#64) * 8#64).toNat = (v.nc.toNat * 2 + 1) * 8 := by
    rw [BitVec.toNat_mul, hnc21, h8]
    exact Nat.mod_eq_of_lt (by omega)
  have hcO : ((v.nc + 1#64) * 8#64).toNat = (v.nc.toNat + 1) * 8 := by
    rw [BitVec.toNat_mul, hnc1, h8]
    exact Nat.mod_eq_of_lt (by omega)
  -- header cells lie below the heap pointer
  have hb : ∀ k, k ≤ 80 → (t + BitVec.ofNat 64 k).toNat + 8 ≤ pv.toNat := by
    intro k hk
    rw [hdr_toNat hlay (by omega)]
    omega
  have hne : ∀ k k', k < 88 → k' < 88 → k ≠ k' →
      t + BitVec.ofNat 64 k ≠ t + BitVec.ofNat 64 k' :=
    fun k k' hk hk' hkk h => hkk ((hdr_eq_hdr hlay hk hk').mp h)
  refine WPs.dec (eval_load_rd hE (eval_addc hE 80#64 ht) hnc) ?_
  refine WPs.dec (w := v.nc * 2#64) (of_eval (by ev [evalPanOp])) ?_
  refine WPs.dec (eval_load_rd hE (eval_addc hE (a := t) 8#64 (by lk [ht])) hst) ?_
  refine WPs.decCall_alloc hE (pv := pv) (nv := (v.nc * 2#64 + 1#64) * v.st)
    (by ev [evalPanOp]) hp hpH ?_
  intro N hN hNin
  rw [hsK] at hN
  refine WPs.seq_mem (fun m' => CopyInv s.memory pv v.keys ((v.nc.toNat + 1) * v.st.toNat) m')
    (WPs.call_memcpy hE (dst := pv) (src := v.keys) (nW := (v.nc + 1#64) * v.st) (by lk [])
      (eval_load_rd hE (eval_addc hE (a := t) 32#64 (by lk [ht])) hkeys) (by ev [evalPanOp])
      ⟨by rw [hcK]; omega, by rw [hcK]; omega, Or.inl (by rw [hcK]; omega), by rw [hcK]; omega⟩
      (fun m' hc => ⟨m', rfl, by rw [hcK] at hc; exact hc⟩)) ?_
  intro m1 c1
  have F1 : ∀ A : Word, A.toNat + 8 ≤ pv.toNat → m1 A = s.memory A :=
    fun A hA => c1.cells A (Or.inl hA)
  refine WPs.seq_store hE (eval_addc hE (a := t) 32#64 (by lk [ht]))
    (of_eval (w := pv) (by lk [])) ?_
  refine WPs.decCall_alloc hE (pv := N) (nv := (v.nc * 2#64 + 1#64) * 32#64)
    (by ev [evalPanOp]) (by simp [update_lookup]) hNin ?_
  intro O hO hOin
  rw [hsN] at hO
  have hRdN : Rd (setCell m1 (t + 32#64) pv) (t + 40#64) v.nodes := by
    unfold Rd
    rw [setCell_ne' _ (hne 40 32 (by omega) (by omega) (by omega)), F1 _ (hb 40 (by omega))]
    exact hnd
  refine WPs.seq_mem (fun m' => CopyInv (setCell m1 (t + 32#64) pv) N v.nodes
      ((v.nc.toNat + 1) * 32) m')
    (WPs.call_memcpy hE (dst := N) (src := v.nodes) (nW := (v.nc + 1#64) * 32#64) (by lk [])
      (eval_load_rd hE (eval_addc hE (a := t) 40#64 (by lk [ht])) hRdN) (by ev [evalPanOp])
      ⟨by rw [hcN]; have := hOin.1; omega, by rw [hcN]; omega, Or.inl (by rw [hcN]; omega),
        by rw [hcN]; omega⟩
      (fun m' hc => ⟨m', rfl, by rw [hcN] at hc; exact hc⟩)) ?_
  intro m2 c2
  have F2 : ∀ A : Word, A.toNat + 8 ≤ N.toNat → m2 A = setCell m1 (t + 32#64) pv A :=
    fun A hA => c2.cells A (Or.inl hA)
  refine WPs.seq_store hE (eval_addc hE (a := t) 40#64 (by lk [ht]))
    (of_eval (w := N) (by lk [])) ?_
  refine WPs.decCall_alloc hE (pv := O) (nv := (v.nc * 2#64 + 1#64) * 8#64)
    (by ev [evalPanOp]) (by simp [update_lookup]) hOin ?_
  intro q hq hqin
  rw [hsO] at hq
  have hRdO : Rd (setCell m2 (t + 40#64) N) (t + 48#64) v.order := by
    unfold Rd
    rw [setCell_ne' _ (hne 48 40 (by omega) (by omega) (by omega)),
      F2 _ (by have := hb 48 (by omega); omega),
      setCell_ne' _ (hne 48 32 (by omega) (by omega) (by omega)), F1 _ (hb 48 (by omega))]
    exact hord
  refine WPs.seq_mem (fun m' => CopyInv (setCell m2 (t + 40#64) N) O v.order
      ((v.nc.toNat + 1) * 8) m')
    (WPs.call_memcpy hE (dst := O) (src := v.order) (nW := (v.nc + 1#64) * 8#64) (by lk [])
      (eval_load_rd hE (eval_addc hE (a := t) 48#64 (by lk [ht])) hRdO) (by ev [evalPanOp])
      ⟨by rw [hcO]; have := hqin.1; omega, by rw [hcO]; omega, Or.inl (by rw [hcO]; omega),
        by rw [hcO]; omega⟩
      (fun m' hc => ⟨m', rfl, by rw [hcO] at hc; exact hc⟩)) ?_
  intro m3 c3
  have F3 : ∀ A : Word, A.toNat + 8 ≤ O.toNat → m3 A = setCell m2 (t + 40#64) N A :=
    fun A hA => c3.cells A (Or.inl hA)
  refine WPs.seq_store hE (eval_addc hE (a := t) 48#64 (by lk [ht]))
    (of_eval (w := O) (by lk [])) ?_
  have hRdC : Rd (setCell m3 (t + 48#64) O) (t + 16#64) v.cp := by
    unfold Rd
    rw [setCell_ne' _ (hne 16 48 (by omega) (by omega) (by omega)),
      F3 _ (by have := hb 16 (by omega); omega),
      setCell_ne' _ (hne 16 40 (by omega) (by omega) (by omega)),
      F2 _ (by have := hb 16 (by omega); omega),
      setCell_ne' _ (hne 16 32 (by omega) (by omega) (by omega)), F1 _ (hb 16 (by omega))]
    exact hcp
  refine WPs.seq_store hE (w := v.cp * 2#64) (eval_addc hE (a := t) 16#64 (by lk [ht])) ?_ ?_
  · intro y hy
    obtain ⟨va, vb, hva, hvb, rfl⟩ := eval_mul_inv hy
    have := eval_load_rd hE (eval_addc hE (a := t) 16#64 (by lk [ht])) hRdC _ hva
    simp only [PanValue.word.injEq] at this
    subst this
    simp only [eval_const, Option.some.injEq, PanValue.word.injEq] at hvb
    subst hvb
    rfl
  refine WPs.seq_store hE (eval_addc hE (a := t) 80#64 (by lk [ht]))
    (of_eval (w := v.nc * 2#64) (by lk [])) ?_
  refine WPs.ret (of_eval (eval_const _ _)) ?_
  exact ⟨_, N, O, q, _, rfl, hN, hNin, hO, hOin, hq, hqin, m1, m2, m3, c1, c2, c3, rfl⟩

end InitECandidate.Solver.GuestBound
