import InitECandidate.Solver.GuestBound.WorldJset

/-!
# Building a trie node keeps the world

`node_new_ext(nib, nlen, child)` with a non-empty segment and a child that is
null or a known node: the result is a new known node, the world invariant is
kept (`HeapW.node_add`), only `heap_ptr` changes among the globals and no
memory outside the heap changes. The other constructors (`node_new_leaf`,
`node_new_hashed`, `node_new_branch`) follow the same proof.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The registry with one more known node. -/
def Reg.addNd (Rg : Reg) (a : Word) : Reg := { Rg with Nd := fun x => Rg.Nd x ∨ x = a }

set_option maxHeartbeats 4000000 in
theorem node_new_ext_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "node_new_ext" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (nib nlen child : Word)
    (hnib : s.locals "nib" = some (.word nib)) (hnl : s.locals "nlen" = some (.word nlen))
    (hcl : s.locals "child" = some (.word child)) (hlen : 1 ≤ nlen.toNat)
    (hch : child = 0#64 ∨ Rg.Nd child) (hW : WorldTJ Rg s.globals s.memory)
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
      WorldTJ (Rg.addNd a) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 257 hE.functions (by guest_decl_at 257) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
    WorldTJ (Rg.addNd a) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, hBT, hCT, hNT⟩ := hW
  have hpE := hpH.1
  have hp8 := hpH.2
  have hJlo := hHW.jrn.lo
  have hJhi := hHW.jrn.hi
  refine WPs.decCall_alloc hE (pv := pv) (nv := 56#64) (eval_const _ _) hp hpH
    (fun qv hq hqH => ?_)
  have hq' : pv.toNat + 56 ≤ qv.toNat := hq
  have hqE := hqH.1
  refine WPs.seq_store hE (addr := pv + 0#64) (w := 2#64) (eval_addc hE 0#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := pv + 8#64) (w := 0#64) (eval_addc hE 8#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := pv + 16#64) (w := 0#64) (eval_addc hE 16#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := pv + 24#64) (w := 0#64) (eval_addc hE 24#64 (by lk []))
    (of_eval (eval_const _ _)) ?_
  refine WPs.seq_store hE (addr := pv + 32#64) (w := nib) (eval_addc hE 32#64 (by lk []))
    (of_eval (by lk [hnib])) ?_
  refine WPs.seq_store hE (addr := pv + 40#64) (w := nlen) (eval_addc hE 40#64 (by lk []))
    (of_eval (by lk [hnl])) ?_
  refine WPs.seq_store hE (addr := pv + 48#64) (w := child) (eval_addc hE 48#64 (by lk []))
    (of_eval (by lk [hcl])) ?_
  refine WPs.ret (w := pv) (of_eval (by lk [])) ?_
  simp only [restorePanValueFfiLocal]
  have NE : ∀ {a b : Word}, a.toNat ≠ b.toNat → a ≠ b := fun h e => h (congrArg _ e)
  have a0 : (pv + 0#64) = pv := by simp
  have a8 : (pv + 8#64).toNat = pv.toNat + 8 := by bv_omega
  have a16 : (pv + 16#64).toNat = pv.toNat + 16 := by bv_omega
  have a24 : (pv + 24#64).toNat = pv.toNat + 24 := by bv_omega
  have a32 : (pv + 32#64).toNat = pv.toNat + 32 := by bv_omega
  have a40 : (pv + 40#64).toNat = pv.toNat + 40 := by bv_omega
  have a48 : (pv + 48#64).toNat = pv.toNat + 48 := by bv_omega
  rw [a0]
  generalize hm' : setCell (setCell (setCell (setCell (setCell (setCell (setCell s.memory pv 2#64)
    (pv + 8#64) 0#64) (pv + 16#64) 0#64) (pv + 24#64) 0#64) (pv + 32#64) nib) (pv + 40#64) nlen)
    (pv + 48#64) child = m'
  have keep : ∀ a : Word, ¬ (pv.toNat ≤ a.toNat ∧ a.toNat < pv.toNat + 56) →
      m' a = s.memory a := by
    intro a ha
    rw [← hm', setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
  have hkind : Rd m' pv 2#64 := by
    rw [← hm']
    exact ((((((Rd.here s.memory pv 2#64).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))
  have h40 : Rd m' (pv + 40#64) nlen := by
    rw [← hm']
    exact (Rd.here _ (pv + 40#64) nlen).frame _ (NE (by omega))
  have h48 : Rd m' (pv + 48#64) child := by
    rw [← hm']
    exact Rd.here _ (pv + 48#64) child
  have hchN : IsChild N child := by
    rcases hch with rfl | hc
    · exact Or.inl rfl
    · exact Or.inr (hNT child hc)
  have hpq : pv.toNat ≤ qv.toNat := by omega
  have hbase : HBASE ≤ pv.toNat := by omega
  have hW' : HeapW m' qv T (addN N pv 2#64) J C n :=
    hHW.node_add (fun x _ hlt => keep x (by omega))
      (fun x hx => keep x (by unfold HBASE at hx hbase; omega)) hp8 (Nat.le_refl _)
      (by show pv.toNat + nodeSize 2#64 ≤ qv.toNat; simp [nodeSize]; omega) hqE (by decide)
      hkind (fun _ => ⟨nlen, child, h40, hlen, h48, hchN⟩)
      (fun hk => absurd hk (by decide))
  refine ⟨_, _, m', pv, rfl, ⟨qv, T, addN N pv 2#64, J, C, n, by simp [updatePanValueMap], hqH,
    by simp (config := { decide := true }) [update_lookup, hJg],
    by simp (config := { decide := true }) [update_lookup, hCg],
    by simp (config := { decide := true }) [update_lookup, hng], hW', hDT,
    fun lo hi hb => (hBT lo hi hb).node_add (Nat.le_refl _) hpq, fun x w hc => ?_,
    fun a ha => ?_⟩, fun x hx => by simp [update_lookup, hx],
    fun addr ha => keep addr (by unfold HBASE at ha hbase; omega)⟩
  · obtain ⟨hr, h8, hi, hhi, hf⟩ := hCT x w hc
    refine ⟨?_, h8, hi, hhi, hf.node_add (Nat.le_refl _) hpq⟩
    have := hf.hi_
    unfold Rd at hr ⊢
    rw [keep x (by omega)]
    exact hr
  · classical
    unfold InitECandidate.Solver.GuestBound.addN
    rcases ha with ha | rfl
    · obtain ⟨k, hk⟩ := hNT a ha
      by_cases e : a = pv
      · exact ⟨2#64, by simp [e]⟩
      · exact ⟨k, by simp [e, hk]⟩
    · exact ⟨2#64, by simp⟩

end InitECandidate.Solver.GuestBound
