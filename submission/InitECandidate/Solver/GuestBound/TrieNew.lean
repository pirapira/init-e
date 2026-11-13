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
def Reg.addNd (Rg : Reg) (a k : Word) (ℓ ℓc : Nat) : Reg :=
  { Rg with
    Nd := fun x => Rg.Nd x ∨ x = a
    Kd := fun x j => Rg.Kd x j ∨ (x = a ∧ j = k)
    Lv := fun x j => Rg.Lv x j ∨ (x = a ∧ j = ℓ)
    Cv := fun x j => Rg.Cv x j ∨ (x = a ∧ j = ℓc) }

/-- `ImOK` after a node is added at the heap pointer: the new node's segment
(if it is a leaf or an extension) must be empty or a nibble array of an
immutable block. -/
theorem ImOK.node_add {Rg : Reg} {m m' : Word → Option (PanValue Word)} {pv pv' a k : Word}
    {T : Word → Option HtabV} {N : Word → Option Word} {J C n : Word} {ℓ ℓc : Nat}
    (h : ImOK Rg m pv T N J C) (hW : HeapW m pv T N J C n)
    (hfr : ∀ x : Word, x.toNat % 8 = 0 → x.toNat < pv.toNat → m' x = m x)
    (hlo : pv.toNat ≤ a.toNat) (hpv : pv.toNat ≤ pv'.toNat)
    (hseg : (k = 1#64 ∨ k = 2#64) → ∃ sp nl : Word, Rd m' (a + 32#64) sp ∧
      Rd m' (a + 40#64) nl ∧ (nl = 0#64 ∨ ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ sp.toNat ∧
        sp.toNat + nl.toNat ≤ hi.toNat ∧ NibSeg m sp nl))
    (hx : k = 2#64 → (∀ nl, Rd m' (a + 40#64) nl → ℓc = ℓ + nl.toNat) ∧
      ∀ c, Rd m' (a + 48#64) c → c ≠ 0#64 → Rg.Lv c ℓc)
    (hb : k = 3#64 → ℓc = ℓ + 1 ∧
      ∀ i c, i < 16 → Rd m' (a + BitVec.ofNat 64 (32 + 8 * i)) c → c ≠ 0#64 → Rg.Lv c ℓc) :
    ImOK (Rg.addNd a k ℓ ℓc) m' pv' T (addN N a k) J C := by
  classical
  have hold_ne : ∀ b j, N b = some j → b ≠ a := by
    intro b j hN e
    have hbi := (hW.nodes.at_ b j hN).hi
    have hsz := nodeSize_pos j
    rw [e] at hbi
    omega
  have rdold : ∀ b j y w, N b = some j → StructCell b j y → Rd m' y w → Rd m y w := by
    intro b j y w hN hsy hr
    have hat := hW.nodes.at_ b j hN
    have hin := hsy.inside hat
    have := hat.hi
    unfold Rd at hr ⊢
    rw [← hfr y (hsy.al hat) (by omega)]
    exact hr
  have hold : SegsOK Rg.Im m' N := h.segs.frame (fun x hx => by
    obtain ⟨b1, b2, b3⟩ := h.cell_bounds hW (Or.inl hx)
    exact hfr x b1 b3)
  refine ⟨fun lo hi hI => ⟨(h.free lo hi hI).1, (h.free lo hi hI).2.node_add hlo hpv⟩,
    h.offB, fun b j hb hj => ?_, fun lo hi hI => by
      have := hi.isLt
      have hf := (h.free lo hi hI).2.hi_
      exact (h.nib lo hi hI).frame (lo := lo) (h.free lo hi hI).1 (Nat.le_refl _) (by omega)
        (fun x hx8 _ h2 => hfr x hx8 (by omega)), fun b j hK => ?_, fun b j hK => ?_,
      fun b j hb => ?_,
      fun u hu => ⟨(h.trf u hu).1, by
        obtain ⟨hi, e, hf⟩ := (h.trf u hu).2
        exact ⟨hi, e, hf.node_add hlo hpv⟩⟩,
      fun u hu => by
        obtain ⟨root, sec, r1, r2, hc⟩ := h.trv u hu
        obtain ⟨c8, c1, c2, hi, e, hf⟩ := tr_cell_in h hu (x := u) (Or.inl rfl)
        obtain ⟨d8, d1, d2, -⟩ := tr_cell_in h hu (x := u + 8#64) (Or.inr rfl)
        have := hf.hi_
        refine ⟨root, sec, ?_, ?_, hc.1.addN a k, fun h0 => Or.inl (hc.2 h0)⟩
        · unfold Rd at r1 ⊢
          rw [hfr u c8 (by omega)]
          exact r1
        · unfold Rd at r2 ⊢
          rw [hfr _ d8 (by omega)]
          exact r2,
      h.offT, h.offC, h.offI, h.offTT, fun b ℓb hL => ?_, fun b ℓ1 ℓ2 h1 h2 => ?_, ?_, ?_,
      fun b ℓb hL => ?_, fun b ℓ1 ℓ2 h1 h2 => ?_, ?_, ?_, ?_,
      fun b sp nl hS => by
        obtain ⟨⟨j, hj, hj12⟩, r1, r2⟩ := h.sg b sp nl hS
        have hat := hW.nodes.at_ b j hj
        have i1 := seg_cell_in hat hj12 (x := b + 32#64) (Or.inl rfl)
        have i2 := seg_cell_in hat hj12 (x := b + 40#64) (Or.inr rfl)
        have := hat.hi
        refine ⟨⟨j, by unfold addN; rw [if_neg (hold_ne b j hj)]; exact hj, hj12⟩, ?_, ?_⟩
        · unfold Rd at r1 ⊢
          rw [hfr _ i1.1 (by omega)]
          exact r1
        · unfold Rd at r2 ⊢
          rw [hfr _ i2.1 (by omega)]
          exact r2⟩
  rotate_left
  · rcases hK with hK | ⟨rfl, rfl⟩
    · have hN := h.kd b j hK
      have hbi := (hW.nodes.at_ b j hN).hi
      have hsz := nodeSize_pos j
      unfold addN
      rw [if_neg (fun e => by rw [e] at hbi; omega)]
      exact hN
    · simp [addN]
  · rcases hK with hK | ⟨rfl, rfl⟩
    · exact Or.inl (h.kn b j hK)
    · exact Or.inr rfl
  · unfold addN at hb
    by_cases e : b = a
    · subst e
      simp only [if_true, Option.some.injEq] at hb
      exact Or.inr ⟨rfl, hb.symm⟩
    · simp only [if_neg e] at hb
      exact Or.inl (h.full b j hb)
  · rcases hL with hL | ⟨rfl, rfl⟩
    · obtain ⟨j, hj⟩ := h.lvk b ℓb hL
      exact ⟨j, by unfold addN; rw [if_neg (hold_ne b j hj)]; exact hj⟩
    · exact ⟨k, by simp [addN]⟩
  · rcases h1 with h1 | ⟨rfl, rfl⟩
    · rcases h2 with h2 | ⟨rfl, rfl⟩
      · exact h.lvu b ℓ1 ℓ2 h1 h2
      · obtain ⟨j, hj⟩ := h.lvk _ ℓ1 h1
        exact absurd rfl (hold_ne _ j hj)
    · rcases h2 with h2 | ⟨-, rfl⟩
      · obtain ⟨j, hj⟩ := h.lvk _ ℓ2 h2
        exact absurd rfl (hold_ne _ j hj)
      · rfl
  · intro b ℓcb c hNb hcv r2 hc
    rcases hcv with hcv | ⟨rfl, rfl⟩
    · obtain ⟨j, hj⟩ := h.cvk b ℓcb hcv
      have hN2 : N b = some 2#64 := by
        unfold addN at hNb
        rw [if_neg (hold_ne b j hj)] at hNb
        exact hNb
      exact Or.inl (h.lvx b ℓcb c hN2 hcv
        (rdold b _ _ _ hN2 (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)) r2) hc)
    · have hk2 : k = 2#64 := by
        simp [addN] at hNb
        exact hNb
      exact Or.inl ((hx hk2).2 c r2 hc)
  · intro b ℓcb i c hNb hcv hi r1 hc
    rcases hcv with hcv | ⟨rfl, rfl⟩
    · obtain ⟨j, hj⟩ := h.cvk b ℓcb hcv
      have hN3 : N b = some 3#64 := by
        unfold addN at hNb
        rw [if_neg (hold_ne b j hj)] at hNb
        exact hNb
      exact Or.inl (h.lvb b ℓcb i c hN3 hcv hi
        (rdold b _ _ _ hN3 (Or.inr (Or.inr ⟨rfl, i, hi, rfl⟩)) r1) hc)
    · have hk3 : k = 3#64 := by
        simp [addN] at hNb
        exact hNb
      exact Or.inl ((hb hk3).2 i c hi r1 hc)
  · rcases hL with hL | ⟨rfl, rfl⟩
    · obtain ⟨j, hj⟩ := h.cvk b ℓb hL
      exact ⟨j, by unfold addN; rw [if_neg (hold_ne b j hj)]; exact hj⟩
    · exact ⟨k, by simp [addN]⟩
  · rcases h1 with h1 | ⟨rfl, rfl⟩
    · rcases h2 with h2 | ⟨rfl, rfl⟩
      · exact h.cvu b ℓ1 ℓ2 h1 h2
      · obtain ⟨j, hj⟩ := h.cvk _ ℓ1 h1
        exact absurd rfl (hold_ne _ j hj)
    · rcases h2 with h2 | ⟨-, rfl⟩
      · obtain ⟨j, hj⟩ := h.cvk _ ℓ2 h2
        exact absurd rfl (hold_ne _ j hj)
      · rfl
  · intro b ℓb ℓcb nl hl hcv hNb r1
    rcases hl with hl | ⟨rfl, rfl⟩
    · obtain ⟨j, hj⟩ := h.lvk b ℓb hl
      have hne := hold_ne b j hj
      rcases hcv with hcv | ⟨rfl, -⟩
      · have hN2 : N b = some 2#64 := by
          unfold addN at hNb
          rw [if_neg hne] at hNb
          exact hNb
        exact h.cvx b ℓb ℓcb nl hl hcv hN2
          (rdold b _ _ _ hN2 (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)) r1)
      · exact absurd rfl hne
    · rcases hcv with hcv | ⟨-, rfl⟩
      · obtain ⟨j, hj⟩ := h.cvk _ ℓcb hcv
        exact absurd rfl (hold_ne _ j hj)
      · have hk2 : k = 2#64 := by
          simp [addN] at hNb
          exact hNb
        exact (hx hk2).1 nl r1
  · intro b ℓb ℓcb hl hcv hNb
    rcases hl with hl | ⟨rfl, rfl⟩
    · obtain ⟨j, hj⟩ := h.lvk b ℓb hl
      have hne := hold_ne b j hj
      rcases hcv with hcv | ⟨rfl, -⟩
      · have hN3 : N b = some 3#64 := by
          unfold addN at hNb
          rw [if_neg hne] at hNb
          exact hNb
        exact h.cvb b ℓb ℓcb hl hcv hN3
      · exact absurd rfl hne
    · rcases hcv with hcv | ⟨-, rfl⟩
      · obtain ⟨j, hj⟩ := h.cvk _ ℓcb hcv
        exact absurd rfl (hold_ne _ j hj)
      · have hk3 : k = 3#64 := by
          simp [addN] at hNb
          exact hNb
        exact (hb hk3).1
  · intro b ℓb j hl hNb hj
    rcases hl with hl | ⟨rfl, rfl⟩
    · obtain ⟨j', hj'⟩ := h.lvk b ℓb hl
      have hNj : N b = some j := by
        unfold addN at hNb
        rw [if_neg (hold_ne b j' hj')] at hNb
        exact hNb
      obtain ⟨ℓc', hc'⟩ := h.lvc b ℓb j hl hNj hj
      exact ⟨ℓc', Or.inl hc'⟩
    · exact ⟨ℓc, Or.inr ⟨rfl, rfl⟩⟩
  unfold addN at hb
  by_cases e : b = a
  · subst e
    simp only [if_true, Option.some.injEq] at hb
    subst hb
    obtain ⟨sp, nl, r1, r2, hc⟩ := hseg hj
    refine ⟨sp, nl, r1, r2, ?_⟩
    rcases hc with h0 | ⟨lo, hi, hI, h1, h2, hn⟩
    · exact Or.inl h0
    · obtain ⟨hlo8, hf⟩ := h.free lo hi hI
      have := hf.hi_
      exact Or.inr ⟨lo, hi, hI, hlo8, h1, h2, hn.frame hlo8 h1 h2
        (fun x hx8 _ hx2 => hfr x hx8 (by omega))⟩
  · simp only [if_neg e] at hb
    exact hold b j hb hj

set_option maxHeartbeats 4000000 in
theorem node_new_ext_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "node_new_ext" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (nib nlen child : Word)
    (hnib : s.locals "nib" = some (.word nib)) (hnl : s.locals "nlen" = some (.word nlen))
    (hcl : s.locals "child" = some (.word child)) (hlen : 1 ≤ nlen.toNat)
    (hch : child = 0#64 ∨ Rg.Nd child) (hW : WorldTJ Rg s.globals s.memory)
    (hseg : ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ nib.toNat ∧ nib.toNat + nlen.toNat ≤ hi.toNat ∧
      NibSeg s.memory nib nlen)
    (ℓ : Nat) (hchl : child ≠ 0#64 → Rg.Lv child (ℓ + nlen.toNat))
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
      WorldTJ (Rg.addNd a 2#64 ℓ (ℓ + nlen.toNat)) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 257 hE.functions (by guest_decl_at 257) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
    WorldTJ (Rg.addNd a 2#64 ℓ (ℓ + nlen.toNat)) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, hBT, hCT, hNT, hIT⟩ := hW
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
  have h32 : Rd m' (pv + 32#64) nib := by
    rw [← hm']
    exact ((Rd.here _ (pv + 32#64) nib).frame _ (NE (by omega))).frame _ (NE (by omega))
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
    fun a ha => ?_, hIT.node_add hHW (fun x _ hlt => keep x (by omega)) (Nat.le_refl _) hpq
      (fun _ => ⟨nib, nlen, h32, h40, Or.inr hseg⟩)
      (fun _ => ⟨fun nl r1 => by rw [Rd.inj r1 h40], fun c r2 hc0 => by
        have e2 : c = child := Rd.inj r2 h48
        subst e2
        exact hchl hc0⟩)
      (fun hk => absurd hk (by decide))⟩, fun x hx => by simp [update_lookup, hx],
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

set_option maxHeartbeats 4000000 in
theorem node_new_leaf_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "node_new_leaf" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (nib nlen vptr vlen : Word)
    (hnib : s.locals "nib" = some (.word nib)) (hnl : s.locals "nlen" = some (.word nlen))
    (hvp : s.locals "vptr" = some (.word vptr)) (hvl : s.locals "vlen" = some (.word vlen))
    (hW : WorldTJ Rg s.globals s.memory)
    (hseg : nlen = 0#64 ∨ ∃ lo hi, Rg.Im lo hi ∧ lo.toNat ≤ nib.toNat ∧ nib.toNat + nlen.toNat ≤ hi.toNat ∧
      NibSeg s.memory nib nlen)
    (ℓ : Nat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
      WorldTJ (Rg.addNd a 1#64 ℓ ℓ) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
      ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
        m' addr = s.memory addr := by
  have hbody := (fun_of_index 256 hE.functions (by guest_decl_at 256) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l g' m' a, r = .returned l g' m' s.ffi [.word a] ∧
    WorldTJ (Rg.addNd a 1#64 ℓ ℓ) g' m' ∧ (∀ x, x ≠ "heap_ptr" → g' x = s.globals x) ∧
    ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m' addr = s.memory addr)) r h
  obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hDT, hBT, hCT, hNT, hIT⟩ := hW
  have hpE := hpH.1
  have hp8 := hpH.2
  have hJlo := hHW.jrn.lo
  have hJhi := hHW.jrn.hi
  refine WPs.decCall_alloc hE (pv := pv) (nv := 64#64) (eval_const _ _) hp hpH
    (fun qv hq hqH => ?_)
  have hq' : pv.toNat + 64 ≤ qv.toNat := hq
  have hqE := hqH.1
  refine WPs.seq_store hE (addr := pv + 0#64) (w := 1#64) (eval_addc hE 0#64 (by lk []))
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
  refine WPs.seq_store hE (addr := pv + 48#64) (w := vptr) (eval_addc hE 48#64 (by lk []))
    (of_eval (by lk [hvp])) ?_
  refine WPs.seq_store hE (addr := pv + 56#64) (w := vlen) (eval_addc hE 56#64 (by lk []))
    (of_eval (by lk [hvl])) ?_
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
  have a56 : (pv + 56#64).toNat = pv.toNat + 56 := by bv_omega
  rw [a0]
  generalize hm' : setCell (setCell (setCell (setCell (setCell (setCell (setCell (setCell s.memory pv 1#64)
    (pv + 8#64) 0#64) (pv + 16#64) 0#64) (pv + 24#64) 0#64) (pv + 32#64) nib) (pv + 40#64) nlen)
    (pv + 48#64) vptr) (pv + 56#64) vlen = m'
  have keep : ∀ a : Word, ¬ (pv.toNat ≤ a.toNat ∧ a.toNat < pv.toNat + 64) →
      m' a = s.memory a := by
    intro a ha
    rw [← hm', setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)),
      setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega)), setCell_ne _ (NE (by omega))]
  have hkind : Rd m' pv 1#64 := by
    rw [← hm']
    exact (((((((Rd.here s.memory pv 1#64).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))).frame _ (NE (by omega))).frame _ (NE (by omega))
  have h40 : Rd m' (pv + 40#64) nlen := by
    rw [← hm']
    exact ((Rd.here _ (pv + 40#64) nlen).frame _ (NE (by omega))).frame _ (NE (by omega))
  have h32 : Rd m' (pv + 32#64) nib := by
    rw [← hm']
    exact (((Rd.here _ (pv + 32#64) nib).frame _ (NE (by omega))).frame _ (NE (by omega))).frame _
      (NE (by omega))
  have hpq : pv.toNat ≤ qv.toNat := by omega
  have hbase : HBASE ≤ pv.toNat := by omega
  have hW' : HeapW m' qv T (addN N pv 1#64) J C n :=
    hHW.node_add (fun x _ hlt => keep x (by omega))
      (fun x hx => keep x (by unfold HBASE at hx hbase; omega)) hp8 (Nat.le_refl _)
      (by show pv.toNat + nodeSize 1#64 ≤ qv.toNat; simp [nodeSize]; omega) hqE (by decide)
      hkind (fun hk => absurd hk (by decide))
      (fun hk => absurd hk (by decide))
  refine ⟨_, _, m', pv, rfl, ⟨qv, T, addN N pv 1#64, J, C, n, by simp [updatePanValueMap], hqH,
    by simp (config := { decide := true }) [update_lookup, hJg],
    by simp (config := { decide := true }) [update_lookup, hCg],
    by simp (config := { decide := true }) [update_lookup, hng], hW', hDT,
    fun lo hi hb => (hBT lo hi hb).node_add (Nat.le_refl _) hpq, fun x w hc => ?_,
    fun a ha => ?_, hIT.node_add hHW (fun x _ hlt => keep x (by omega)) (Nat.le_refl _) hpq
      (fun _ => ⟨nib, nlen, h32, h40, hseg⟩) (fun hk => absurd hk (by decide))
      (fun hk => absurd hk (by decide))⟩, fun x hx => by simp [update_lookup, hx],
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
      · exact ⟨1#64, by simp [e]⟩
      · exact ⟨k, by simp [e, hk]⟩
    · exact ⟨1#64, by simp⟩


end InitECandidate.Solver.GuestBound
