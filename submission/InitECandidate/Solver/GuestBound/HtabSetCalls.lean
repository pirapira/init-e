import InitECandidate.Solver.GuestBound.HtabInternal
import InitECandidate.Solver.GuestBound.HtabPath
import InitECandidate.Solver.GuestBound.HtabSetInv
import InitECandidate.Solver.GuestBound.ScratchAlloc

/-!
# Hash tables: the calls made by `htab_set`
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem memeq_quiet : keepFn quietLeaf Guest.Software.guestAst 1 "memeq" = true := by
  decide +kernel

/-- `var x = memeq(e1, e2, e3)`: it changes nothing, and answers 1 on equal bytes. -/
theorem WPs.decCall_memeq_any (hE : GuestEnv E) {x : VarName} {body : Prog Word}
    {e1 e2 e3 : Exp Word} {A B nW : Word} (h1 : E.eval s e1 = some (.word A))
    (h2 : E.eval s e2 = some (.word B)) (h3 : E.eval s e3 = some (.word nW))
    (hA : A.toNat + nW.toNat < 2 ^ 64) (hB : B.toNat + nW.toNat < 2 ^ 64)
    (hn : nW.toNat < 2 ^ 63)
    (h : ∀ e : Word,
      ((∀ k, k < nW.toNat → byteAt s.memory (off A k) = byteAt s.memory (off B k)) → e = 1#64) →
      WPs E ⟨updatePanValueMap s.locals x (.word e), s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "memeq" [e1, e2, e3] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 18 hE.functions (by guest_decl_at 18) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hq := keepFn_sound (quietKeeper E) hE.functions 1 "memeq" memeq_quiet parameters
    cbody hlookup
  obtain ⟨fuel, nb, hrunb⟩ := id hcallee
  have hkeep := hq fuel _ rb nb hrunb
  cases rb with
  | returned lr g m f vs =>
    obtain ⟨hg, hm, hf⟩ := hkeep
    have hg' : g = s.globals := hg
    have hm' : m = s.memory := hm
    have hf' : f = s.ffi := hf
    subst hg' hm' hf'
    cases vs with
    | nil => exact hout.elim
    | cons value tl =>
      cases tl with
      | cons _ _ => exact hout.elim
      | nil =>
        obtain ⟨r', hshape, hrun', rfl⟩ := hout
        obtain ⟨e, rfl⟩ := word_of_shape_one hshape
        have he1 : (∀ k, k < nW.toNat → byteAt s.memory (off A k) = byteAt s.memory (off B k)) →
            e = 1#64 := by
          intro hb
          rcases memeq_eq hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ A B nW
            (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
            (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
            (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
            ⟨hA, hB, hn, hb⟩ hcallee with hst | ⟨l, heq⟩
          · exact absurd hst (fun h => h)
          · cases heq
            rfl
        rcases h e he1 r' hrun' with hs | hq
        · exact Or.inl hs.restore
        · exact Or.inr hq
  | raised lr g m f ex v =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | finalFfi lr g m f ev =>
    simp only at hout
    subst hout
    exact Or.inl trivial
  | _ => exact hout.elim

/-- `var x = htab_find_leaf(t, key)` for an arbitrary key. -/
theorem WPs.decCall_findpath (hE : GuestEnv E) {x : VarName} {body : Prog Word} {t kp : Word}
    {v : HtabV} {kind : Nat → NodeKind} {rep : KeyRep} {κ : Word → Bool}
    (ht : s.locals "t" = some (.word t)) (hkp : s.locals "key" = some (.word kp))
    (hwf : HtabWF s.memory t v kind) (hk : HtabKeys s.memory v kind rep)
    (hkey : ∀ j : Word, j.toNat < (v.kl * 8#64).toNat → KeyBitIs 8#64 s.memory kp j (κ j))
    (h : ∀ nv, PathR s.memory v kind rep κ nv →
      WPs E ⟨updatePanValueMap s.locals x (.word nv), s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "htab_find_leaf" [.var .local "t", .var .local "key"] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 131 hE.functions (by guest_decl_at 131) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ht, hkp, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := htab_find_path_runs hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩
    rb t v kind rep kp κ (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hwf hk
    (by rw [hE.bytes]; exact hkey) hcallee
  rcases hpost with hst | ⟨l, nv, rfl, hres⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f => exact hout.elim
    | _ => exact absurd hst (fun h => h)
  · obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h nv hres r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

/-- `var x = htab_first_diff(e1, e2, e3)`. -/
theorem WPs.decCall_firstdiff (hE : GuestEnv E) {x : VarName} {body : Prog Word}
    {e1 e2 e3 : Exp Word} {A B nW : Word} (h1 : E.eval s e1 = some (.word A))
    (h2 : E.eval s e2 = some (.word B)) (h3 : E.eval s e3 = some (.word nW))
    (P : FdPre A B nW)
    (h : ∀ d, FdPost s.memory A B nW.toNat d →
      WPs E ⟨updatePanValueMap s.locals x (.word d), s.globals, s.memory, s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "htab_first_diff" [e1, e2, e3] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 130 hE.functions (by guest_decl_at 130) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, h3, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := htab_first_diff_runs hE parameters cbody hlookup
    ⟨cl, s.globals, s.memory, s.ffi⟩ rb A B nW
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) P hcallee
  rcases hpost with hst | ⟨l, d, rfl, hres⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f => exact hout.elim
    | _ => exact absurd hst (fun h => h)
  · obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h d hres r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

/-- What `htab_new_leaf` leaves behind. -/
def NewLeafPost (m : Word → Option (PanValue Word)) (t keyp pv : Word) (v : HtabV)
    (kind : Nat → NodeKind) (rep : KeyRep) (det : Nat → Prop)
    (g' : VarName → Option (PanValue Word)) (m' : Word → Option (PanValue Word)) (n : Word)
    (v' : HtabV) (kind' : Nat → NodeKind) : Prop :=
  HtabOKd m' t v' kind' (fun i => if i = n.toNat then srcBit m keyp else rep i)
      (fun i => i = n.toNat ∨ det i) ∧
    v'.kl = v.kl ∧ v'.st = v.st ∧ v'.cnt = v.cnt + 1#64 ∧ v'.root = v.root ∧ 1 ≤ n.toNat ∧
    n.toNat < v'.next.toNat ∧ kind' n.toNat = .leaf ∧
    (∀ i, i < v.next.toNat → i ≠ n.toNat → kind' i = kind i) ∧
    v.next.toNat ≤ v'.next.toNat ∧ (kind n.toNat = .free ∨ n.toNat = v.next.toNat) ∧
    (∀ (i o : Nat) (w : Word), i ≤ v.nc.toNat → i ≠ n.toNat → o < 32 → o % 8 = 0 →
      (Rd m' (nodeField v' i o) w ↔ Rd m (nodeField v i o) w)) ∧
    (∃ pv' : Word, g' "heap_ptr" = some (.word pv') ∧ InHeap pv' ∧
      v'.order.toNat + (v'.nc.toNat + 1) * 8 ≤ pv'.toNat ∧ pv.toNat ≤ pv'.toNat) ∧
    ∀ A : Word, (A.toNat + 8 ≤ t.toNat ∨ t.toNat + 88 ≤ A.toNat) →
      (A.toNat + 8 ≤ pv.toNat ∨ 2952790016 ≤ A.toNat) →
      (A.toNat + 8 ≤ v.keys.toNat ∨ v.order.toNat + (v.nc.toNat + 1) * 8 ≤ A.toNat) →
      m' A = m A

/-- `var x = htab_new_leaf(t, key, value)`. -/
theorem WPs.decCall_newleaf (hE : GuestEnv E) {x : VarName} {body : Prog Word}
    {t keyp val pv : Word} {v : HtabV} {kind : Nat → NodeKind} {rep : KeyRep} {det : Nat → Prop}
    (ht : s.locals "t" = some (.word t)) (hk : s.locals "key" = some (.word keyp))
    (hv : s.locals "value" = some (.word val)) (hok : HtabOKd s.memory t v kind rep det)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (ht8 : t.toNat % 8 = 0)
    (hk64 : keyp.toNat + v.kl.toNat < 2 ^ 64)
    (hkT : keyp.toNat + v.kl.toNat ≤ t.toNat ∨ t.toNat + 88 ≤ keyp.toNat)
    (hkB : keyp.toNat + v.kl.toNat ≤ v.keys.toNat ∨
      v.order.toNat + (v.nc.toNat + 1) * 8 ≤ keyp.toNat)
    (hkP : keyp.toNat + v.kl.toNat ≤ pv.toNat ∨ 2952790016 ≤ keyp.toNat)
    (h : ∀ g' m' n v' kind', NewLeafPost s.memory t keyp pv v kind rep det g' m' n v' kind' →
      WPs E ⟨updatePanValueMap s.locals x (.word n), g', m', s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "htab_new_leaf"
      [.var .local "t", .var .local "key", .var .local "value"] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 135 hE.functions (by guest_decl_at 135) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ht, hk, hv, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := htab_new_leaf_exec hE parameters cbody hlookup ⟨cl, s.globals, s.memory, s.ffi⟩
    rb t keyp val pv v kind rep det
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hok hp hpH hend ht8 hk64 hkT hkB hkP hcallee
  rcases hpost with hst | ⟨l, g', m', n, v', kind', rfl, hres⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f => exact hout.elim
    | _ => exact absurd hst (fun h => h)
  · obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h g' m' n v' kind' hres r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

/-- What `htab_new_internal` leaves behind. -/
def NewIntPost (m : Word → Option (PanValue Word)) (t bit pv : Word) (v : HtabV)
    (kind : Nat → NodeKind) (rep : KeyRep) (det : Nat → Prop)
    (g' : VarName → Option (PanValue Word)) (m' : Word → Option (PanValue Word)) (n : Word)
    (v' : HtabV) (kind' : Nat → NodeKind) : Prop :=
  HtabOKd m' t v' kind' rep (fun i => i = n.toNat ∨ det i) ∧
    v'.kl = v.kl ∧ v'.st = v.st ∧ v'.cnt = v.cnt ∧ v'.root = v.root ∧ 1 ≤ n.toNat ∧
    n.toNat < v'.next.toNat ∧ kind' n.toNat = .internal ∧
    (∀ i, i < v.next.toNat → i ≠ n.toNat → kind' i = kind i) ∧
    v.next.toNat ≤ v'.next.toNat ∧ (kind n.toNat = .free ∨ n.toNat = v.next.toNat) ∧
    Rd m' (nodeField v' n.toNat 24) bit ∧
    (∀ (i o : Nat) (w : Word), i ≤ v.nc.toNat → i ≠ n.toNat → o < 32 → o % 8 = 0 →
      (Rd m' (nodeField v' i o) w ↔ Rd m (nodeField v i o) w)) ∧
    (∃ pv' : Word, g' "heap_ptr" = some (.word pv') ∧ InHeap pv' ∧
      v'.order.toNat + (v'.nc.toNat + 1) * 8 ≤ pv'.toNat ∧ pv.toNat ≤ pv'.toNat) ∧
    ∀ A : Word, (A.toNat + 8 ≤ t.toNat ∨ t.toNat + 88 ≤ A.toNat) →
      (A.toNat + 8 ≤ pv.toNat ∨ 2952790016 ≤ A.toNat) →
      (A.toNat + 8 ≤ v.keys.toNat ∨ v.order.toNat + (v.nc.toNat + 1) * 8 ≤ A.toNat) →
      m' A = m A

/-- `var x = htab_new_internal(t, e)`. -/
theorem WPs.decCall_newinternal (hE : GuestEnv E) {x : VarName} {body : Prog Word}
    {e2 : Exp Word} {t bit pv : Word} {v : HtabV} {kind : Nat → NodeKind} {rep : KeyRep}
    {det : Nat → Prop} (ht : s.locals "t" = some (.word t))
    (h2 : E.eval s e2 = some (.word bit)) (hok : HtabOKd s.memory t v kind rep det)
    (hp : s.globals "heap_ptr" = some (.word pv)) (hpH : InHeap pv)
    (hend : v.order.toNat + (v.nc.toNat + 1) * 8 ≤ pv.toNat) (hbit : bit ≠ v.kl * 8#64)
    (h : ∀ g' m' n v' kind', NewIntPost s.memory t bit pv v kind rep det g' m' n v' kind' →
      WPs E ⟨updatePanValueMap s.locals x (.word n), g', m', s.ffi⟩ body
        (fun r' => Q (restorePanValueFfiLocal x (s.locals x) r'))) :
    WPs E s (.decCall x .one "htab_new_internal" [.var .local "t", e2] body) Q := by
  intro r hr
  rcases runs_decCall_inv hr with herr | ⟨parameters, cbody, values, cl, rb, hlookup, hvalues,
    hbind, hcallee, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 136 hE.functions (by guest_decl_at 136) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ht, h2, Option.map_some,
    Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have hpost := htab_new_internal_exec hE parameters cbody hlookup
    ⟨cl, s.globals, s.memory, s.ffi⟩ rb t bit pv v kind rep det
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    hok hp hpH hend hbit hcallee
  rcases hpost with hst | ⟨l, g', m', n, v', kind', rfl, hres⟩
  · cases rb with
    | raised lr g m f ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f => exact hout.elim
    | _ => exact absurd hst (fun h => h)
  · obtain ⟨r', -, hrun', rfl⟩ := hout
    rcases h g' m' n v' kind' hres r' hrun' with hs | hq
    · exact Or.inl hs.restore
    · exact Or.inr hq

end InitECandidate.Solver.GuestBound
