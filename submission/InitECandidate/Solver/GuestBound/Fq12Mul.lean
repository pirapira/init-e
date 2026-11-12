import InitECandidate.Solver.GuestBound.Fq12MulAst

/-!
# `fq12_mul` keeps coefficients below `p`

Canonical operands give a canonical product in the destination; besides the
destination only fresh heap above the entry `heap_ptr` is written, and
`heap_ptr` is restored. Part of the canonicity chain for `fq12_inv` (issue #19).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}
  {m m' : Word → Option (PanValue Word)}

theorem CanonN.frame {A : Word} {n : Nat} (h64 : A.toNat + 32 * n ≤ 2 ^ 64)
    (h : ∀ x : Word, A.toNat ≤ x.toNat → x.toNat < A.toNat + 32 * n → m' x = m x)
    (hc : CanonN m A n) : CanonN m' A n := by
  intro i
  obtain ⟨v, hv⟩ := hc i
  refine ⟨v, fun hi => ⟨fe_congr (by rw [coefAddr_toNat (by omega)]; omega) (fun x h1 h2 => ?_)
    (hv hi).1, (hv hi).2⟩⟩
  rw [coefAddr_toNat (by omega)] at h1 h2
  exact h x (by omega) (by omega)

theorem CanonN.poly {A : Word} {n : Nat} (h : CanonN m A n) :
    ∃ c, PolyAt m A c n ∧ ∀ i, i < n → c i < bnP := by
  choose c hc using h
  exact ⟨c, fun i hi => (hc i hi).1, fun i hi => (hc i hi).2⟩

theorem CanonN.of_poly {A : Word} {n : Nat} {c : Nat → Nat} (hp : PolyAt m A c n)
    (hc : ∀ i, i < n → c i < bnP) : CanonN m A n :=
  fun i => ⟨c i, fun hi => ⟨hp i hi, hc i hi⟩⟩

theorem CanonN.mono {A : Word} {n k : Nat} (h : CanonN m A n) (hk : k ≤ n) : CanonN m A k :=
  fun i => (h i).imp (fun _ hv hi => hv (by omega))

section rets

variable {vs : List (PanValue Word)} {g : VarName → Option (PanValue Word)}
  {m : Word → Option (PanValue Word)} {ffi : FfiState σ}

theorem reduce_ret (hE : GuestEnv E) {e : Exp Word} {T : Word}
    (h : CalleeRet E s "fq12_reduce" [e] vs g m ffi) (h1 : E.eval s e = some (.word T))
    (h64 : T.toNat + 736 ≤ 2 ^ 63) (hc : CanonN s.memory T 23) :
    g = s.globals ∧ ffi = s.ffi ∧
      (∀ x : Word, (x.toNat < T.toNat ∨ T.toNat + 736 ≤ x.toNat) → m x = s.memory x) ∧
      CanonN m T 23 := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 658 hE.functions (by guest_decl_at 658) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases fq12_reduce_canon hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ T
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) h64 hc hrun with
    hst | ⟨l', m', heq, hfr, hc'⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, hfr, hc'⟩

theorem release_ret (hE : GuestEnv E) {e : Exp Word} {pv mv : Word}
    (h : CalleeRet E s "heap_release" [e] vs g m ffi) (h1 : E.eval s e = some (.word mv))
    (hp : s.globals "heap_ptr" = some (.word pv)) :
    g = updatePanValueMap s.globals "heap_ptr" (.word mv) ∧ m = s.memory ∧ ffi = s.ffi := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 9 hE.functions (by guest_decl_at 9) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  have := heap_release_runs hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ pv mv
    hp (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hrun
  cases this
  exact ⟨rfl, rfl, rfl⟩

end rets

/-- Invariant of the inner loop of `fq12_mul`, relative to its entry state. -/
def MulInI (a : St σ) (kk ie : Nat) (st : St σ) : Prop :=
  st.globals = a.globals ∧ st.memory = a.memory ∧ st.ffi = a.ffi ∧
    (∀ x, x ≠ "i" → x ≠ "acc" → st.locals x = a.locals x) ∧
    (∃ ii, st.locals "i" = some (.word (BitVec.ofNat 64 ii)) ∧ kk ≤ ii + 11 ∧ ii ≤ ie + 1) ∧
    ∃ c0 c1 c2 c3 : Word, st.locals "acc" = some (.rStruct [.word c0, .word c1, .word c2,
      .word c3]) ∧ limbsVal [c0, c1, c2, c3] < bnP

set_option maxHeartbeats 8000000 in
theorem mul_inner (hE : GuestEnv E) {a : St σ} {A B : Word} {kk ie ii0 : Nat}
    {c0 c1 c2 c3 : Word}
    (hA : a.locals "a" = some (.word A)) (hB : a.locals "b" = some (.word B))
    (hk : a.locals "k" = some (.word (BitVec.ofNat 64 kk)))
    (hie : a.locals "iend" = some (.word (BitVec.ofNat 64 ie)))
    (hi : a.locals "i" = some (.word (BitVec.ofNat 64 ii0)))
    (hacc : a.locals "acc" = some (.rStruct [.word c0, .word c1, .word c2, .word c3]))
    (hcl : limbsVal [c0, c1, c2, c3] < bnP)
    (hkk : kk < 23) (hie11 : ie ≤ 11) (hiek : ie ≤ kk) (h1 : kk ≤ ii0 + 11) (h2 : ii0 ≤ ie + 1)
    (bA : A.toNat + 384 ≤ 2 ^ 63) (bB : B.toNat + 384 ≤ 2 ^ 63)
    (cA : CanonN a.memory A 12) (cB : CanonN a.memory B 12) :
    WPs E a FQM_INNER (fun r => ∃ l, r = .normal l a.globals a.memory a.ffi ∧
      MulInI a kk ie ⟨l, a.globals, a.memory, a.ffi⟩) := by
  have hpp : 0 < bnP := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine WPs.loopG (I := MulInI a kk ie)
    ⟨rfl, rfl, rfl, fun _ _ _ => rfl, ⟨ii0, hi, h1, h2⟩, c0, c1, c2, c3, hacc, hcl⟩ ?_ ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hm, hf, hloc, ⟨ii, hii, k1, k2⟩, d0, d1, d2, d3, hac, hdl⟩
      ⟨w, cc, hcond, hw⟩
    simp only at hg hm hf hloc hii hac
    subst hg hm hf
    have hla : la "a" = some (.word A) := (hloc _ (by decide) (by decide)).trans hA
    have hlb : la "b" = some (.word B) := (hloc _ (by decide) (by decide)).trans hB
    have hlk : la "k" = some (.word (BitVec.ofNat 64 kk)) :=
      (hloc _ (by decide) (by decide)).trans hk
    have hlie : la "iend" = some (.word (BitVec.ofNat 64 ie)) :=
      (hloc _ (by decide) (by decide)).trans hie
    have hcv := eval_cmp_inv hE (op := .notLower) (of_eval (w := BitVec.ofNat 64 ie)
      (by lk [hlie])) (of_eval (w := BitVec.ofNat 64 ii) (by lk [hii])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hile : ii ≤ ie := by
      by_contra hgt
      have hl : (BitVec.ofNat 64 ie : Word) < BitVec.ofNat 64 ii := by
        rw [BitVec.lt_def, hnat ie (by omega), hnat ii (by omega)]
        omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have hsub : (BitVec.ofNat 64 kk : Word) - BitVec.ofNat 64 ii = BitVec.ofNat 64 (kk - ii) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, hnat kk (by omega), hnat ii (by omega), hnat (kk - ii) (by omega)]
      omega
    obtain ⟨va, hfa, hva⟩ := cA.get (i := ii) (by omega)
    obtain ⟨vb, hfb, hvb⟩ := cB.get (i := kk - ii) (by omega)
    refine WPs.dec_load4 hE (addr := coefAddr A ii)
      (of_eval (by unfold coefAddr; ev [evalPanOp, hla, hii])) hfa (fun a0 a1 a2 a3 hav => ?_)
    refine WPs.dec_load4 hE (addr := coefAddr B (kk - ii))
      (of_eval (by unfold coefAddr; ev [evalPanOp, hlb, hlk, hii, hsub])) hfb
      (fun b0 b1 b2 b3 hbv => ?_)
    refine WPs.decCall_fqmul hE (a0 := a0) (a1 := a1) (a2 := a2) (a3 := a3) (b0 := b0) (b1 := b1)
      (b2 := b2) (b3 := b3) (by lk []) (by lk []) (by rw [hav]; exact hva)
      (by rw [hbv]; exact hvb) (fun p0 p1 p2 p3 hplt _ => ?_)
    refine WPs.seq_callA_ret (fun v g m ffi hret => ?_)
    obtain ⟨hg, hm, hf, e0, e1, e2, e3, hv, he⟩ := fqadd_ret hE hret (a0 := d0) (a1 := d1)
      (a2 := d2) (a3 := d3) (b0 := p0) (b1 := p1) (b2 := p2) (b3 := p3) (by lk [hac]) (by lk [])
      hdl hplt
    simp only [List.cons.injEq, and_true] at hv
    subst g m ffi v
    refine WPs.assign (old := BitVec.ofNat 64 ii) (by lk [hii])
      (of_eval (w := BitVec.ofNat 64 (ii + 1)) (by ev [hii, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, rfl, ?_, ⟨ii + 1, ?_, by omega, by omega⟩, e0, e1, e2, e3, ?_,
      by rw [he]; exact Nat.mod_lt _ hpp⟩
    · intro x hx1 hx2
      refine Eq.trans ?_ (hloc x hx1 hx2)
      show restorePanValueLocal _ _ _ x = la x
      by_cases h3 : x = "p"
      · subst h3
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h4 : x = "bj"
      · subst h4
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h5 : x = "ai"
      · subst h5
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h3, h4, h5, hx1,
        hx2]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hm, hf, rest⟩ -
    simp only at hg hm hf
    subst hg hm hf
    exact ⟨la, rfl, rfl, rfl, rfl, rest⟩

theorem CanonN.snoc {A w0 w1 w2 w3 : Word} {k : Nat} (h64 : A.toNat + 32 * (k + 1) ≤ 2 ^ 64)
    (hc : CanonN m A k) (hv : limbsVal [w0, w1, w2, w3] < bnP) :
    CanonN (InitECandidate.Solver.GuestBound.set4 m (coefAddr A k) w0 w1 w2 w3) A (k + 1) := by
  have hck := coefAddr_toNat (a := A) (i := k) (by omega)
  have hb : (coefAddr A k).toNat + 32 ≤ 2 ^ 64 := by rw [hck]; omega
  intro i
  by_cases hi : i = k
  · subst hi
    exact ⟨_, fun _ => ⟨fe_set4 hb, hv⟩⟩
  · obtain ⟨v, hv'⟩ := hc i
    refine ⟨v, fun hin => ⟨fe_congr (by rw [coefAddr_toNat (by omega)]; omega)
      (fun x h1 h2 => set4_other hb ?_) (hv' (by omega)).1, (hv' (by omega)).2⟩⟩
    rw [coefAddr_toNat (by omega)] at h1 h2
    rw [hck]
    omega

/-- `if c { x = e; } rest` for a local word `x`. -/
theorem WPs.seq_ite_assign {c e : Exp Word} {x : VarName} {rest : Prog Word} {old w wc : Word}
    (hx : s.locals x = some (.word old)) (hc : ∀ y, E.eval s c = some y → y = .word wc)
    (he : wc ≠ 0 → ∀ y, E.eval s e = some y → y = .word w) (h0 : wc = 0 → w = old)
    (h : WPs E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩ rest Q) :
    WPs E s (.seq (.ite c (.assign .local x e) .skip) rest) Q := by
  refine WPs.seq (fun st => st = ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory,
    s.ffi⟩) (WPs.ite hc ?_) (by rintro _ rfl; exact h)
  split
  · rename_i hz
    refine WPs.skip ⟨_, _, _, _, rfl, ?_⟩
    rw [h0 hz, update_same _ _ _ hx]
  · rename_i hz
    exact WPs.assign hx (he hz) ⟨_, _, _, _, rfl, rfl⟩

theorem lower11 {kk : Nat} (hk : kk < 100) :
    evalPanCmp .lower (11#64 : Word) (BitVec.ofNat 64 kk) = if 11 < kk then 1 else 0 := by
  have hn : (BitVec.ofNat 64 kk : Word).toNat = kk := by
    rw [BitVec.toNat_ofNat]
    omega
  have h11 : (11#64 : Word).toNat = 11 := by decide
  by_cases h : 11 < kk
  · have hl : (11#64 : Word) < BitVec.ofNat 64 kk := by rw [BitVec.lt_def, hn, h11]; exact h
    simp [evalPanCmp, hl, h]
  · have hl : ¬ (11#64 : Word) < BitVec.ofNat 64 kk := by rw [BitVec.lt_def, hn, h11]; exact h
    simp [evalPanCmp, hl, h]

/-- Invariant of the outer loop of `fq12_mul`. -/
def MulOutI (L0 G : VarName → Option (PanValue Word)) (F : FfiState σ)
    (m0 : Word → Option (PanValue Word)) (pv : Word) (st : St σ) : Prop :=
  st.globals = G ∧ st.ffi = F ∧ (∀ x, x ≠ "k" → st.locals x = L0 x) ∧
    (∀ x : Word, x.toNat < pv.toNat → st.memory x = m0 x) ∧
    ∃ kk, st.locals "k" = some (.word (BitVec.ofNat 64 kk)) ∧ kk ≤ 23 ∧ CanonN st.memory pv kk

set_option maxHeartbeats 16000000 in
theorem fq12_mul_canon (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq12_mul" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (A B D pv : Word)
    (ha : s.locals "a" = some (.word A)) (hb : s.locals "b" = some (.word B))
    (hd : s.locals "d" = some (.word D)) (hp : s.globals "heap_ptr" = some (.word pv))
    (hpH : InHeap pv) (bA : A.toNat + 384 ≤ pv.toNat) (bB : B.toNat + 384 ≤ pv.toNat)
    (bD : D.toNat + 384 ≤ pv.toNat) (alD : D.toNat % 8 = 0)
    (cA : CanonN s.memory A 12) (cB : CanonN s.memory B 12) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, x.toNat < pv.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
        m' x = s.memory x) ∧ CanonN m' D 12 := by
  have hbody := (fun_of_index 659 hE.functions (by guest_decl_at 659) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  have hpH' := hpH
  unfold InHeap at hpH'
  have h384 : (384#64 : Word).toNat = 384 := by decide
  have hnat : ∀ n : Nat, n < 100 → (BitVec.ofNat 64 n : Word).toNat = n := by
    intro n hn
    rw [BitVec.toNat_ofNat]
    omega
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      (∀ x : Word, x.toNat < pv.toNat → (x.toNat < D.toNat ∨ D.toNat + 384 ≤ x.toNat) →
        m' x = s.memory x) ∧ CanonN m' D 12)) r h
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hg, hm, hf, hv⟩ := heap_mark_ret hE hret hp
  simp only [List.cons.injEq, and_true] at hv
  subst g m ffi v
  refine WPs.decCall_ret (fun v g m ffi hret => ?_)
  obtain ⟨hv, hm, hf, qv, hg, hq1, hq2⟩ := alloc_ret hE hret (nv := 23#64 * 32#64)
    (by ev [evalPanOp]) hp hpH
  simp only [List.cons.injEq, and_true] at hv
  subst v m ffi g
  rw [show (23#64 * 32#64 : Word).toNat = 736 by decide] at hq1
  unfold InHeap at hq2
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  obtain ⟨L0, hL0⟩ : ∃ L0, L0 = updatePanValueMap (updatePanValueMap (updatePanValueMap s.locals
      "mark" (.word pv)) "t" (.word pv)) "k" (.word 0#64) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = updatePanValueMap s.globals "heap_ptr" (.word qv) := ⟨_, rfl⟩
  rw [← hL0, ← hG]
  have La : L0 "a" = some (.word A) := by rw [hL0]; lk [ha]
  have Lb : L0 "b" = some (.word B) := by rw [hL0]; lk [hb]
  have Ld : L0 "d" = some (.word D) := by rw [hL0]; lk [hd]
  have Lt : L0 "t" = some (.word pv) := by rw [hL0]; lk []
  have Lm : L0 "mark" = some (.word pv) := by rw [hL0]; lk []
  have hGs : updatePanValueMap G "heap_ptr" (.word pv) = s.globals := by
    rw [hG]
    funext y
    simp only [update_lookup]
    split
    · rename_i hy
      have : y = "heap_ptr" := by simpa using hy
      rw [this, hp]
    · rfl
  refine WPs.seqG (fun st => MulOutI L0 G s.ffi s.memory pv st ∧ CanonN st.memory pv 23)
    (WPs.loopG (I := MulOutI L0 G s.ffi s.memory pv)
      ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl, 0, by rw [hL0]; lk [], by omega,
        fun i => ⟨0, fun h => absurd h (Nat.not_lt_zero _)⟩⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hloc, hlow, kk, hkk, hk23, hct⟩ ⟨w, cc, hcond, hw⟩
    simp only at hg hf hloc hlow hkk hct
    subst ga fa
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 kk) (by lk [hkk]))
      (of_eval (w := 23#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hklt : kk < 23 := by
      by_contra hge
      have hl : ¬ (BitVec.ofNat 64 kk : Word) < 23#64 := by
        rw [BitVec.lt_def, hnat kk (by omega)]
        have : (23#64 : Word).toNat = 23 := by decide
        omega
      rw [hcv] at hw
      simp [evalPanCmp, hl] at hw
    have lat : la "t" = some (.word pv) := (hloc _ (by decide)).trans Lt
    have laa : la "a" = some (.word A) := (hloc _ (by decide)).trans La
    have lab : la "b" = some (.word B) := (hloc _ (by decide)).trans Lb
    have cAa : CanonN ma A 12 := cA.frame (by omega) (fun x h1 h2 => hlow x (by omega))
    have cBa : CanonN ma B 12 := cB.frame (by omega) (fun x h1 h2 => hlow x (by omega))
    refine WPs.dec_val (v := .rStruct [.word 0#64, .word 0#64, .word 0#64, .word 0#64])
      (by simp [evalF_rStruct, evalArgs_cons, evalArgs_nil]) ?_
    refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
    have hl11 := lower11 (kk := kk) (by omega)
    refine WPs.seq_ite_assign (old := 0#64) (w := BitVec.ofNat 64 (kk - 11))
      (wc := evalPanCmp .lower (11#64 : Word) (BitVec.ofNat 64 kk)) (by lk [])
      (eval_cmp_inv hE (of_eval (eval_const _ _)) (of_eval (by lk [hkk]))) ?_ ?_ ?_
    · intro hne
      have h11 : 11 < kk := by
        by_contra hn
        rw [hl11, if_neg hn] at hne
        exact hne rfl
      have hsub : (BitVec.ofNat 64 kk : Word) - 11#64 = BitVec.ofNat 64 (kk - 11) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_sub, hnat kk (by omega), hnat (kk - 11) (by omega)]
        have : (11#64 : Word).toNat = 11 := by decide
        omega
      exact of_eval (by ev [hkk, hsub])
    · intro h0
      have h11 : ¬ 11 < kk := by
        intro hn
        rw [hl11, if_pos hn] at h0
        exact absurd h0 (by decide)
      have : kk - 11 = 0 := by omega
      rw [this]
    refine WPs.dec (w := BitVec.ofNat 64 kk) (of_eval (by lk [hkk])) ?_
    refine WPs.seq_ite_assign (old := BitVec.ofNat 64 kk) (w := BitVec.ofNat 64 (min kk 11))
      (wc := evalPanCmp .lower (11#64 : Word) (BitVec.ofNat 64 kk)) (by lk [])
      (eval_cmp_inv hE (of_eval (eval_const _ _)) (of_eval (by lk []))) ?_ ?_ ?_
    · intro hne
      have h11 : 11 < kk := by
        by_contra hn
        rw [hl11, if_neg hn] at hne
        exact hne rfl
      have : min kk 11 = 11 := by omega
      rw [this]
      exact of_eval (eval_const _ _)
    · intro h0
      have h11 : ¬ 11 < kk := by
        intro hn
        rw [hl11, if_pos hn] at h0
        exact absurd h0 (by decide)
      have : min kk 11 = kk := by omega
      rw [this]
    refine WPs.seq (fun st => st.globals = G ∧ st.memory = ma ∧ st.ffi = s.ffi ∧
        (∀ x, x ≠ "i" → x ≠ "acc" → x ≠ "iend" → st.locals x = la x) ∧
        ∃ c0 c1 c2 c3 : Word, st.locals "acc" = some (.rStruct [.word c0, .word c1, .word c2,
          .word c3]) ∧ limbsVal [c0, c1, c2, c3] < bnP)
      (WPs.conseq (mul_inner hE (A := A) (B := B) (kk := kk) (ie := min kk 11) (ii0 := kk - 11)
        (c0 := 0#64) (c1 := 0#64) (c2 := 0#64) (c3 := 0#64) (by lk [laa]) (by lk [lab])
        (by lk [hkk]) (by lk []) (by lk []) (by lk []) (by decide) hklt (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) cAa cBa) ?_) ?_
    · rintro r ⟨l, rfl, -, -, -, hloc', -, c0, c1, c2, c3, hacc', hc'⟩
      refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, fun x h1 h2 h3 => (hloc' x h1 h2).trans ?_,
        c0, c1, c2, c3, hacc', hc'⟩
      simp [update_lookup, h1, h2, h3]
    rintro ⟨l3, g3, m3, f3⟩ ⟨hg, hm, hf, hloc3, e0, e1, e2, e3, hacc3, hc3⟩
    simp only at hg hm hf hloc3 hacc3
    subst g3 m3 f3
    have l3t : l3 "t" = some (.word pv) := (hloc3 _ (by decide) (by decide) (by decide)).trans lat
    have l3k : l3 "k" = some (.word (BitVec.ofNat 64 kk)) :=
      (hloc3 _ (by decide) (by decide) (by decide)).trans hkk
    refine WPs.seq_store4 hE (addr := coefAddr pv kk) (w0 := e0) (w1 := e1) (w2 := e2) (w3 := e3)
      (of_eval (by unfold coefAddr; ev [evalPanOp, l3t, l3k])) (by lk [hacc3]) ?_
    refine WPs.assign (old := BitVec.ofNat 64 kk) (by lk [l3k])
      (of_eval (w := BitVec.ofNat 64 (kk + 1)) (by ev [l3k, ofNat_succ])) ?_
    simp only [restorePanValueFfiLocal]
    refine ⟨rfl, rfl, ?_, ?_, kk + 1, ?_, by omega, CanonN.snoc (by omega) hct hc3⟩
    · intro x hx
      refine Eq.trans ?_ (hloc x hx)
      show restorePanValueLocal _ _ _ x = la x
      by_cases h3 : x = "iend"
      · subst h3
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h4 : x = "i"
      · subst h4
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      by_cases h5 : x = "acc"
      · subst h5
        simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
      simp (config := { decide := true }) [restorePanValueLocal, update_lookup, h3, h4, h5, hx]
      exact hloc3 x h4 h5 h3
    · intro x hx
      show set4 ma (coefAddr pv kk) e0 e1 e2 e3 x = s.memory x
      rw [set4_outN (n := 23) (by omega) (by omega) (Or.inl hx)]
      exact hlow x hx
    · simp (config := { decide := true }) [restorePanValueLocal, update_lookup]
  · rintro ⟨la, ga, ma, fa⟩ k ⟨hg, hf, hloc, hlow, kk, hkk, hk23, hct⟩ hcond
    simp only at hg hf hloc hlow hkk hct
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 kk) (by lk [hkk]))
      (of_eval (w := 23#64) (eval_const _ _)) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge : ¬ kk < 23 := by
      intro hlt
      have hl : (BitVec.ofNat 64 kk : Word) < 23#64 := by
        rw [BitVec.lt_def, hnat kk (by omega)]
        have : (23#64 : Word).toNat = 23 := by decide
        omega
      simp [evalPanCmp, hl] at hcv
    have : kk = 23 := by omega
    subst this
    exact ⟨⟨hg, hf, hloc, hlow, 23, hkk, hk23, hct⟩, hct⟩
  · rintro ⟨la, ga, ma, fa⟩ ⟨⟨hg, hf, hloc, hlow, -⟩, hct⟩
    simp only at hg hf hloc hlow hct
    subst ga fa
    have lat : la "t" = some (.word pv) := (hloc _ (by decide)).trans Lt
    have lad : la "d" = some (.word D) := (hloc _ (by decide)).trans Ld
    have lam : la "mark" = some (.word pv) := (hloc _ (by decide)).trans Lm
    refine WPs.seq_call_ret (fun vs g m1 ffi hret => ?_)
    obtain ⟨hg, hf, hfr1, hc1⟩ := reduce_ret hE hret (T := pv) (by lk [lat]) (by omega) hct
    subst g ffi
    refine WPs.seq_call_ret (fun vs g m2 ffi hret => ?_)
    obtain ⟨hg, hf, hcopy⟩ := memcpy_ret hE hret (dst := D) (src := pv) (nW := 384#64)
      (by lk [lad]) (by lk [lat]) (eval_const _ _)
      ⟨by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega, by rw [h384]; omega⟩
    subst g ffi
    rw [h384] at hcopy
    refine WPs.seq_call_ret (fun vs g m3 ffi hret => ?_)
    obtain ⟨hg, hm, hf⟩ := release_ret hE hret (mv := pv) (pv := qv) (by lk [lam])
      (by rw [hG]; lk [])
    subst g m3 ffi
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    simp only [restorePanValueFfiLocal]
    rw [hGs]
    refine ⟨_, m2, rfl, ?_, ?_⟩
    · intro x hx hxD
      exact (hcopy.cells x (by omega)).trans ((hfr1 x (Or.inl hx)).trans (hlow x hx))
    · obtain ⟨c, hpc, hlc⟩ := (hc1.mono (k := 12) (by omega)).poly
      exact CanonN.of_poly (PolyAt.of_copy (n := 12) hcopy alD hpH'.2 (by omega) (by omega) hpc)
        hlc

end InitECandidate.Solver.GuestBound
