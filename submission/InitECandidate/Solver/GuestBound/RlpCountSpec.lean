import InitECandidate.Solver.GuestBound.RlpTotalSpec
import InitECandidate.Solver.GuestBound.MemCpy
import InitECandidate.Solver.GuestBound.HtabDiff
import InitECandidate.Solver.GuestBound.Fq12InvInner

/-!
# `rlp_list_count` walks a chain of items that exactly fills the slice

`Items m p o c`: starting at `p`, `c` consecutive items (each with its `TotSpec`
total, at least 1) end at offset `o`.  `rlp_list_count(p, len)` returns `c`
with `Items m p len c`.  The chain is determined by memory, so a second pass
finds the same offsets (issue #30).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem byteAt_low {m m' : Word → Option (PanValue Word)} {a : Word}
    (h : ∀ x : Word, x.toNat ≤ a.toNat → m' x = m x) : byteAt m' a = byteAt m a := by
  unfold byteAt
  rw [h _ (al8_le a)]

/-- `TotSpec` reads at most nine bytes. -/
theorem TotSpec.frame {m m' : Word → Option (PanValue Word)} {p T : Word} (h : TotSpec m p T)
    (hp : p.toNat + 16 < 2 ^ 64)
    (hb : ∀ j, j < 9 → byteAt m' (p + BitVec.ofNat 64 j) = byteAt m (p + BitVec.ofNat 64 j)) :
    TotSpec m' p T := by
  obtain ⟨b, hbt, hc⟩ := h
  have hb256 := byteAt_lt hbt
  have h0 : p + BitVec.ofNat 64 0 = p := by simp
  have hb0 : byteAt m' p = some b := by
    have := hb 0 (by omega)
    rw [h0] at this
    rw [this]
    exact hbt
  have rl : ∀ (k : Nat) (n : Word), k ≤ 8 → RL m (p + 1#64) k n → RL m' (p + 1#64) k n := by
    intro k n hk hrl
    refine hrl.frame (fun j hj => ?_)
    have e : p + 1#64 + BitVec.ofNat 64 j = p + BitVec.ofNat 64 (j + 1) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [e]
    exact hb (j + 1) (by omega)
  have sub1 : (b - 183#64).toNat = (2 ^ 64 - 183 + b.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]
    rfl
  have sub2 : (b - 247#64).toNat = (2 ^ 64 - 247 + b.toNat) % 2 ^ 64 := by
    rw [BitVec.toNat_sub]
    rfl
  refine ⟨b, hb0, ?_⟩
  rcases hc with h1 | h1 | ⟨a1, a2, n, hn, hT⟩ | h1 | ⟨a1, n, hn, hT⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl ⟨a1, a2, n, rl _ n (by rw [sub1]; omega) hn, hT⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨a1, n, rl _ n (by rw [sub2]; omega) hn, hT⟩)))

/-- `c` consecutive items from `p` end at offset `o`. -/
inductive Items (m : Word → Option (PanValue Word)) (p : Word) : Nat → Nat → Prop
  | zero : Items m p 0 0
  | step {o c : Nat} {t : Word} : Items m p o c → TotSpec m (p + BitVec.ofNat 64 o) t →
      1 ≤ t.toNat → Items m p (o + t.toNat) (c + 1)

theorem Items.fn {m : Word → Option (PanValue Word)} {p : Word} {o o' c : Nat}
    (h : Items m p o c) (h' : Items m p o' c) : o = o' := by
  induction h generalizing o' with
  | zero => cases h'; rfl
  | step _ ht _ ih =>
    cases h' with
    | step h1 ht' _ =>
      have := ih h1
      subst this
      have := ht.fn ht'
      subst this
      rfl

/-- Offsets grow with the count. -/
theorem Items.count_le {m : Word → Option (PanValue Word)} {p : Word} {o c : Nat}
    (h : Items m p o c) : c ≤ o := by
  induction h with
  | zero => exact Nat.le_refl _
  | step _ _ ht ih => omega

/-- Invariant of the counting loop. -/
def CnI (pv fv pw lw : Word) (s a : St σ) : Prop :=
  a.globals = s.globals ∧ a.ffi = s.ffi ∧ ScrMem pv fv s.memory a.memory ∧
    a.locals "p" = some (.word pw) ∧ a.locals "len" = some (.word lw) ∧
    ∃ ow cw : Word, a.locals "off" = some (.word ow) ∧ a.locals "count" = some (.word cw) ∧
      ow.toNat ≤ lw.toNat ∧ Items s.memory pw ow.toNat cw.toNat

set_option maxHeartbeats 8000000 in
theorem rlp_list_count_items (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_list_count" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pv fv pw lw : Word) (hpw : s.locals "p" = some (.word pw))
    (hlen : s.locals "len" = some (.word lw))
    (hp : s.globals "scratch_ptr" = some (.word pv))
    (hf : s.globals "frame_mem_ptr" = some (.word fv)) (hfp : fv.toNat ≤ pv.toNat)
    (hlow : pw.toNat + lw.toNat + 16 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m c, r = .returned l s.globals m s.ffi [.word c] ∧
      ScrMem pv fv s.memory m ∧ Items s.memory pw lw.toNat c.toNat := by
  have hbody := (fun_of_index 113 hE.functions (by guest_decl_at 113) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m c, r = .returned l s.globals m s.ffi [.word c] ∧
    ScrMem pv fv s.memory m ∧ Items s.memory pw lw.toNat c.toNat)) r h
  have hfvl := fv.isLt
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := fun r => ∃ l m c, r = .returned l s.globals m s.ffi [.word c] ∧
    ScrMem pv fv s.memory m ∧ Items s.memory pw lw.toNat c.toNat) ?_
    (by rintro r ⟨l, m, c, rfl, hk⟩; exact ⟨_, m, c, rfl, hk⟩)
  refine WPs.seqG (fun a => CnI pv fv pw lw s a ∧ a.locals "off" = some (.word lw))
    (WPs.loopG (I := CnI pv fv pw lw s)
      ⟨rfl, rfl, ScrMem.refl _ _ _, by lk [hpw], by lk [hlen], 0#64, 0#64, by lk [], by lk [],
        Nat.zero_le _, .zero⟩ ?_ ?_) ?_
  · rintro ⟨la, ga, ma, fa⟩ ⟨hg, hfa, hk, hP, hL, ow, cw, hoff, hcnt, c2, hit⟩ -
    simp only at hg hfa hk hP hL hoff hcnt
    subst hg hfa
    have hsub : (lw - ow).toNat = lw.toNat - ow.toNat := by
      rw [BitVec.toNat_sub]
      have := ow.isLt
      have := lw.isLt
      omega
    have epo : (pw + ow).toNat = pw.toNat + ow.toNat := by
      rw [BitVec.toNat_add]
      omega
    refine WPs.decCall_ret (fun v g m ffi hret => ?_)
    obtain ⟨-, -, -, t', hv', t1, -⟩ := rlptotal_ret hE hret (pw0 := pw + ow)
      (lenv := lw - ow) (by ev [hP, hoff]) (by ev [hL, hoff]) hp hf hfp
    obtain ⟨hg, hf', t, hv, hts, t2, hk2⟩ := rlptotal_tot_ret hE hret (pw := pw + ow)
      (lw := lw - ow) (by ev [hP, hoff]) (by ev [hL, hoff]) hp hf hfp
    simp only [List.cons.injEq, and_true] at hv hv'
    subst g ffi v
    simp only [PanValue.word.injEq] at hv'
    subst hv'
    rw [hsub] at t2
    try dsimp only
    refine WPs.seq_assign (old := ow) (by lk [hoff]) (of_eval (w := ow + t) (by ev [hoff])) ?_
    try dsimp only
    refine WPs.assign (old := cw) (by lk [hcnt]) (of_eval (w := cw + 1#64) (by ev [hcnt])) ?_
    simp only [restorePanValueFfiLocal]
    have hlv := lw.isLt
    have e1 : (ow + t).toNat = ow.toNat + t.toNat := by
      rw [BitVec.toNat_add]
      omega
    have hcle := hit.count_le
    have e2 : (cw + 1#64).toNat = cw.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#64 : Word).toNat = 1 by decide]
      omega
    have hts0 : TotSpec s.memory (pw + BitVec.ofNat 64 ow.toNat) t := by
      rw [ofNat_toNat']
      refine hts.frame (by omega) (fun j hj => byteAt_low (fun x hx => ?_))
      have e : (pw + ow + BitVec.ofNat 64 j).toNat = pw.toNat + ow.toNat + j := by
        rw [BitVec.toNat_add, epo, BitVec.toNat_ofNat]
        omega
      exact (hk x (Or.inl (by omega))).symm
    refine ⟨rfl, rfl, hk.trans hk2,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hP],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup, hL],
      ow + t, cw + 1#64,
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup],
      by simp (config := { decide := true }) [restorePanValueLocal, update_lookup], ?_, ?_⟩
    · rw [e1]; omega
    · rw [e1, e2]
      exact .step hit hts0 t1
  · rintro a kk ⟨hg, hfa, hk, hP, hL, ow, cw, hoff, hcnt, c2, hit⟩ hcond
    have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := ow) (by lk [hoff]))
      (of_eval (w := lw) (by lk [hL])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hcv
    have hge := (lower_iff ow lw).mp hcv.symm
    have heq : ow = lw := BitVec.eq_of_toNat_eq (by omega)
    subst heq
    exact ⟨⟨hg, hfa, hk, hP, hL, ow, cw, hoff, hcnt, c2, hit⟩, hoff⟩
  · rintro a ⟨⟨hg, hfa, hk, hP, hL, ow, cw, hoff, hcnt, c2, hit⟩, hol⟩
    have heq : ow = lw := by
      rw [hoff] at hol
      simpa using hol
    subst heq
    refine WPs.ret (w := cw) (of_eval (by lk [hcnt])) ?_
    exact ⟨_, a.memory, cw, by rw [hg, hfa], hk, hit⟩

end InitECandidate.Solver.GuestBound
