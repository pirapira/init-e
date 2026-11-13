import InitECandidate.Solver.GuestBound.RlpTotSpec
import InitECandidate.Solver.GuestBound.TrieCompact

/-!
# `rlp_item_header` agrees with `TotSpec`

`rlp_item_header(p, len)` returns `<h0, h1, kind>` where `h0 + h1` is the total
length of the item at `p` (as `TotSpec` reads it off memory) and fits in `len`.
The function changes nothing.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- What `rlp_item_header` returns. -/
def HdrQ (s : St σ) (pw lw : Word) (r : Result σ) : Prop :=
  ∃ l, ∃ (h0 h1 k : Word), r = .returned l s.globals s.memory s.ffi
      [.rStruct [.word h0, .word h1, .word k]] ∧
    TotSpec s.memory pw (h0 + h1) ∧ h0.toNat + h1.toNat ≤ lw.toNat

theorem HdrQ.restore {pw lw : Word} {x : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (h : HdrQ s pw lw r) : HdrQ s pw lw (restorePanValueFfiLocal x old r) := by
  obtain ⟨l, h0, h1, k, rfl, hk⟩ := h
  exact ⟨_, h0, h1, k, rfl, hk⟩

theorem add_sub_w (b c : Word) : 1#64 + (b - c) = 1#64 + b - c := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub]
  omega

set_option maxHeartbeats 16000000 in
theorem rlp_item_header_tot (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_item_header" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (pw lw : Word) (hpw : s.locals "p" = some (.word pw))
    (hlw : s.locals "len" = some (.word lw)) (h : Runs E s body r) :
    Stopped r ∨ HdrQ s pw lw r := by
  have hbody := (fun_of_index 109 hE.functions (by guest_decl_at 109) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (HdrQ s pw lw)) r h
  have hfq := rlp_fail_quiet hE
  have hnr := rlp_fail_noReturn hE
  have h1 : (1#64 : Word).toNat = 1 := rfl
  have hlwl := lw.isLt
  refine WPs.guard_nr hnr (fun hc0 => ?_)
  have hl1 : 1 ≤ lw.toNat := by
    have := eval_cmp_inv hE (op := .equal) (of_eval (w := lw) (by lk [hlw]))
      (of_eval (eval_const _ 0#64)) _ hc0
    simp only [PanValue.word.injEq] at this
    by_contra hlt
    have : lw = 0#64 := BitVec.eq_of_toNat_eq (by simp; omega)
    subst this
    simp [evalPanCmp] at *
  have esub : (lw - 1#64).toNat = lw.toNat - 1 := by
    rw [BitVec.toNat_sub, h1]
    omega
  refine WPs.dec_ev (fun vb hvb => WPs.conseq (Q' := HdrQ s pw lw) ?_ (fun r h => h.restore))
  obtain ⟨b, rfl, hbt⟩ := loadByte_byteAt hE hvb (addr := pw) (of_eval (by lk [hpw]))
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qp : L "p" = some (.word pw) := by rw [hLL]; lk [hpw]
  have ql : L "len" = some (.word lw) := by rw [hLL]; lk [hlw]
  have qb : L "b" = some (.word b) := by rw [hLL]; lk []
  clear hLL
  have cmpv : ∀ (op : Cmp) (e1 e2 : Exp Word) (x y w : Word),
      E.eval (⟨L, s.globals, s.memory, s.ffi⟩ : St σ) e1 = some (.word x) →
      E.eval (⟨L, s.globals, s.memory, s.ffi⟩ : St σ) e2 = some (.word y) →
      E.eval (⟨L, s.globals, s.memory, s.ffi⟩ : St σ) (.cmp op e1 e2) = some (.word w) →
      w = evalPanCmp op x y := by
    intro op e1 e2 x y w h1 h2 hw
    have := eval_cmp_inv hE (op := op) (of_eval h1) (of_eval h2) _ hw
    simpa using this
  have eb : E.eval (⟨L, s.globals, s.memory, s.ffi⟩ : St σ) (.var .local "b") =
      some (.word b) := by lk [qb]
  have elen1 : ∀ (L' : VarName → Option (PanValue Word)) (m' : Word → Option (PanValue Word)),
      L' "len" = some (.word lw) →
      E.eval ⟨L', s.globals, m', s.ffi⟩ (.op .sub [.var .local "len", .const 1#64]) =
        some (.word (lw - 1#64)) := by
    intro L' m' h
    simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_local, h, wordsProj_cons,
      wordsProj_nil, wordOp]
  -- below 128
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩ ∧ 128 ≤ b.toNat)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · have hwv := cmpv .lower _ _ b 128#64 w eb (eval_const _ _) hw
    split
    · rename_i h0
      rw [h0] at hwv
      exact WPs.skip ⟨rfl, (lower_iff b 128#64).mp hwv.symm⟩
    · rename_i h0
      have hlt : b.toNat < 128 := by
        by_contra hge
        exact h0 (hwv.trans ((lower_iff b 128#64).mpr (by simpa using hge)))
      exact WPs.ret_triple (a := 0#64) (b := 1#64) (c := 0#64) (of_eval (eval_const _ _))
        (of_eval (eval_const _ _)) (of_eval (eval_const _ _))
        ⟨_, 0#64, 1#64, 0#64, rfl, ⟨b, hbt, Or.inl ⟨hlt, by simp⟩⟩, by
          show (0#64 : Word).toNat + (1#64 : Word).toNat ≤ lw.toNat
          rw [h1]
          simp
          omega⟩
  intro a ha
  obtain ⟨ha, h128⟩ := ha
  rw [ha]
  clear ha a
  -- short string
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩ ∧ 183 < b.toNat)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · have hwv := cmpv .notLower _ _ 183#64 b w (eval_const _ _) eb hw
    split
    · rename_i h0
      rw [h0] at hwv
      exact WPs.skip ⟨rfl, (notLower_iff 183#64 b).mp hwv.symm⟩
    · rename_i h0
      have hle : b.toNat ≤ 183 := by
        by_contra hgt
        exact h0 (hwv.trans ((notLower_iff 183#64 b).mpr (by simpa using hgt)))
      refine WPs.dec (w := b - 128#64) (of_eval (by ev [qb])) ?_
      refine WPs.conseq (Q' := HdrQ s pw lw) ?_ (fun r h => by
        obtain ⟨l, h0', h1', k, rfl, hk⟩ := h
        exact ⟨_, h0', h1', k, rfl, hk⟩)
      refine WPs.guard_nr hnr (fun hc => ?_)
      have hn := lower_false hE (wb := b - 128#64) (elen1 _ _ (by lk [ql])) (by lk []) hc
      rw [esub] at hn
      refine WPs.guard2_quiet hfq ?_
      exact WPs.ret_triple (a := 1#64) (b := b - 128#64) (c := 0#64) (of_eval (eval_const _ _))
        (of_eval (by lk [])) (of_eval (eval_const _ _))
        ⟨_, 1#64, b - 128#64, 0#64, rfl,
          ⟨b, hbt, Or.inr (Or.inl ⟨h128, hle, add_sub_w b 128#64⟩)⟩, by rw [h1]; omega⟩
  intro a ha
  obtain ⟨ha, h183⟩ := ha
  rw [ha]
  clear ha a
  -- long string
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩ ∧ 191 < b.toNat)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · have hwv := cmpv .notLower _ _ 191#64 b w (eval_const _ _) eb hw
    split
    · rename_i h0
      rw [h0] at hwv
      exact WPs.skip ⟨rfl, (notLower_iff 191#64 b).mp hwv.symm⟩
    · rename_i h0
      have hle : b.toNat ≤ 191 := by
        by_contra hgt
        exact h0 (hwv.trans ((notLower_iff 191#64 b).mpr (by simpa using hgt)))
      refine WPs.dec (w := b - 183#64) (of_eval (by ev [qb])) ?_
      refine WPs.conseq (Q' := HdrQ s pw lw) ?_ (fun r h => by
        obtain ⟨l, h0', h1', k, rfl, hk⟩ := h
        exact ⟨_, h0', h1', k, rfl, hk⟩)
      refine WPs.guard_nr hnr (fun hc => ?_)
      have hll := lower_false hE (wb := b - 183#64) (elen1 _ _ (by lk [ql])) (by lk []) hc
      rw [esub] at hll
      refine WPs.decCall_word (fun nn g m ffi hret =>
        WPs.conseq (Q' := HdrQ s pw lw) ?_ (fun r h => h.restore))
      obtain ⟨rfl, rfl, rfl, hrl⟩ := rlpreadlen_ret hE hret (pw := pw + 1#64)
        (nw := b - 183#64) (by ev [qp]) (by lk [])
      refine WPs.guard_quiet hfq ?_
      refine WPs.guard_nr hnr (fun hc2 => ?_)
      have esub2 : (lw - 1#64 - (b - 183#64)).toNat = lw.toNat - 1 - (b - 183#64).toNat := by
        rw [BitVec.toNat_sub, esub]
        omega
      have hn := lower_false hE (a := .op .sub [.op .sub [.var .local "len", .const 1#64],
        .var .local "ll"]) (wa := lw - 1#64 - (b - 183#64)) (wb := nn)
        (by simp (config := { decide := true }) [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
          evalF_local, update_lookup, ql, wordsProj_cons, wordsProj_nil, wordOp])
        (by lk []) hc2
      rw [esub2] at hn
      have e1l : (1#64 + (b - 183#64)).toNat = 1 + (b - 183#64).toNat := by
        rw [BitVec.toNat_add, h1]
        omega
      exact WPs.ret_triple (a := 1#64 + (b - 183#64)) (b := nn) (c := 0#64)
        (of_eval (by ev [])) (of_eval (by lk [])) (of_eval (eval_const _ _))
        ⟨_, _, nn, 0#64, rfl,
          ⟨b, hbt, Or.inr (Or.inr (Or.inl ⟨h183, hle, nn, hrl, BitVec.add_assoc _ _ _⟩))⟩,
          by rw [e1l]; omega⟩
  intro a ha
  obtain ⟨ha, h191⟩ := ha
  rw [ha]
  clear ha a
  -- short list
  refine WPs.seqG (fun a => a = ⟨L, s.globals, s.memory, s.ffi⟩ ∧ 247 < b.toNat)
    (WPs.ite_both (fun w hw => ?_)) ?_
  · have hwv := cmpv .notLower _ _ 247#64 b w (eval_const _ _) eb hw
    split
    · rename_i h0
      rw [h0] at hwv
      exact WPs.skip ⟨rfl, (notLower_iff 247#64 b).mp hwv.symm⟩
    · rename_i h0
      have hle : b.toNat ≤ 247 := by
        by_contra hgt
        exact h0 (hwv.trans ((notLower_iff 247#64 b).mpr (by simpa using hgt)))
      refine WPs.dec (w := b - 192#64) (of_eval (by ev [qb])) ?_
      refine WPs.conseq (Q' := HdrQ s pw lw) ?_ (fun r h => by
        obtain ⟨l, h0', h1', k, rfl, hk⟩ := h
        exact ⟨_, h0', h1', k, rfl, hk⟩)
      refine WPs.guard_nr hnr (fun hc => ?_)
      have hn := lower_false hE (wb := b - 192#64) (elen1 _ _ (by lk [ql])) (by lk []) hc
      rw [esub] at hn
      exact WPs.ret_triple (a := 1#64) (b := b - 192#64) (c := 1#64) (of_eval (eval_const _ _))
        (of_eval (by lk [])) (of_eval (eval_const _ _))
        ⟨_, 1#64, b - 192#64, 1#64, rfl,
          ⟨b, hbt, Or.inr (Or.inr (Or.inr (Or.inl ⟨h191, hle, add_sub_w b 192#64⟩)))⟩,
          by rw [h1]; omega⟩
  intro a ha
  obtain ⟨ha, h247⟩ := ha
  rw [ha]
  clear ha a
  -- long list
  refine WPs.dec (w := b - 247#64) (of_eval (by ev [qb])) ?_
  refine WPs.conseq (Q' := HdrQ s pw lw) ?_ (fun r h => h.restore)
  refine WPs.guard_nr hnr (fun hc => ?_)
  have hll := lower_false hE (wb := b - 247#64) (elen1 _ _ (by lk [ql])) (by lk []) hc
  rw [esub] at hll
  refine WPs.decCall_word (fun nn g m ffi hret =>
    WPs.conseq (Q' := HdrQ s pw lw) ?_ (fun r h => h.restore))
  obtain ⟨rfl, rfl, rfl, hrl⟩ := rlpreadlen_ret hE hret (pw := pw + 1#64)
    (nw := b - 247#64) (by ev [qp]) (by lk [])
  refine WPs.guard_quiet hfq ?_
  refine WPs.guard_nr hnr (fun hc2 => ?_)
  have esub2 : (lw - 1#64 - (b - 247#64)).toNat = lw.toNat - 1 - (b - 247#64).toNat := by
    rw [BitVec.toNat_sub, esub]
    omega
  have hn := lower_false hE (a := .op .sub [.op .sub [.var .local "len", .const 1#64],
    .var .local "ll"]) (wa := lw - 1#64 - (b - 247#64)) (wb := nn)
    (by simp (config := { decide := true }) [evalF_op hE.word, evalArgs_cons, evalArgs_nil,
      evalF_local, update_lookup, ql, wordsProj_cons, wordsProj_nil, wordOp])
    (by lk []) hc2
  rw [esub2] at hn
  have e1l : (1#64 + (b - 247#64)).toNat = 1 + (b - 247#64).toNat := by
    rw [BitVec.toNat_add, h1]
    omega
  exact WPs.ret_triple (a := 1#64 + (b - 247#64)) (b := nn) (c := 1#64)
    (of_eval (by ev [])) (of_eval (by lk [])) (of_eval (eval_const _ _))
    ⟨_, _, nn, 1#64, rfl,
      ⟨b, hbt, Or.inr (Or.inr (Or.inr (Or.inr ⟨h247, nn, hrl, BitVec.add_assoc _ _ _⟩)))⟩,
      by rw [e1l]; omega⟩

end InitECandidate.Solver.GuestBound
