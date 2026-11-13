import InitECandidate.Solver.GuestBound.RlpLenSpec

/-!
# The total length of an RLP item as a function of memory

`TotSpec m p T`: the item whose first byte is at `p` has total length `T`
(header plus payload), read off the bytes in `m`.  `rlp_item_total_unchecked`
computes it.  The relation is functional, so a second pass over unchanged
bytes finds the same totals (issue #30).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The total length of the item at `p`, in the forms the evaluator produces. -/
def TotSpec (m : Word → Option (PanValue Word)) (p T : Word) : Prop :=
  ∃ b : Word, byteAt m p = some b ∧
    ((b.toNat < 128 ∧ T = 1#64) ∨
      (128 ≤ b.toNat ∧ b.toNat ≤ 183 ∧ T = 1#64 + b - 128#64) ∨
      (183 < b.toNat ∧ b.toNat ≤ 191 ∧ ∃ n, RL m (p + 1#64) (b - 183#64).toNat n ∧
        T = 1#64 + (b - 183#64 + n)) ∨
      (191 < b.toNat ∧ b.toNat ≤ 247 ∧ T = 1#64 + b - 192#64) ∨
      (247 < b.toNat ∧ ∃ n, RL m (p + 1#64) (b - 247#64).toNat n ∧
        T = 1#64 + (b - 247#64 + n)))

theorem TotSpec.fn {m : Word → Option (PanValue Word)} {p T T' : Word} (h : TotSpec m p T)
    (h' : TotSpec m p T') : T = T' := by
  obtain ⟨b, hb, hc⟩ := h
  obtain ⟨b', hb', hc'⟩ := h'
  rw [hb] at hb'
  simp only [Option.some.injEq] at hb'
  subst hb'
  rcases hc with ⟨a1, rfl⟩ | ⟨a1, a2, rfl⟩ | ⟨a1, a2, n, hn, rfl⟩ | ⟨a1, a2, rfl⟩ | ⟨a1, n, hn, rfl⟩ <;>
    rcases hc' with ⟨c1, rfl⟩ | ⟨c1, c2, rfl⟩ | ⟨c1, c2, n', hn', rfl⟩ | ⟨c1, c2, rfl⟩ |
      ⟨c1, n', hn', rfl⟩ <;>
    first
      | rfl
      | omega
      | (have := hn.fn hn'; subst this; rfl)

theorem lower_iff (a b : Word) : evalPanCmp .lower a b = 0#64 ↔ b.toNat ≤ a.toNat := by
  by_cases hl : a < b
  · have : ¬ b.toNat ≤ a.toNat := by rw [BitVec.lt_def] at hl; omega
    simp [evalPanCmp, hl, this]
  · have : b.toNat ≤ a.toNat := by rw [BitVec.lt_def] at hl; omega
    simp [evalPanCmp, hl, this]

theorem notLower_iff (a b : Word) : evalPanCmp .notLower a b = 0#64 ↔ a.toNat < b.toNat := by
  by_cases hl : a < b
  · have : a.toNat < b.toNat := by rw [BitVec.lt_def] at hl; exact hl
    simp [evalPanCmp, hl, this]
  · have : ¬ a.toNat < b.toNat := by rw [BitVec.lt_def] at hl; exact hl
    simp [evalPanCmp, hl, this]

/-- What a returning `rlp_read_length` leaves. -/
theorem rlpreadlen_ret (hE : GuestEnv E) {e1 e2 : Exp Word} {pw nw v : Word}
    {g : VarName → Option (PanValue Word)} {m : Word → Option (PanValue Word)}
    {ffi : FfiState σ}
    (h : CalleeRet E s "rlp_read_length" [e1, e2] [.word v] g m ffi)
    (h1 : E.eval s e1 = some (.word pw)) (h2 : E.eval s e2 = some (.word nw)) :
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ RL s.memory pw nw.toNat v := by
  obtain ⟨parameters, body, values, cl, l, hlookup, hvalues, hbind, hrun⟩ := h
  have hparams := (fun_of_index 106 hE.functions (by guest_decl_at 106) (by decide +kernel)
    hlookup).2
  simp only [evalArgs_cons, evalArgs_nil, h1, h2, Option.map_some, Option.some.injEq] at hvalues
  subst hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases rlp_read_length_spec hE parameters body hlookup ⟨cl, s.globals, s.memory, s.ffi⟩ _ pw nw
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) hrun
    with hst | ⟨l', v', heq, hrl⟩
  · exact absurd hst (fun h => h)
  · cases heq
    exact ⟨rfl, rfl, rfl, hrl⟩

set_option maxHeartbeats 8000000 in
theorem rlp_item_total_unchecked_spec (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "rlp_item_total_unchecked" E.functions =
      some (parameters, body))
    (s : St σ) (r : Result σ) (pw : Word) (hp : s.locals "p" = some (.word pw))
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l T, r = .returned l s.globals s.memory s.ffi [.word T] ∧
      TotSpec s.memory pw T := by
  have hbody := (fun_of_index 114 hE.functions (by guest_decl_at 114) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l T, r = .returned l s.globals s.memory s.ffi [.word T] ∧
    TotSpec s.memory pw T)) r h
  refine WPs.dec_ev (fun vb hvb => WPs.conseq (Q' := fun r => ∃ l T,
    r = .returned l s.globals s.memory s.ffi [.word T] ∧ TotSpec s.memory pw T) ?_
    (fun r h => by
      obtain ⟨l, T, rfl, hk⟩ := h
      exact ⟨_, T, rfl, hk⟩))
  obtain ⟨b, rfl, hbt⟩ := loadByte_byteAt hE hvb (addr := pw) (of_eval (by lk [hp]))
  refine WPs.name_locals (fun L hLL => ?_)
  dsimp only at hLL
  have qp : L "p" = some (.word pw) := by rw [hLL]; lk [hp]
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
      exact WPs.ret (w := 1#64) (of_eval (eval_const _ _))
        ⟨_, 1#64, rfl, b, hbt, Or.inl ⟨hlt, rfl⟩⟩
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
      exact WPs.ret (w := 1#64 + b - 128#64) (of_eval (by ev [qb]))
        ⟨_, _, rfl, b, hbt, Or.inr (Or.inl ⟨h128, hle, rfl⟩)⟩
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
      refine WPs.decCall_word (fun nn g m ffi hret => ?_)
      obtain ⟨rfl, rfl, rfl, hrl⟩ := rlpreadlen_ret hE hret (pw := pw + 1#64)
        (nw := b - 183#64) (by ev [qp]) (by lk [])
      refine WPs.ret (w := 1#64 + (b - 183#64 + nn)) (of_eval (by ev [])) ?_
      simp only [restorePanValueFfiLocal]
      exact ⟨_, _, rfl, b, hbt, Or.inr (Or.inr (Or.inl ⟨h183, hle, nn, hrl, rfl⟩))⟩
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
      exact WPs.ret (w := 1#64 + b - 192#64) (of_eval (by ev [qb]))
        ⟨_, _, rfl, b, hbt, Or.inr (Or.inr (Or.inr (Or.inl ⟨h191, hle, rfl⟩)))⟩
  intro a ha
  obtain ⟨ha, h247⟩ := ha
  rw [ha]
  clear ha a
  -- long list
  refine WPs.dec (w := b - 247#64) (of_eval (by ev [qb])) ?_
  refine WPs.decCall_word (fun nn g m ffi hret => ?_)
  obtain ⟨rfl, rfl, rfl, hrl⟩ := rlpreadlen_ret hE hret (pw := pw + 1#64)
    (nw := b - 247#64) (by ev [qp]) (by lk [])
  refine WPs.ret (w := 1#64 + (b - 247#64 + nn)) (of_eval (by ev [])) ?_
  simp only [restorePanValueFfiLocal]
  exact ⟨_, _, rfl, b, hbt, Or.inr (Or.inr (Or.inr (Or.inr ⟨h247, nn, hrl, rfl⟩)))⟩

end InitECandidate.Solver.GuestBound
