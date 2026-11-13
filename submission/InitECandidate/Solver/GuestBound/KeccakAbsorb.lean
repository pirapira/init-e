import InitECandidate.Solver.GuestBound.KeccakFrame
import InitECandidate.Solver.GuestBound.WorldRestore

/-!
# `keccak_absorb_block` writes only the 200-byte state

Both absorb loops store at `stp + i` for `i < 136`, then `keccak_f1600` runs.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

theorem less136 (jj : Nat) (h : jj ≤ 136) :
    evalPanCmp .less (BitVec.ofNat 64 jj) (136#64 : Word) = if jj < 136 then 1#64 else 0#64 := by
  interval_cases jj <;> rfl

theorem ofNat_add8 (j : Nat) : (BitVec.ofNat 64 j : Word) + 8#64 = BitVec.ofNat 64 (j + 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- Invariant of the absorb loops. -/
def AbI (s : St σ) (stp : Word) (a : St σ) : Prop :=
  a.globals = s.globals ∧ a.ffi = s.ffi ∧ a.locals "stp" = some (.word stp) ∧
    (∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → a.memory x = s.memory x) ∧
    ∃ jj : Nat, a.locals "i" = some (.word (BitVec.ofNat 64 jj)) ∧ jj ≤ 136 ∧ jj % 8 = 0

/-- One absorb loop, whatever is xored in. -/
theorem absorb_loop (hE : GuestEnv E) {s0 : St σ} {stp : Word} (h64 : stp.toNat + 200 < 2 ^ 64)
    {v : Exp Word} (hI : AbI s0 stp s)
    (hQ : ∀ a, AbI s0 stp a → Q (.normal a.locals a.globals a.memory a.ffi)) :
    WPs E s (.while (.cmp .less (.var .local "i") (.const 136#64))
      (.seq (.store (.op .add [.var .local "stp", .var .local "i"])
          (.op .xor [.load .one (.op .add [.var .local "stp", .var .local "i"]), v]))
        (.assign .local "i" (.op .add [.var .local "i", .const 8#64])))) Q := by
  refine WPs.loopG (I := AbI s0 stp) hI ?_ (fun a k hI' _ => hQ a hI')
  rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hstp, hfr, jj, hi, hj, hj8⟩ ⟨w, cc, hcond, hw⟩
  dsimp only at hg hf hstp hfr hi
  subst hg hf
  have hc' := eval_cmp_inv hE (op := .less)
    (of_eval (w := BitVec.ofNat 64 jj) (by lk [hi])) (of_eval (eval_const _ (136#64))) _
    (cond_of_eval hcond)
  simp only [PanValue.word.injEq] at hc'
  rw [less136 jj hj] at hc'
  have hjj : jj < 136 := by
    by_contra hge
    rw [if_neg hge] at hc'
    rw [hc'] at hw
    simp at hw
  have ea : (stp + BitVec.ofNat 64 jj).toNat = stp.toNat + jj := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  refine WPs.seq_store_rng hE (addr := stp + BitVec.ofNat 64 jj) (lo := stp.toNat)
    (hi := stp.toNat + 200) (of_eval (by ev [hstp, hi]))
    (fun y hy => by
      obtain ⟨_, _, w', _, _, _, rfl⟩ := eval_op2_inv hE.word hy
      exact ⟨w', rfl⟩) (by omega) (by omega) hfr (fun m hfr' => ?_)
  refine WPs.assign (old := BitVec.ofNat 64 jj) (w := BitVec.ofNat 64 (jj + 8)) hi
    (of_eval (by ev [hi, ofNat_add8])) ?_
  exact ⟨rfl, rfl, by lk [hstp], hfr', jj + 8, by lk [], by omega, by omega⟩

/-- Locals bound from a single word argument are words. -/
theorem allW_one {cl : VarName → Option (PanValue Word)} {x : VarName} {w : Word}
    (h : updatePanValueMap (fun _ => none) x (.word w) = cl) : AllW cl := by
  intro y v hy
  rw [← h, update_lookup] at hy
  split at hy
  · exact ⟨w, (Option.some.inj hy).symm⟩
  · cases hy

set_option maxHeartbeats 8000000 in
theorem keccak_absorb_frame (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "keccak_absorb_block" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (stp : Word) (hstp : s.locals "stp" = some (.word stp))
    (h64 : stp.toNat + 200 < 2 ^ 64) (h : Runs E s body r) :
    Stopped r ∨ ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
      ∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → m' x = s.memory x := by
  have hbody := (fun_of_index 102 hE.functions (by guest_decl_at 102) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (fun r => ∃ l m', r = .returned l s.globals m' s.ffi [.word 0#64] ∧
    ∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → m' x = s.memory x)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  have hI0 : AbI s stp (⟨updatePanValueMap s.locals "i" (.word 0#64), s.globals, s.memory,
      s.ffi⟩ : St σ) :=
    ⟨rfl, rfl, by lk [hstp], fun _ _ => rfl, 0, by lk [], by omega, by omega⟩
  refine WPs.seqG (fun a => AbI s stp a) (WPs.ite_both (fun w _ => ?_)) ?_
  · split
    · exact absorb_loop hE h64 hI0 (fun a hI => hI)
    · exact absorb_loop hE h64 hI0 (fun a hI => hI)
  rintro ⟨la, ga, ma, fa⟩ ⟨hg, hf, hstp', hfr, -⟩
  dsimp only at hg hf hstp' hfr
  subst hg hf
  refine WPs.seqG (fun a => ∃ m', a = ⟨la, s.globals, m', s.ffi⟩ ∧
      ∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → m' x = s.memory x)
    (WPs.call_runs (fun rb => ∃ l m', rb = .returned l s.globals m' s.ffi [.word 0#64] ∧
        ∀ x : Word, (x.toNat < stp.toNat ∨ stp.toNat + 200 ≤ x.toNat) → m' x = ma x)
      ?_ ?_ ?_) ?_
  · intro ps cbody values cl hlk hvalues hbind rb hrun
    have hparams := (fun_of_index 101 hE.functions (by guest_decl_at 101) (by decide +kernel)
      hlk).2
    simp (config := { decide := true }) [evalArgs_cons, evalArgs_nil, evalF_local, hstp']
      at hvalues
    subst hvalues
    rw [hparams] at hbind
    simp [bindPanValueParameters] at hbind
    exact keccak_f1600_frame hE ps cbody hlk ⟨cl, s.globals, ma, s.ffi⟩ rb stp
      (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
      (allW_one hbind) h64 hrun
  · rintro rb ⟨l, m', rfl, -⟩
    exact ⟨_, _, _, _, _, rfl⟩
  · rintro l g m ffi v ⟨l', m', heq, hh⟩
    injection heq with _ hg hm hf _
    subst g m ffi
    exact ⟨m', rfl, fun x hx => (hh x hx).trans (hfr x hx)⟩
  rintro _ ⟨m', rfl, hfr'⟩
  refine WPs.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  exact ⟨_, m', rfl, hfr'⟩

end InitECandidate.Solver.GuestBound
