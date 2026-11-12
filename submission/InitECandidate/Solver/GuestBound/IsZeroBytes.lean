import InitECandidate.Solver.GuestBound.HtabDiff
import InitECandidate.Solver.GuestBound.MemStruct

/-!
# `is_zero_bytes`

Returns 1 when all `n` bytes at `p` are zero, and 0 at the first nonzero byte.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- What `is_zero_bytes` returns. -/
def ZeroQ (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (p : Word) (n : Nat) (r : Result σ) : Prop :=
  ∃ l z, r = .returned l g m f [.word z] ∧
    ((z = 1#64 ∧ ∀ k, k < n → byteAt m (off p k) = some 0#64) ∨
      (z = 0#64 ∧ ∃ k x, k < n ∧ byteAt m (off p k) = some x ∧ x ≠ 0#64))

def ZeroI (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) (p nW : Word) (j : Nat) (a : St σ) : Prop :=
  a.globals = g ∧ a.memory = m ∧ a.ffi = f ∧ a.locals "p" = some (.word p) ∧
    a.locals "n" = some (.word nW) ∧ a.locals "i" = some (.word (BitVec.ofNat 64 j)) ∧
    j ≤ nW.toNat ∧ ∀ k, k < j → byteAt m (off p k) = some 0#64

set_option maxHeartbeats 8000000 in
theorem is_zero_bytes_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "is_zero_bytes" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (p nW : Word) (hp : s.locals "p" = some (.word p))
    (hn : s.locals "n" = some (.word nW)) (h : Runs E s body r) :
    Stopped r ∨ ZeroQ s.globals s.memory s.ffi p nW.toNat r := by
  have hbody := (fun_of_index 19 hE.functions (by guest_decl_at 19) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPs E s _ (ZeroQ s.globals s.memory s.ffi p nW.toNat)) r h
  refine WPs.dec (w := 0#64) (of_eval (eval_const _ _)) ?_
  refine WPs.conseq (Q' := ZeroQ s.globals s.memory s.ffi p nW.toNat) ?_
    (by rintro r ⟨l, z, rfl, hz⟩; exact ⟨_, z, rfl, hz⟩)
  have hjt : ∀ j : Nat, j ≤ nW.toNat → (BitVec.ofNat 64 j : Word).toNat = j := by
    intro j hj
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by have := nW.isLt; omega)
  refine WPs.seqG (fun a => ZeroI s.globals s.memory s.ffi p nW nW.toNat a)
    (WPs.loopG (I := fun a => ∃ j, ZeroI s.globals s.memory s.ffi p nW j a)
      ⟨0, rfl, rfl, rfl, by lk [hp], by lk [hn], by lk [], Nat.zero_le _,
        fun k hk => absurd hk (Nat.not_lt_zero _)⟩ ?_ ?_) ?_
  · rintro a ⟨j, hg, hm, hf, hP, hN, hI, hjn, hz⟩ ⟨w, c, hcond, hw⟩
    have hc := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hI]))
      (of_eval (w := nW) (by lk [hN])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hlt : j < nW.toNat := by
      by_contra hge
      have hnl : ¬ (BitVec.ofNat 64 j : Word) < nW := by
        rw [BitVec.lt_def, hjt j hjn]
        exact hge
      rw [hc] at hw
      simp [evalPanCmp, hnl] at hw
    cases hlb : E.eval a (.loadByte (.op .add [.var .local "p", .var .local "i"])) with
    | none =>
      refine WPs.seqG (fun _ => False) (WPs.ite_both (fun w' hw' => ?_)) (fun _ hF => hF.elim)
      simp [evalF_cmp hE.word, hlb] at hw'
    | some y =>
      obtain ⟨addr, cell, ha, hcell, rfl⟩ := eval_loadByte hE.mem hlb
      rw [eval_off0 hE hP hI] at ha
      simp only [Option.some.injEq, PanValue.word.injEq] at ha
      subst ha
      rw [hE.bytes, hm] at hcell
      have hbyte : byteAt s.memory (off p j) =
          some (RiscV.panRiscVGetByte E.bytesInWord (off p j) cell) := by
        unfold byteAt
        rw [hcell, hE.bytes]
      by_cases hx : RiscV.panRiscVGetByte E.bytesInWord (off p j) cell = 0#64
      · refine WPs.guard0 (fun y hy => by
          rw [eval_cmp_inv hE (of_eval hlb) (of_eval (eval_const _ _)) y hy]
          simp [evalPanCmp, hx]) ?_
        refine WPs.assign (old := BitVec.ofNat 64 j) hI
          (of_eval (w := BitVec.ofNat 64 (j + 1)) (by ev [hI, ofNat_succ])) ?_
        refine ⟨j + 1, hg, hm, hf, by lk [hP], by lk [hN], by lk [], by omega, ?_⟩
        intro k hk
        by_cases hkj : k = j
        · subst hkj
          rw [hbyte, hx]
        · exact hz k (by omega)
      · refine WPs.seqG (fun _ => False) ?_ (fun _ hF => hF.elim)
        refine WPs.ite (w := 1#64) (fun y hy => by
          rw [eval_cmp_inv hE (of_eval hlb) (of_eval (eval_const _ _)) y hy]
          simp [evalPanCmp, hx]) ?_
        split
        · rename_i h10
          exact absurd h10 (by decide)
        refine WPs.ret (of_eval (eval_const _ _)) ?_
        exact ⟨_, 0#64, by rw [hg, hm, hf], Or.inr ⟨rfl, j, _, hlt, hbyte, hx⟩⟩
  · rintro a k ⟨j, hg, hm, hf, hP, hN, hI, hjn, hz⟩ hcond
    have hc := eval_cmp_inv hE (op := .lower) (of_eval (w := BitVec.ofNat 64 j) (by lk [hI]))
      (of_eval (w := nW) (by lk [hN])) _ (cond_of_eval hcond)
    simp only [PanValue.word.injEq] at hc
    have hge : nW.toNat ≤ j := by
      by_contra hlt
      have hl : (BitVec.ofNat 64 j : Word) < nW := by
        rw [BitVec.lt_def, hjt j hjn]
        omega
      simp [evalPanCmp, hl] at hc
    have : j = nW.toNat := by omega
    subst this
    exact ⟨hg, hm, hf, hP, hN, hI, hjn, hz⟩
  · rintro a ⟨hg, hm, hf, hP, hN, hI, hjn, hz⟩
    refine WPs.ret (of_eval (eval_const _ _)) ?_
    exact ⟨_, 1#64, by rw [hg, hm, hf], Or.inl ⟨rfl, hz⟩⟩

end InitECandidate.Solver.GuestBound
