import InitECandidate.Solver.GuestBound.KeyNibblesSeg
import InitECandidate.Solver.GuestBound.TrieFreeze

/-!
# `key_to_nibbles` against the world invariant

Writing the nibbles of a key into a registered buffer `[lo, hi)` keeps the
world invariant and leaves a nibble array there. After `WorldTJ.freeze` the
array can serve as the segment of a new leaf or extension.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem key_to_nibbles_world (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "key_to_nibbles" E.functions = some (parameters, body))
    (Rg : Reg) (s : St σ) (r : Result σ) (kw nw ow0 lo hi : Word)
    (hk : s.locals "key" = some (.word kw)) (hn : s.locals "n" = some (.word nw))
    (ho : s.locals "out" = some (.word ow0)) (hW : WorldTJ Rg s.globals s.memory)
    (hb : Rg.B lo hi) (h8 : lo.toNat % 8 = 0) (h1 : lo.toNat ≤ ow0.toNat)
    (h2 : ow0.toNat + 2 * nw.toNat ≤ hi.toNat)
    (hcn : ∀ x w, Rg.Cn x w → ¬ (lo.toNat ≤ x.toNat ∧ x.toNat < hi.toNat))
    (h : Runs E s body r) :
    Stopped r ∨ ∃ l m, r = .returned l s.globals m s.ffi [.word 0#64] ∧
      WorldTJ Rg s.globals m ∧ Nibs m ow0 (2 * nw.toNat) ∧
      ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m a = s.memory a := by
  have hbnd : HBASE ≤ lo.toNat ∧ hi.toNat ≤ 2952790016 := by
    obtain ⟨pv, T, N, J, C, n, hp, hpH, hJg, hCg, hng, hHW, hD, hB, hCn, hNd, hIm⟩ := hW
    have hf := hB lo hi hb
    have := hf.lo_
    have := hf.hi_
    have := hpH.1
    exact ⟨by omega, by omega⟩
  obtain ⟨hlo, hhi⟩ := hbnd
  rcases key_to_nibbles_nib hE parameters body hlookup s r kw nw ow0 hk hn ho (by omega) h with
    hs | ⟨l, m, rfl, -, hnb, hfr⟩
  · exact Or.inl hs
  have hout : ∀ a : Word, (a.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ a.toNat) → m a = s.memory a := by
    intro a ha
    refine hfr a ?_
    rcases ha with ha | ha
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  refine Or.inr ⟨l, m, rfl, hW.write_free hb (fun a ha8 hni _ => hfr a ?_) hout hcn, hnb, hout⟩
  by_cases hlt : a.toNat < lo.toNat
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

end InitECandidate.Solver.GuestBound
