import InitECandidate.Solver.GuestBound.PureLoop

/-! # Iteration bound for pure counter loops -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The first `i = i + k` assignment in a loop body. -/
def findStep : Prog Word → Option (VarName × Word)
  | .assign .local name (.op .add [.var .local name', .const k]) =>
      if name == name' then some (name, k) else none
  | .seq first second =>
      match findStep first with
      | some found => some found
      | none => findStep second
  | .ite _ thenBranch elseBranch =>
      match findStep thenBranch with
      | some found => some found
      | none => findStep elseBranch
  | .dec _ _ _ body => findStep body
  | .decCall _ _ _ _ body => findStep body
  | _ => none

/-- The body changes only one local, by a constant step on every way back to the loop head. -/
def pureLoop (body : Prog Word) : Bool :=
  match findStep body with
  | some (i, k) => frameOk k i body && stepsBack (effect (.upBy k) i body)
  | none => false

theorem stepN_succ (k : Word) (t : Nat) (w : Word) : stepN k (t + 1) w = stepN k t w + k := by
  rw [stepN_eq, stepN_eq]
  have : BitVec.ofNat 64 (t + 1) = BitVec.ofNat 64 t + 1 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [this]
  ring

/-- A pure counter loop costs at most `2^64` iterations of its guard and body. -/
theorem pureLoop_costs (hE : WordEnv E) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : pureLoop body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold pureLoop at hcheck
  split at hcheck
  · rename_i i k hfind
    simp only [Bool.and_eq_true] at hcheck
    obtain ⟨hframe, hback⟩ := hcheck
    simp only [stepsBack, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hback
    unfold Costs Triple
    intro fuel s r m _ hrun hne
    refine ⟨?_, trivial⟩
    rw [← stepCost_eq]
    by_cases hw : ∃ w, s.locals i = some (.word w)
    · obtain ⟨w, hw⟩ := hw
      let S : Nat → St σ := fun t =>
        ⟨updatePanValueMap s.locals i (.word (stepN k t w)), s.globals, s.memory, s.ffi⟩
      have hsame : updatePanValueMap s.locals i (.word w) = s.locals := by
        funext x
        simp only [updatePanValueMap]
        split
        · rename_i h
          have hx : x = i := by simpa using h
          subst hx
          exact hw.symm
        · rfl
      have hS0 : S 0 = s := by
        show (⟨updatePanValueMap s.locals i (.word (stepN k 0 w)), s.globals, s.memory, s.ffi⟩ :
          St σ) = s
        simp only [stepN, hsame]
      have hper : S (2 ^ 64) = S 0 := by
        have h := stepN_mod k (2 ^ 64) w
        rw [Nat.mod_self] at h
        show (⟨updatePanValueMap s.locals i (.word (stepN k (2 ^ 64) w)), s.globals, s.memory,
          s.ffi⟩ : St σ) = ⟨updatePanValueMap s.locals i (.word (stepN k 0 w)), s.globals,
          s.memory, s.ffi⟩
        rw [h]
      have hnext : ∀ t fuel l g mem f nb,
          (E.run fuel (S t) body = some (.normal l g mem f, nb) ∨
            E.run fuel (S t) body = some (.continued l g mem f, nb)) →
          (⟨l, g, mem, f⟩ : St σ) = S (t + 1) := by
        intro t fuel l g mem f nb h
        have key : g = s.globals ∧ mem = s.memory ∧ f = s.ffi ∧
            (∀ x, x ≠ i → l x = (S t).locals x) ∧
            l i = some (.word (stepN k t w + k)) := by
          have hSi : (S t).locals i = some (.word (stepN k t w)) := by
            simp [S, updatePanValueMap]
          rcases h with h | h
          · have fr := frame_sound hE k i fuel body (S t) _ nb hframe h
            have ef := effect_sound hE (.upBy k) i fuel body (S t) _ nb h
            simp only [Frame] at fr
            simp only [PostR] at ef
            obtain ⟨hg, hm, hf, hl, -⟩ := fr
            refine ⟨hg, hm, hf, hl, ?_⟩
            rcases hback.1 with he | he
            · rw [he] at ef
              exact ef _ hSi
            · rw [he] at ef
              exact ef.elim
          · have fr := frame_sound hE k i fuel body (S t) _ nb hframe h
            have ef := effect_sound hE (.upBy k) i fuel body (S t) _ nb h
            simp only [Frame] at fr
            simp only [PostR] at ef
            obtain ⟨hg, hm, hf, hl, -⟩ := fr
            refine ⟨hg, hm, hf, hl, ?_⟩
            rcases hback.2 with he | he
            · rw [he] at ef
              exact ef _ hSi
            · rw [he] at ef
              exact ef.elim
        obtain ⟨hg, hm, hf, hl, hi⟩ := key
        show (⟨l, g, mem, f⟩ : St σ) =
          ⟨updatePanValueMap s.locals i (.word (stepN k (t + 1) w)), s.globals, s.memory, s.ffi⟩
        have hlocals : l = updatePanValueMap s.locals i (.word (stepN k (t + 1) w)) := by
          funext x
          by_cases hx : x = i
          · subst hx
            rw [hi, stepN_succ]
            simp [updatePanValueMap]
          · have hx' : (x == i) = false := by simpa using hx
            rw [hl x hx]
            simp [S, updatePanValueMap, hx']
        rw [hlocals, hg, hm, hf]
      have hrun' : E.run fuel (S 0) (.while c body) = some (r, m) := by rw [hS0]; exact hrun
      exact orbit_bound S (condCost (fun _ => True) c) hbody hnext hper fuel r m hrun' hne
    · have hnext : ∀ (t : Nat) fuel l g mem f nb,
          (E.run fuel ((fun _ : Nat => s) t) body = some (.normal l g mem f, nb) ∨
            E.run fuel ((fun _ : Nat => s) t) body = some (.continued l g mem f, nb)) →
          (⟨l, g, mem, f⟩ : St σ) = (fun _ : Nat => s) (t + 1) := by
        intro t fuel l g mem f nb h
        have key : g = s.globals ∧ mem = s.memory ∧ f = s.ffi ∧ (∀ x, x ≠ i → l x = s.locals x) ∧
            (l i = s.locals i ∨ ∃ w, s.locals i = some (.word w)) := by
          rcases h with h | h
          · have fr := frame_sound hE k i fuel body s _ nb hframe h
            simpa only [Frame] using fr
          · have fr := frame_sound hE k i fuel body s _ nb hframe h
            simpa only [Frame] using fr
        obtain ⟨hg, hm, hf, hl, hi⟩ := key
        have hi' : l i = s.locals i := by
          rcases hi with h | h
          · exact h
          · exact absurd h hw
        have hlocals : l = s.locals := by
          funext x
          by_cases hx : x = i
          · subst hx; exact hi'
          · exact hl x hx
        show (⟨l, g, mem, f⟩ : St σ) = s
        rw [hlocals, hg, hm, hf]
      exact orbit_bound (fun _ : Nat => s) (condCost (fun _ => True) c) hbody hnext rfl fuel r m
        hrun hne
  · cases hcheck

end InitECandidate.Solver.GuestBound
