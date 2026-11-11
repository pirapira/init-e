import Mathlib.Data.Fintype.Option
import InitECandidate.Solver.GuestBound.OrderedLoop
import InitECandidate.Solver.GuestBound.BitMem
import InitECandidate.Solver.GuestBound.GuestShape
import InitECandidate.Solver.GuestBound.RlpHeader
import InitECandidate.Solver.GuestBound.HalvingLoop

/-!
# The loop of `compute_jumpdests`

`while pc <+ n { …; pc = pc + adv }` marks jump destinations in a bitmap. The
body changes only `pc` and, by or-ing one bit into a word, memory. Memory
therefore only gains bits, and between two such changes a returning run
cannot see the same `pc` twice. No assumption on `n` is needed.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem KeepLe.of_error {I : St σ → Prop} {le : St σ → St σ → Prop} {s : St σ} {r : Result σ}
    (h : r.isError = true) : KeepLe I le s r := by
  cases r <;> trivial

theorem restore_isError (x : VarName) (old : Option (PanValue Word)) (r : Result σ) :
    (restorePanValueFfiLocal x old r).isError = r.isError := by
  cases r <;> rfl

namespace Manual

/-- Loop-head states reachable from `s`. -/
def JdInv (s a : St σ) : Prop :=
  a.globals = s.globals ∧ a.ffi = s.ffi ∧ (∀ x, x ≠ "pc" → a.locals x = s.locals x) ∧
    (IsWordVal (a.locals "pc") ∨ a.locals "pc" = s.locals "pc") ∧ MemGe s.memory a.memory

/-- The program counter, when it is a word. -/
def pcCode (a : St σ) : Option Word :=
  match a.locals "pc" with
  | some (.word w) => some w
  | _ => none

theorem pcCode_some {a : St σ} {w : Word} :
    pcCode a = some w ↔ a.locals "pc" = some (.word w) := by
  unfold pcCode
  split
  · rename_i w' h
    rw [h]
    simp
  · rename_i h
    constructor
    · intro h'; cases h'
    · intro h'; exact absurd h' (h w)

noncomputable def jdEnc (a : St σ) : Option Word × Fin (2 ^ 64 * 64 + 1) :=
  (pcCode a, ⟨(bitsOf a.memory).card, Nat.lt_succ_of_le (bitsOf_card_le _)⟩)

theorem jd_inj {s a a' : St σ} (ha : JdInv s a) (ha' : JdInv s a')
    (hle : MemGe a'.memory a.memory) (henc : jdEnc a = jdEnc a') : a = a' := by
  have hpc : pcCode a = pcCode a' := congrArg Prod.fst henc
  have hbits : (bitsOf a.memory).card = (bitsOf a'.memory).card :=
    congrArg (fun p => p.2.val) henc
  have hmem : a'.memory = a.memory := memGe_eq hle (by omega)
  have hpcv : a.locals "pc" = a'.locals "pc" := by
    by_cases hw : ∃ w, a.locals "pc" = some (.word w)
    · obtain ⟨w, hw⟩ := hw
      have : pcCode a' = some w := by rw [← hpc]; exact pcCode_some.mpr hw
      rw [hw, pcCode_some.mp this]
    · by_cases hw' : ∃ w, a'.locals "pc" = some (.word w)
      · obtain ⟨w, hw'⟩ := hw'
        have : pcCode a = some w := by rw [hpc]; exact pcCode_some.mpr hw'
        exact absurd ⟨w, pcCode_some.mp this⟩ hw
      · rcases ha.2.2.2.1 with h | h
        · exact absurd h hw
        · rcases ha'.2.2.2.1 with h' | h'
          · exact absurd h' hw'
          · rw [h, h']
  have hlocals : a.locals = a'.locals := by
    funext x
    by_cases hx : x = "pc"
    · rw [hx]; exact hpcv
    · rw [ha.2.2.1 x hx, ha'.2.2.1 x hx]
  cases a with
  | mk l g mem f =>
    cases a' with
    | mk l' g' mem' f' =>
      simp only at hlocals hmem
      obtain ⟨hg, hf, -, -, -⟩ := ha
      obtain ⟨hg', hf', -, -, -⟩ := ha'
      simp only at hg hf hg' hf'
      rw [hlocals, hg, hf, hg', hf', hmem]

theorem jd_card :
    Fintype.card (Option Word × Fin (2 ^ 64 * 64 + 1)) ≤
      21778071482940061662855013240424286388225 := by
  rw [Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
  have := word_card
  calc (Fintype.card Word + 1) * (2 ^ 64 * 64 + 1) ≤ (2 ^ 64 + 1) * (2 ^ 64 * 64 + 1) :=
        Nat.mul_le_mul_right _ (by omega)
    _ = 21778071482940061662855013240424286388225 := by norm_num

theorem compute_jumpdests.loop0 {σ : Type} {E : Env σ} (hE : GuestEnv E) (b : Nat)
    (hbody : Costs E (loopBody 463 0) b) :
    Costs E (.while (loopGuard 463 0) (loopBody 463 0))
      (21778071482940061662855013240424286388225 * (expCost (loopGuard 463 0) + b + 1)) := by
  revert hbody
  loop_reduce 463 0
  intro hbody fuel s r m _ hrun hne
  refine ⟨?_, trivial⟩
  rw [← stepCost_eq]
  refine Nat.le_trans (Nat.le_add_right m _) (ordered_core (JdInv s)
    (fun x y => MemGe x.memory y.memory) (fun _ _ _ h₁ h₂ => h₁.trans h₂) jdEnc
    (fun a a' ha ha' hle henc => jd_inj ha ha' hle henc) _ jd_card ?_ r hne fuel ∅ s m
    ⟨rfl, rfl, fun _ _ => rfl, Or.inr rfl, MemGe.refl _⟩ hrun
    (by intro code hcode; simp at hcode))
  intro fuel a r n hI hct hrunb hneb
  refine ⟨(hbody fuel a r n trivial hrunb hneb).1, ?_⟩
  obtain ⟨hg, hf, hl, -, hmem⟩ := hI
  obtain ⟨v, kc, hcond, hv⟩ := hct
  obtain ⟨pv, nv, hpcw, -, -⟩ := cmp_inv hE.word (cond_of_eval hcond)
  simp only [eval_local] at hpcw
  rcases dec_run_inv hrunb with herr | ⟨f1, v1, rb1, n1, -, -, hrun1, rfl⟩
  · exact KeepLe.of_error herr
  rcases dec_run_inv hrun1 with herr | ⟨f2, v2, rb2, n2, -, -, hrun2, rfl⟩
  · exact KeepLe.of_error (by rw [restore_isError]; exact herr)
  obtain ⟨f3, r₁, n3, hite, hrest⟩ := seq_run_inv hrun2
  have hmid : match r₁ with
      | .normal l g m f | .continued l g m f =>
          g = a.globals ∧ f = a.ffi ∧
            (∀ x, x ≠ "adv" →
              l x = updatePanValueMap (updatePanValueMap a.locals "op" v1) "adv" v2 x) ∧
            MemGe a.memory m
      | _ => True := by
    rcases ite_run_inv hite with herr | ⟨f4, cv, n4, -, hbranch⟩
    · cases r₁ <;> trivial
    rcases hbranch with ⟨-, hthen⟩ | ⟨-, helse⟩
    · rcases store_word_inv hE.mem hthen with herr | ⟨addr, val, m', ha, hval, rfl, hm⟩
      · cases r₁ <;> trivial
      obtain ⟨va, vb, w, hla, -, hop, rfl⟩ := eval_op2_inv hE.word hval
      obtain ⟨addr', v', ha', hv', hcell⟩ := eval_load_one hE.mem hla
      rw [ha] at ha'
      simp only [Option.some.injEq, PanValue.word.injEq] at ha' hv'
      subst ha' hv'
      simp only [wordOp, Option.some.injEq, List.foldr] at hop
      subst hop
      have hm' := hm _ rfl
      subst hm'
      exact ⟨rfl, rfl, fun _ _ => rfl, setCell_ge hcell⟩
    · have hp := shape_sound (E := E) (fun _ => false) (by intro f h; simp at h) f4 ["adv"] _ _
        r₁ n4 (by decide +kernel) helse
      cases r₁ with
      | normal l g m f =>
        obtain ⟨hg', hm', hf', hl', -⟩ := hp
        simp only at hg' hm' hf'
        subst hg' hm' hf'
        exact ⟨rfl, rfl, fun x hx => hl' x (by simpa using hx), MemGe.refl _⟩
      | continued l g m f =>
        obtain ⟨hg', hm', hf', hl', -⟩ := hp
        simp only at hg' hm' hf'
        subst hg' hm' hf'
        exact ⟨rfl, rfl, fun x hx => hl' x (by simpa using hx), MemGe.refl _⟩
      | _ => trivial
  cases r₁ with
  | normal l g mem f =>
    obtain ⟨hg', hf', hl', hmem'⟩ := hmid
    simp only at hrest
    obtain ⟨n₂, hassign⟩ := hrest
    rcases assign_local_inv hassign with herr | ⟨va, hva, rfl⟩
    · exact KeepLe.of_error (by rw [restore_isError, restore_isError]; exact herr)
    obtain ⟨xa, xb, -, -, rfl⟩ := eval_add hE.word hva
    simp only [restorePanValueFfiLocal, KeepLe]
    refine ⟨⟨hg'.trans hg, hf'.trans hf, ?_, Or.inl ⟨xa + xb, ?_⟩, hmem.trans hmem'⟩, hmem'⟩
    · intro x hx
      by_cases h1 : x = "op"
      · subst h1
        simp [restorePanValueLocal, hl]
      · by_cases h2 : x = "adv"
        · subst h2
          simp [restorePanValueLocal, updatePanValueMap, hl]
        · have := hl' x h2
          simp [restorePanValueLocal, updatePanValueMap, h1, h2, hx] at this ⊢
          rw [this, hl x hx]
    · simp [restorePanValueLocal, updatePanValueMap]
  | continued l g mem f =>
    obtain ⟨hg', hf', hl', hmem'⟩ := hmid
    simp only at hrest
    subst hrest
    simp only [restorePanValueFfiLocal, KeepLe]
    refine ⟨⟨hg'.trans hg, hf'.trans hf, ?_, Or.inl ⟨pv, ?_⟩, hmem.trans hmem'⟩, hmem'⟩
    · intro x hx
      by_cases h1 : x = "op"
      · subst h1
        simp [restorePanValueLocal, hl]
      · by_cases h2 : x = "adv"
        · subst h2
          simp [restorePanValueLocal, updatePanValueMap, hl]
        · have := hl' x h2
          simp [restorePanValueLocal, updatePanValueMap, h1, h2] at this ⊢
          rw [this, hl x hx]
    · have := hl' "pc" (by decide)
      simp [restorePanValueLocal, updatePanValueMap] at this ⊢
      rw [this, hpcw]
  | _ =>
    simp only at hrest
    subst hrest
    simp only [restorePanValueFfiLocal, KeepLe]

end Manual
end InitECandidate.Solver.GuestBound
