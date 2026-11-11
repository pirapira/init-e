import InitECandidate.Solver.GuestBound.CounterCheck
import InitECandidate.Solver.GuestBound.Call

/-!
# Soundness of the local-variable effect analysis

`effect_sound`: whatever a program does, on each kind of exit the tracked
local `i` has changed as `effect mode i p` says. It holds for environments
whose word operations are the standard ones and whose external calls cannot
touch locals (`WordEnv`).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- Environments with a memory-access model whose word arithmetic is the
standard one, and without an accelerator handler (so external calls leave
locals alone). -/
structure WordEnv {σ : Type} (E : Env σ) : Prop where
  noMemoryHandler : E.memoryHandler = none
  access : ∃ access, E.memoryAccess = some access ∧
    (∀ a b, access.wordOp .add [a, b] = some (a + b)) ∧
    (∀ a b, access.wordOp .sub [a, b] = some (a - b)) ∧
    (∀ operator a b, access.compare operator a b = evalPanCmp operator a b)

def stepWord : Mode → Word → Word
  | .up, w => w + 1
  | .down, w => w - 1

/-- What an abstract effect says about the locals `l` at one exit, given the
value `v` the tracked local had at entry. -/
def Post (mode : Mode) (i : VarName) (v : Option (PanValue Word)) :
    Eff → (VarName → Option (PanValue Word)) → Prop
  | .unreach, _ => False
  | .keep, l => ∀ w, v = some (.word w) → l i = some (.word w)
  | .step, l => ∀ w, v = some (.word w) → l i = some (.word (stepWord mode w))
  | .bad, _ => True

/-- `Post` at the exit a result takes. -/
def PostR {σ : Type} (mode : Mode) (i : VarName) (v : Option (PanValue Word)) (e : Effs) :
    Result σ → Prop
  | .normal l _ _ _ => Post mode i v e.normal l
  | .continued l _ _ _ => Post mode i v e.continued l
  | .broke l _ _ _ => Post mode i v e.broke l
  | _ => True

section algebra
variable {mode : Mode} {i : VarName} {v : Option (PanValue Word)}
  {l l₁ l₂ : VarName → Option (PanValue Word)}

theorem Post.comp {a b : Eff} (h₁ : Post mode i v a l₁) (h₂ : Post mode i (l₁ i) b l₂) :
    Post mode i v (a.comp b) l₂ := by
  cases a <;> cases b <;> simp only [Eff.comp, Post] at * <;>
    first
      | exact fun w hw => h₂ w (h₁ w hw)
      | exact fun w hw => h₂ _ (h₁ w hw)

theorem Post.join_left {a : Eff} (b : Eff) (h : Post mode i v a l) :
    Post mode i v (a.join b) l := by
  cases a <;> cases b <;> simp only [Eff.join, Post] at * <;> exact h

theorem Post.join_right (a : Eff) {b : Eff} (h : Post mode i v b l) :
    Post mode i v (a.join b) l := by
  cases a <;> cases b <;> simp only [Eff.join, Post] at * <;> exact h

theorem Post.of_quiet {a : Eff} (hq : a.quiet = true) (h : Post mode i v a l) :
    ∀ w, v = some (.word w) → l i = some (.word w) := by
  cases a <;> simp only [Eff.quiet, Post] at * <;> first | exact h | cases hq | cases h

theorem Post.restore_same {a : Eff} {v' : Option (PanValue Word)} (h : Post mode i v' a l) :
    Post mode i v a.restore (restorePanValueLocal l i v) := by
  cases a <;> simp only [Eff.restore, Post] at * <;>
    first
      | exact fun w hw => by simp [restorePanValueLocal, hw]
      | exact h

theorem Post.restore_other {a : Eff} {name : VarName} {old : Option (PanValue Word)}
    (hne : (i == name) = false) (h : Post mode i v a l) :
    Post mode i v a (restorePanValueLocal l name old) := by
  cases a <;> simp only [Post, restorePanValueLocal, hne] at * <;> exact h

end algebra

section results
variable {σ : Type} {mode : Mode} {i : VarName} {v : Option (PanValue Word)}

theorem PostR.bad (r : Result σ) : PostR mode i v Effs.bad r := by
  cases r <;> simp [PostR, Effs.bad, Post]

theorem PostR.seq_second {a b : Effs} {l₁ : VarName → Option (PanValue Word)} {r : Result σ}
    (h₁ : Post mode i v a.normal l₁) (h₂ : PostR mode i (l₁ i) b r) :
    PostR mode i v ⟨a.normal.comp b.normal, a.continued.join (a.normal.comp b.continued),
      a.broke.join (a.normal.comp b.broke)⟩ r := by
  cases r <;> simp only [PostR] at * <;>
    first
      | exact Post.comp h₁ h₂
      | exact Post.join_right _ (Post.comp h₁ h₂)

theorem PostR.join_left {a : Effs} (b : Effs) {r : Result σ} (h : PostR mode i v a r) :
    PostR mode i v ⟨a.normal.join b.normal, a.continued.join b.continued, a.broke.join b.broke⟩
      r := by
  cases r <;> simp only [PostR] at * <;> exact Post.join_left _ h

theorem PostR.join_right (a : Effs) {b : Effs} {r : Result σ} (h : PostR mode i v b r) :
    PostR mode i v ⟨a.normal.join b.normal, a.continued.join b.continued, a.broke.join b.broke⟩
      r := by
  cases r <;> simp only [PostR] at * <;> exact Post.join_right _ h

theorem PostR.restore_same {a : Effs} {v' : Option (PanValue Word)} {r : Result σ}
    (h : PostR mode i v' a r) :
    PostR mode i v ⟨a.normal.restore, a.continued.restore, a.broke.restore⟩
      (restorePanValueFfiLocal i v r) := by
  cases r <;> simp only [PostR, restorePanValueFfiLocal] at * <;> exact Post.restore_same h

theorem PostR.restore_other {a : Effs} {name : VarName} {old : Option (PanValue Word)}
    {r : Result σ} (hne : (i == name) = false) (h : PostR mode i v a r) :
    PostR mode i v a (restorePanValueFfiLocal name old r) := by
  cases r <;> simp only [PostR, restorePanValueFfiLocal] at * <;> exact Post.restore_other hne h

end results

end InitECandidate.Solver.GuestBound
