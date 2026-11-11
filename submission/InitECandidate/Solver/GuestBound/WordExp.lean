import InitECandidate.Solver.GuestBound.WalkLoopBound

/-! # Expressions whose value, when they evaluate, is a word -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Syntactically word-valued expressions. -/
def wordExp : Exp Word → Bool
  | .const _ | .op _ _ | .cmp _ _ _ | .shift _ _ _ | .load .one _ | .load32 _
  | .loadByte _ => true
  | _ => false

theorem flatLoadFuel_one {structs : StructContext} {readWord : Word → Option Word}
    {bytesInWord address : Word} {v : PanValue Word} :
    ∀ fuel, panValueFlatLoadFuel structs readWord bytesInWord fuel .one address = some v →
      ∃ w, v = .word w := by
  intro fuel h
  cases fuel with
  | zero => simp [panValueFlatLoadFuel] at h
  | succ fuel =>
    simp only [panValueFlatLoadFuel, Option.map_eq_some_iff] at h
    obtain ⟨w, -, rfl⟩ := h
    exact ⟨w, rfl⟩

/-- A syntactically word-valued expression evaluates to a word. -/
theorem wordExp_eval (hE : WordEnv E) {s : St σ} {e : Exp Word} {v : PanValue Word}
    (hw : wordExp e = true)
    (h : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress E.topAddress
      E.bytesInWord e E.memoryAccess = some v) : ∃ w, v = .word w := by
  obtain ⟨access, hacc, -, -, -⟩ := hE.access
  rw [hacc] at h
  cases e with
  | const value =>
    simp only [evalPanValueExp, Option.some.injEq] at h
    exact ⟨value, h.symm⟩
  | op operator arguments =>
    simp only [evalPanValueExp, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨_, _, _, _, w, -, rfl⟩ := h
    exact ⟨w, rfl⟩
  | cmp operator left right =>
    simp only [evalPanValueExp, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨lv, -, rv, -, h⟩ := h
    cases lv <;> cases rv <;> simp at h
    exact ⟨_, h.symm⟩
  | shift operator left right =>
    simp only [evalPanValueExp, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨lv, -, rv, -, h⟩ := h
    cases lv <;> cases rv <;> simp at h
    obtain ⟨w, -, rfl⟩ := h
    exact ⟨w, rfl⟩
  | load shape address =>
    cases shape with
    | one =>
      simp only [evalPanValueExp, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨av, -, h⟩ := h
      cases av <;> simp at h
      unfold panValueFlatLoad at h
      split at h
      · exact flatLoadFuel_one _ h
      · cases h
    | _ => simp [wordExp] at hw
  | load32 address =>
    simp only [evalPanValueExp, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨av, -, h⟩ := h
    cases av <;> simp at h
    obtain ⟨w, -, rfl⟩ := h
    exact ⟨w, rfl⟩
  | loadByte address =>
    simp only [evalPanValueExp, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨av, -, h⟩ := h
    cases av <;> simp at h
    obtain ⟨w, -, rfl⟩ := h
    exact ⟨w, rfl⟩
  | _ => simp [wordExp] at hw

end InitECandidate.Solver.GuestBound
