import InitECandidate.Solver.GuestBound.SepRules
import InitECandidate.Solver.GuestBound.Gas

/-!
# `charge_gas` as a framed specification

`WPFr` is `WPF` over `WPr`: the postcondition also covers raised results, which
the interpreter loop catches and continues from. `charge_gas_framed` owns the
global `ev` and the two cells `ev + 64` (gas left) and `ev + 184` (gas used);
everything else, in particular the gas fields of the other frames, is in the
frame and so is unchanged.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

instance : Std.Associative Assn.sep := ⟨Assn.sep_assoc⟩
instance : Std.Commutative Assn.sep := ⟨Assn.sep_comm⟩

/-- Either assertion. -/
def Assn.or (P Q : Assn) : Assn := fun h => P h ∨ Q h

variable {σ : Type} {E : Env σ} {s : St σ}

theorem Assn.holds_perm {P P' : Assn} {s : St σ} (h : P.holds s) (e : P = P') : P'.holds s :=
  e ▸ h

theorem Assn.holds_or_left {P Q R : Assn} {s : St σ} (h : (P ⋆ R).holds s) :
    (Assn.or P Q ⋆ R).holds s :=
  Assn.holdsV_mono (Assn.sep_mono (fun _ h => Or.inl h) (fun _ h => h)) h

theorem Assn.holds_or_right {P Q R : Assn} {s : St σ} (h : (Q ⋆ R).holds s) :
    (Assn.or P Q ⋆ R).holds s :=
  Assn.holdsV_mono (Assn.sep_mono (fun _ h => Or.inr h) (fun _ h => h)) h

/-- `WPF` with a postcondition on every result other than `.error`. -/
def WPFr (E : Env σ) (s : St σ) (p : Prog Word) (P : Assn) (Q : Result σ → Assn) : Prop :=
  ∀ R : Assn, (P ⋆ R).holds s → WPr E s p (fun r => (Q r ⋆ R).holds r.st)

theorem WPFr.frame {p : Prog Word} {P : Assn} {Q : Result σ → Assn} (F : Assn)
    (h : WPFr E s p P Q) : WPFr E s p (P ⋆ F) (fun r => Q r ⋆ F) := by
  intro R hR
  rw [Assn.sep_assoc] at hR
  refine WPr.conseq (h (F ⋆ R) hR) (fun r hr => ?_)
  rw [Assn.sep_assoc]
  exact hr

theorem WPFr.conseq {p : Prog Word} {P P' : Assn} {Q Q' : Result σ → Assn}
    (h : WPFr E s p P Q) (hp : ∀ h, P' h → P h) (hq : ∀ r h, Q r h → Q' r h) :
    WPFr E s p P' Q' := by
  intro R hR
  refine WPr.conseq (h R (Assn.holdsV_mono (Assn.sep_mono hp (fun _ h => h)) hR)) (fun r hr => ?_)
  exact Assn.holdsV_mono (Assn.sep_mono (hq r) (fun _ h => h)) hr

/-- The gas fields of the current frame: `ev`, gas left, gas used. -/
def GasCells (e gl used : Word) : Assn :=
  .glob "ev" ↦ .word e ⋆ .mem (e + 64#64) ↦ .word gl ⋆ .mem (e + 184#64) ↦ .word used

/-- `charge_gas(amount)`: raises with nothing changed when the gas left is less
than `amount`, and otherwise moves `amount` from gas left to gas used. -/
theorem charge_gas_framed (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "charge_gas" E.functions = some (parameters, body))
    (s : St σ) (e a gl used : Word) (ha : s.locals "amount" = some (.word a)) :
    WPFr E s body (GasCells e gl used) (fun r => Assn.or
      (⌜gl < a ∧ ∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 4#64)⌝ ⋆ GasCells e gl used)
      (⌜¬ gl < a ∧ ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
        GasCells e (gl - a) (used + a))) := by
  intro R hR r hr
  have h0 : (.glob "ev" ↦ .word e ⋆ .mem (e + 64#64) ↦ .word gl ⋆
      .mem (e + 184#64) ↦ .word used ⋆ R).holds s := Assn.holds_perm hR (by unfold GasCells; ac_rfl)
  have hev := Assn.holds_glob h0
  have h64 : (.mem (e + 64#64) ↦ .word gl ⋆ .glob "ev" ↦ .word e ⋆
      .mem (e + 184#64) ↦ .word used ⋆ R).holds s := Assn.holds_perm h0 (by ac_rfl)
  have hgl := Assn.holds_mem h64
  rcases charge_gas_spec hE parameters body hlookup s r e a hev ha hr with he | ⟨gl', hgl', hc⟩
  · exact Or.inl he
  rw [hgl] at hgl'
  simp only [Option.some.injEq, PanValue.word.injEq] at hgl'
  subst hgl'
  refine Or.inr ?_
  rcases hc with ⟨hlt, l, rfl⟩ | ⟨hge, l, used', hused', rfl⟩
  · refine Assn.holds_or_left ?_
    rw [Assn.sep_assoc]
    exact Assn.holdsV_pure.mpr ⟨⟨hlt, _, _, _, rfl⟩, Assn.holds_congr rfl rfl hR⟩
  · refine Assn.holds_or_right ?_
    rw [Assn.sep_assoc]
    refine Assn.holdsV_pure.mpr ⟨⟨hge, _, _, _, rfl⟩, ?_⟩
    have h1 : (.mem (e + 64#64) ↦ .word (gl - a) ⋆ .glob "ev" ↦ .word e ⋆
        .mem (e + 184#64) ↦ .word used ⋆ R).holds
        (⟨l, s.globals, setCell s.memory (e + 64#64) (gl - a), s.ffi⟩ : St σ) :=
      Assn.holds_setCell h64
    have h184 : (.mem (e + 184#64) ↦ .word used ⋆ .mem (e + 64#64) ↦ .word (gl - a) ⋆
        .glob "ev" ↦ .word e ⋆ R).holds
        (⟨l, s.globals, setCell s.memory (e + 64#64) (gl - a), s.ffi⟩ : St σ) :=
      Assn.holds_perm h1 (by ac_rfl)
    have hu := Assn.holds_mem h184
    dsimp only at hu
    rw [hused'] at hu
    simp only [Option.some.injEq, PanValue.word.injEq] at hu
    subst hu
    have h2 := Assn.holds_setCell (w := used' + a) (l := l) (f := s.ffi) h184
    exact Assn.holds_perm h2 (by unfold GasCells; ac_rfl)

end InitECandidate.Solver.GuestBound
