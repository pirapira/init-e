import InitECandidate.Solver.GuestBound.Wpr

/-!
# Gas accounting of the current frame

The interpreter keeps the gas of the current frame in memory, in the record
`ev` points at: regular gas left at `ev + 64` (`EV_GAS_LEFT`) and regular gas
used at `ev + 184` (`EV_REGULAR_GAS_USED`). `charge_gas_spec` says exactly
what `charge_gas` does to those two cells, including the state it leaves when
it raises `EvmErr`. First step of the `run_frames` iteration bound (#9).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- What `charge_gas(a)` leaves for the frame record at `e`: with less than `a`
regular gas it raises `EvmErr 4` (out of gas) and changes nothing; otherwise it
returns 0 with `a` moved from the gas left to the gas used. -/
def ChargePost (s : St σ) (e a : Word) (r : Result σ) : Prop :=
  ∃ gl : Word, s.memory (e + 64#64) = some (.word gl) ∧
    ((gl < a ∧ ∃ l, r = .raised l s.globals s.memory s.ffi "EvmErr" (.word 4#64)) ∨
      (¬ gl < a ∧ ∃ l, ∃ used : Word,
        setCell s.memory (e + 64#64) (gl - a) (e + 184#64) = some (.word used) ∧
        r = .returned l s.globals
          (setCell (setCell s.memory (e + 64#64) (gl - a)) (e + 184#64) (used + a)) s.ffi
          [.word 0#64]))

theorem charge_gas_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "charge_gas" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (e a : Word) (hev : s.globals "ev" = some (.word e))
    (ha : s.locals "amount" = some (.word a)) (h : Runs E s body r) :
    r.isError = true ∨ ChargePost s e a r := by
  have hbody := (fun_of_index 448 hE.functions (by guest_decl_at 448) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  refine (?_ : WPr E s _ (ChargePost s e a)) r h
  refine WPr.dec_ev (fun v hv => ?_)
  obtain ⟨addr, gl, haddr, rfl, hmem⟩ := eval_load_one hE.mem hv
  have h64 : E.eval s (.op .add [.var .global "ev", .const 64#64]) = some (.word (e + 64#64)) := by
    ev [eval_global, hev]
  rw [h64] at haddr
  simp only [Option.some.injEq, PanValue.word.injEq] at haddr
  subst haddr
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap s.locals "gl" (.word gl), s.globals, s.memory,
      s.ffi⟩ ∧ ¬ gl < a) (WPr.ite_both (fun w hw => ?_)) ?_
  · have hcv := eval_cmp_inv hE (op := .lower) (of_eval (w := gl) (by lk []))
      (of_eval (w := a) (by lk [ha])) _ hw
    simp only [PanValue.word.injEq] at hcv
    split
    · rename_i h0
      rw [h0] at hcv
      exact WPr.skip ⟨rfl, lower_zero hcv.symm⟩
    · rename_i h0
      refine WPr.raise (fun v hv => ?_)
      rw [eval_const] at hv
      cases hv
      simp only [restorePanValueFfiLocal]
      refine ⟨gl, hmem, Or.inl ⟨?_, _, rfl⟩⟩
      by_contra hlt
      exact h0 (by rw [hcv]; simp [evalPanCmp, hlt])
  rintro _ ⟨rfl, hge⟩
  refine WPr.seq (fun s' => s' = ⟨updatePanValueMap s.locals "gl" (.word gl), s.globals,
      setCell s.memory (e + 64#64) (gl - a), s.ffi⟩)
    (WPr.store hE (addr := e + 64#64) (w := gl - a) (by ev [eval_global, hev])
      (of_eval (by ev [ha])) rfl) ?_
  rintro _ rfl
  refine WPr.seq (fun s' => ∃ used : Word,
      setCell s.memory (e + 64#64) (gl - a) (e + 184#64) = some (.word used) ∧
      s' = ⟨updatePanValueMap s.locals "gl" (.word gl), s.globals,
        setCell (setCell s.memory (e + 64#64) (gl - a)) (e + 184#64) (used + a), s.ffi⟩)
    (WPr.store_ev hE (addr := e + 184#64) (by ev [eval_global, hev]) (fun y hy => ?_)) ?_
  · obtain ⟨va, vb, w, hva, hvb, hw, rfl⟩ := eval_op2_inv hE.word hy
    obtain ⟨addr, used, haddr, hu, hmem2⟩ := eval_load_one hE.mem hva
    have h184 : E.eval ⟨updatePanValueMap s.locals "gl" (.word gl), s.globals,
        setCell s.memory (e + 64#64) (gl - a), s.ffi⟩
        (.op .add [.var .global "ev", .const 184#64]) = some (.word (e + 184#64)) := by
      ev [eval_global, hev]
    rw [h184] at haddr
    simp only [Option.some.injEq, PanValue.word.injEq] at haddr hu
    subst haddr hu
    have hb : vb = a := by
      have : E.eval ⟨updatePanValueMap s.locals "gl" (.word gl), s.globals,
          setCell s.memory (e + 64#64) (gl - a), s.ffi⟩ (.var .local "amount") =
          some (.word a) := by lk [ha]
      rw [this] at hvb
      simpa using hvb.symm
    subst hb
    refine ⟨w, rfl, va, hmem2, ?_⟩
    simp [wordOp] at hw
    rw [← hw]
  rintro _ ⟨used, hused, rfl⟩
  refine WPr.ret (w := 0#64) (of_eval (eval_const _ _)) ?_
  simp only [restorePanValueFfiLocal]
  exact ⟨gl, hmem, Or.inr ⟨hge, _, used, hused, rfl⟩⟩

end InitECandidate.Solver.GuestBound
