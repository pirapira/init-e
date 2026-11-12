import InitECandidate.Solver.GuestBound.ModInvSpec
import InitECandidate.Solver.GuestBound.MontMul

/-!
# The bn254 base field: `fq_inv`

`fq_inv(a) = fq_mul(modinv_bin(a, p), R^3 mod p)`: for a canonical nonzero
`a`, the result `d` is canonical and `d * a * R ≡ R^3 (mod p)` with `R = 2^256`,
which makes `d` the Montgomery inverse of `a`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- `R^3 mod p` for `R = 2^256`. -/
def bnR3 : Nat := 14921786541159648185948152738563080959093619838510245177710943249661917737183

theorem bnR3_limbs : limbsVal [(12812017116984455391#64 : Word), 7129779742913871286#64,
    17257524443456604923#64, 2377177743836652868#64] = bnR3 := by
  decide

set_option exponentiation.threshold 1000 in
theorem bnR3_eq : bnR3 = 2 ^ 768 % bnP := by
  norm_num [bnR3, bnP]

set_option maxHeartbeats 8000000 in
theorem fq_inv_spec (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "fq_inv" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (a0 a1 a2 a3 : Word)
    (ha : s.locals "a" = some (.rStruct [.word a0, .word a1, .word a2, .word a3]))
    (hA : limbsVal [a0, a1, a2, a3] ≠ 0) (h : Runs E s body r) :
    Stopped r ∨ ∃ l d0 d1 d2 d3, r = .returned l s.globals s.memory s.ffi
        [.rStruct [.word d0, .word d1, .word d2, .word d3]] ∧ limbsVal [d0, d1, d2, d3] < bnP ∧
      limbsVal [d0, d1, d2, d3] * limbsVal [a0, a1, a2, a3] * 2 ^ 256 % bnP = bnR3 % bnP := by
  have hbody := (fun_of_index 655 hE.functions (by guest_decl_at 655) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  rcases runs_decCall_inv h with herr | ⟨ps, cb, vals, cl, rb, hl, hvals, hbind, hcal, hout⟩
  · exact Or.inl (Stopped.of_error herr)
  have hparams := (fun_of_index 157 hE.functions (by guest_decl_at 157) (by decide +kernel) hl).2
  simp only [evalArgs_cons, evalArgs_nil, evalF_local, ha, evalF_rStruct, eval_const,
    Option.map_some, Option.some.injEq] at hvals
  subst hvals
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  rcases modinv_bin_spec hE ps cb hl ⟨cl, s.globals, s.memory, s.ffi⟩ rb a0 a1 a2 a3
    4332616871279656263#64 10917124144477883021#64 13281191951274694749#64 3486998266802970665#64
    (by rw [← hbind]; simp [updatePanValueMap]) (by rw [← hbind]; simp [updatePanValueMap]) hA
    (by rw [bnP_limbs]; decide) (by rw [bnP_limbs]; decide) hcal with hst | hret
  · cases rb with
    | raised lr g m f ex v =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only at hout
      subst hout
      exact Or.inl trivial
    | error lr g m f => exact hout.elim
    | _ => exact absurd hst (fun h => h)
  obtain ⟨lr, i0, i1, i2, i3, rfl, hIlt, hIinv⟩ := hret
  rw [bnP_limbs] at hIlt hIinv
  obtain ⟨r1, -, hrun1, rfl⟩ := hout
  rcases runs_call_inv none hrun1 with herr | ⟨ps2, cb2, vals2, cl2, rb2, hl2, hvals2, hbind2,
    hcal2, hout2⟩
  · exact Or.inl (Stopped.restore (Stopped.of_error herr))
  have hparams2 := (fun_of_index 652 hE.functions (by guest_decl_at 652) (by decide +kernel)
    hl2).2
  simp (config := { decide := true }) only [evalArgs_cons, evalArgs_nil, evalF_local,
    update_lookup, evalF_rStruct, eval_const, Option.map_some, Option.some.injEq,
    if_true] at hvals2
  subst hvals2
  rw [hparams2] at hbind2
  simp [bindPanValueParameters] at hbind2
  rcases fq_mul_spec hE ps2 cb2 hl2 ⟨cl2, s.globals, s.memory, s.ffi⟩ rb2 i0 i1 i2 i3
    12812017116984455391#64 7129779742913871286#64 17257524443456604923#64 2377177743836652868#64
    (by rw [← hbind2]; simp [updatePanValueMap]) (by rw [← hbind2]; simp [updatePanValueMap]) hIlt
    (by rw [bnR3_limbs]; decide) hcal2 with hst | ⟨l2, d0, d1, d2, d3, rfl, hdlt, hd⟩
  · cases rb2 with
    | raised lr g m f ex v =>
      simp only [CallOutcome] at hout2
      subst hout2
      exact Or.inl trivial
    | finalFfi lr g m f ev =>
      simp only [CallOutcome] at hout2
      subst hout2
      exact Or.inl trivial
    | error lr g m f =>
      simp only [CallOutcome] at hout2
      exact Or.inl (Stopped.restore (Stopped.of_error hout2))
    | _ => exact absurd hst (fun h => h)
  simp only [CallOutcome] at hout2
  rcases hout2 with herr | ⟨l', rfl⟩
  · exact Or.inl (Stopped.restore (Stopped.of_error herr))
  refine Or.inr ⟨_, d0, d1, d2, d3, rfl, hdlt, ?_⟩
  rw [bnR3_limbs] at hd
  -- d * R ≡ i * C and i * a ≡ 1, so d * a * R ≡ C
  have h1 : limbsVal [d0, d1, d2, d3] * 2 ^ 256 ≡ limbsVal [i0, i1, i2, i3] * bnR3 [MOD bnP] := hd
  have h2 : limbsVal [i0, i1, i2, i3] * limbsVal [a0, a1, a2, a3] ≡ 1 [MOD bnP] := hIinv
  have h3 : limbsVal [d0, d1, d2, d3] * limbsVal [a0, a1, a2, a3] * 2 ^ 256 ≡ bnR3 [MOD bnP] := by
    calc limbsVal [d0, d1, d2, d3] * limbsVal [a0, a1, a2, a3] * 2 ^ 256
        = limbsVal [d0, d1, d2, d3] * 2 ^ 256 * limbsVal [a0, a1, a2, a3] := by ring
      _ ≡ limbsVal [i0, i1, i2, i3] * bnR3 * limbsVal [a0, a1, a2, a3] [MOD bnP] :=
          h1.mul_right _
      _ = limbsVal [i0, i1, i2, i3] * limbsVal [a0, a1, a2, a3] * bnR3 := by ring
      _ ≡ 1 * bnR3 [MOD bnP] := h2.mul_right _
      _ = bnR3 := Nat.one_mul _
  exact h3

end InitECandidate.Solver.GuestBound
