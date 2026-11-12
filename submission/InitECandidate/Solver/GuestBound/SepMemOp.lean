import InitECandidate.Solver.GuestBound.ChargeMem
import InitECandidate.Solver.GuestBound.Dispatch

/-!
# The frame invariant with the memory buffer

`MemExtra e Y` is the EVM memory buffer of the frame and its three fields. It
sits next to `FrameOp` (the stack rules treat it as part of their frame).
`HandlerQM` is `HandlerQ` with the buffer state and `frame_mem_ptr` allowed to
change, which is what handlers that grow memory need. `op_charge_mem` is the
step rule for `charge_with_memory(…)`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- The frame fields beyond the stack: the memory buffer's three fields, the
running flag, and the return-data pointer and length. -/
structure MemSt where
  len : Word
  cap : Word
  mem : Word
  run : Word
  rd : Word
  rl : Word

/-- The cells of `MemSt` other than the buffer itself. -/
def MemTail (e : Word) (Y : MemSt) : Assn :=
  .mem (e + 32#64) ↦ .word Y.len ⋆ .mem (e + 40#64) ↦ .word Y.cap ⋆
    .mem (e + 24#64) ↦ .word Y.mem ⋆ .mem (e + 104#64) ↦ .word Y.run ⋆
    .mem (e + 120#64) ↦ .word Y.rd ⋆ .mem (e + 128#64) ↦ .word Y.rl

/-- The memory buffer and the cells of `MemSt`. -/
def MemExtra (e : Word) (Y : MemSt) : Assn :=
  Assn.Range Y.mem (Y.mem + Y.cap) ⋆ MemTail e Y

/-- The pure side for the memory buffer: aligned, length a multiple of 32, and
the buffer ends at `frame_mem_ptr`. -/
structure MBufOk (Y : MemSt) (fv : Word) : Prop where
  mal : Y.mem.toNat % 8 = 0
  cal : Y.cap.toNat % 8 = 0
  l32 : Y.len.toNat % 32 = 0
  lc : Y.len.toNat ≤ Y.cap.toNat
  top : Y.mem.toNat + Y.cap.toNat = fv.toNat

/-- `FrameOp` without what `charge_with_memory` touches. -/
def RestCM (M : Word) (K : Word → Prop) (e : Word) (X : OpSt) (run rd rl : Word) : Assn :=
  Assn.Range X.base (X.base + 32#64 * X.cap) ⋆ .mem (e + 16#64) ↦ .word X.sp ⋆
    .mem (e + 232#64) ↦ .word X.cap ⋆ .mem (e + 8#64) ↦ .word X.base ⋆ .mem e ↦ .word X.pc ⋆
    JunkW M K X.pv X.base X.cap ⋆ .mem (e + 104#64) ↦ .word run ⋆
    .mem (e + 120#64) ↦ .word rd ⋆ .mem (e + 128#64) ↦ .word rl

theorem FrameM_cmw (M : Word) (K : Word → Prop) (e fv : Word) (X : OpSt) (Y : MemSt) :
    (FrameOp M K e fv X ⋆ MemExtra e Y) =
      (CMW e Y.len Y.cap Y.mem X.pv fv X.gl X.used ⋆ RestCM M K e X Y.run Y.rd Y.rl) := by
  unfold FrameOp OpW StackW MemExtra MemTail CMW MemW RestCM
  ac_rfl

/-- The handler stopped early, with the buffer state and `frame_mem_ptr` free to differ. -/
def AbortM (M : Word) (K : Word → Prop) (e : Word) (R : Assn) (ffi : FfiState σ) (X0 : OpSt)
    (r : Result σ) : Prop :=
  Trap r ∨ ∃ fv X Y n, FrameOk M K fv X ∧ MBufOk Y fv ∧ Adv X X0 n ∧
    (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds r.st ∧
    ∃ l g m v, r = .raised l g m ffi "EvmErr" v

/-- What a handler guarantees, at the level of the frame with its memory buffer. -/
def HandlerQM (M : Word) (K : Word → Prop) (e : Word) (R : Assn) (ffi : FfiState σ)
    (X0 : OpSt) (r : Result σ) : Prop :=
  AbortM M K e R ffi X0 r ∨ ∃ fv X Y n, FrameOk M K fv X ∧ MBufOk Y fv ∧ Adv X X0 n ∧
    (0 < n ∨ Y.run = 0#64) ∧
    (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds r.st ∧
    ∃ l g m, r = .returned l g m ffi [.word 0#64]

/-- A stack-level outcome is a memory-level one. -/
theorem HandlerQ.toM {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {ffi : FfiState σ}
    {X0 : OpSt} {Y : MemSt} (hY : MBufOk Y fv) {r : Result σ}
    (h : HandlerQ M K e fv (MemExtra e Y ⋆ R) ffi X0 r) : HandlerQM M K e R ffi X0 r := by
  rcases h with (ht | ⟨X, n, hok, hp, hh, hex⟩) | ⟨X, n, hok, hp, hn, hh, hex⟩
  · exact Or.inl (Or.inl ht)
  · exact Or.inl (Or.inr ⟨fv, X, Y, n, hok, hY, hp, hh, hex⟩)
  · exact Or.inr ⟨fv, X, Y, n, hok, hY, hp, Or.inl hn, hh, hex⟩

theorem HandlerQM.restore {M : Word} {K : Word → Prop} {e : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} {x : VarName} {old : Option (PanValue Word)} {r : Result σ}
    (h : HandlerQM M K e R ffi X0 r) :
    HandlerQM M K e R ffi X0 (restorePanValueFfiLocal x old r) := by
  rcases h with (ht | ⟨fv, X, Y, n, hok, hY, hp, hh, hex⟩) |
    ⟨fv, X, Y, n, hok, hY, hp, hn, hh, hex⟩
  · exact Or.inl (Or.inl ht.restore)
  · refine Or.inl (Or.inr ⟨fv, X, Y, n, hok, hY, hp, ?_, ?_⟩)
    · unfold Assn.holds at hh ⊢
      rw [restore_view]
      exact hh
    · obtain ⟨l, g, m, v, rfl⟩ := hex
      exact ⟨_, _, _, _, rfl⟩
  · refine Or.inr ⟨fv, X, Y, n, hok, hY, hp, hn, ?_, restore_returned_ex hex⟩
    unfold Assn.holds at hh ⊢
    rw [restore_view]
    exact hh

/-- A postcondition that accepts every memory-level handler outcome. -/
def AcceptsM (M : Word) (K : Word → Prop) (e : Word) (R : Assn) (ffi : FfiState σ)
    (X0 : OpSt) (Q : Result σ → Prop) : Prop :=
  ∀ r, HandlerQM M K e R ffi X0 r → Q r

theorem AcceptsM.refl {M : Word} {K : Word → Prop} {e : Word} {R : Assn} {ffi : FfiState σ}
    {X0 : OpSt} : AcceptsM M K e R ffi X0 (HandlerQM M K e R ffi X0) :=
  fun _ h => h

theorem AcceptsM.restore {M : Word} {K : Word → Prop} {e : Word} {R : Assn}
    {ffi : FfiState σ} {X0 : OpSt} {x : VarName} {old : Option (PanValue Word)}
    (h : AcceptsM M K e R ffi X0 Q) :
    AcceptsM M K e R ffi X0 (fun r => Q (restorePanValueFfiLocal x old r)) :=
  fun _ hr => h _ hr.restore

/-- For the stack rules: with the buffer in their frame. -/
theorem AcceptsM.toH {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {ffi : FfiState σ}
    {X0 : OpSt} {Y : MemSt} (h : AcceptsM M K e R ffi X0 Q) (hY : MBufOk Y fv) :
    AcceptsH M K e fv (MemExtra e Y ⋆ R) ffi X0 Q :=
  fun r hr => h r (hr.toM hY)

/-- `charge_with_memory(base, start, size)` at a call site. -/
theorem charge_with_memory_hc (hE : GuestEnv E) {args : List (Exp Word)}
    {base a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hargs : E.evalArgs s args = some [.word base,
      .rStruct [.word a0, .word a1, .word a2, .word a3],
      .rStruct [.word b0, .word b1, .word b2, .word b3]])
    (e len cap mem pv fv gl used : Word) (ok : MemOk len cap mem pv fv)
    (hl32 : len.toNat % 32 = 0) (hgl : gl.toNat < 2 ^ 64 - 1) :
    ∀ parameters cbody values cl,
      lookupPanFunction "charge_with_memory" E.functions = some (parameters, cbody) →
      E.evalArgs s args = some values →
      bindPanValueParameters parameters values = some cl →
      WPFt E ⟨cl, s.globals, s.memory, s.ffi⟩ cbody (CMW e len cap mem pv fv gl used)
        (fun r => Assn.or
          (⌜∃ l g m, r = .raised l g m s.ffi "EvmErr" (.word 4#64)⌝ ⋆
            CMW e len cap mem pv fv gl used)
          (Assn.ex fun cap' : Word => Assn.ex fun fv' : Word => Assn.ex fun x : Word =>
            Assn.ex fun total : Word =>
              ⌜(MemOk (len + x) cap' mem pv fv' ∧ (len + x).toNat = len.toNat + x.toNat ∧
                  x.toNat % 32 = 0 ∧
                  (satW b0 b1 b2 b3 = 0#64 ∨
                    (satW a0 a1 a2 a3).toNat + (satW b0 b1 b2 b3).toNat ≤
                      len.toNat + x.toNat) ∧
                  base.toNat ≤ total.toNat ∧ total.toNat ≤ gl.toNat ∧ fv.toNat ≤ fv'.toNat) ∧
                ∃ l g m, r = .returned l g m s.ffi [.word 0#64]⌝ ⋆
              CMW e (len + x) cap' mem pv fv' (gl - total) (used + total))) := by
  intro parameters cbody values cl hlk hvalues hbind
  have hparams := (fun_of_index 461 hE.functions (by guest_decl_at 461) (by decide +kernel)
    hlk).2
  rw [hargs] at hvalues
  cases hvalues
  rw [hparams] at hbind
  simp [bindPanValueParameters] at hbind
  exact charge_with_memory_framed hE parameters cbody hlk ⟨cl, s.globals, s.memory, s.ffi⟩ e len
    cap mem pv fv gl used base a0 a1 a2 a3 b0 b1 b2 b3
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap])
    (by rw [← hbind]; simp (config := { decide := true }) [updatePanValueMap]) ok hl32 hgl

set_option maxHeartbeats 1000000 in
/-- `charge_with_memory(base, start, size); rest` under the frame invariant
with its memory buffer. -/
theorem op_charge_mem (hE : GuestEnv E) {args : List (Exp Word)} {q : Prog Word}
    {base a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (hargs : E.evalArgs s args = some [.word base,
      .rStruct [.word a0, .word a1, .word a2, .word a3],
      .rStruct [.word b0, .word b1, .word b2, .word b3]])
    {M : Word} {K : Word → Prop} {e fv : Word} {R : Assn} {X0 X : OpSt} {Y : MemSt} {n : Nat}
    (hok : FrameOk M K fv X) (hY : MBufOk Y fv) (hp : Adv X X0 n)
    (hgl : X.gl.toNat < 2 ^ 64 - 1)
    (h : (FrameOp M K e fv X ⋆ MemExtra e Y ⋆ R).holds s)
    (hQ : AcceptsM M K e R s.ffi X0 Q)
    (hq : ∀ (fv' x total cap' : Word) g m,
      FrameOk M K fv' { X with gl := X.gl - total, used := X.used + total } →
      MBufOk { Y with len := Y.len + x, cap := cap' } fv' →
      Adv { X with gl := X.gl - total, used := X.used + total } X0 (n + base.toNat) →
      (satW b0 b1 b2 b3 = 0#64 ∨
        (satW a0 a1 a2 a3).toNat + (satW b0 b1 b2 b3).toNat ≤ (Y.len + x).toNat) →
      (FrameOp M K e fv' { X with gl := X.gl - total, used := X.used + total } ⋆
        MemExtra e { Y with len := Y.len + x, cap := cap' } ⋆ R).holds
          (⟨s.locals, g, m, s.ffi⟩ : St σ) →
      WPr E ⟨s.locals, g, m, s.ffi⟩ q Q) :
    WPr E s (.seq (.call (some (none, none)) "charge_with_memory" args) q) Q := by
  have hmok : MemOk Y.len Y.cap Y.mem X.pv fv :=
    ⟨hY.mal, hY.cal, by have := hY.l32; omega, hY.lc, hY.top, hok.ok.fp, hok.ok.pv_hi⟩
  refine WPr.seq_call_framedT (Assn.holds_focus (FrameM_cmw M K e fv X Y)
      (Assn.holds_assoc_l (P := FrameOp M K e fv X) h))
    (charge_with_memory_hc hE hargs e Y.len Y.cap Y.mem X.pv fv X.gl X.used hmok hY.l32 hgl)
    (fun r ht => hQ r (Or.inl (Or.inl ht))) ?_ ?_
  · intro l g m ffi vs hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨_, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC
    obtain ⟨cap', hh⟩ := Assn.holdsV_ex.mp hh
    obtain ⟨fv', hh⟩ := Assn.holdsV_ex.mp hh
    obtain ⟨x, hh⟩ := Assn.holdsV_ex.mp hh
    obtain ⟨total, hh⟩ := Assn.holdsV_ex.mp hh
    obtain ⟨⟨⟨ok', hlx, hx32, hacc, hbt, htg, hfv⟩, _, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
    injection hC with _ _ _ hf _
    subst hf
    have hsub : (X.gl - total).toNat = X.gl.toNat - total.toNat := by bv_omega
    refine hq fv' x total cap' g m
      ⟨⟨hok.ok.cap_pos, hok.ok.cap_le, hok.ok.sp_le, hok.ok.base_al, hok.ok.base_hi, ok'.fp,
        hok.ok.pv_hi⟩, hok.pb, hok.bM, hok.Kpv, hok.Kst⟩
      ⟨ok'.mal, ok'.cal, by show (Y.len + x).toNat % 32 = 0; have := hY.l32; omega, ok'.lc,
        ok'.top⟩
      ⟨by show (X.gl - total).toNat + (n + base.toNat) ≤ X0.gl.toNat; have := hp.1; omega, hp.2⟩
      (by rw [hlx]; exact hacc) ?_
    exact Assn.holds_assoc_r (Assn.holds_unfocus (FrameM_cmw M K e fv'
      { X with gl := X.gl - total, used := X.used + total }
      { Y with len := Y.len + x, cap := cap' }) hk)
  · intro l g m ffi exc v _ hh
    rcases Assn.holds_or_elim hh with hh | hh
    · obtain ⟨⟨_, _, _, hC⟩, hk⟩ := Assn.holds_pure_elim hh
      injection hC with _ _ _ hf hx hv
      subst hf hx hv
      exact hQ _ (Or.inl (Or.inr ⟨fv, X, Y, n, hok, hY, hp, Assn.holds_assoc_r
        (Assn.holds_unfocus (FrameM_cmw M K e fv X Y) (Assn.holds_congr rfl rfl hk)),
        _, _, _, _, rfl⟩))
    · obtain ⟨cap', hh⟩ := Assn.holdsV_ex.mp hh
      obtain ⟨fv', hh⟩ := Assn.holdsV_ex.mp hh
      obtain ⟨x, hh⟩ := Assn.holdsV_ex.mp hh
      obtain ⟨total, hh⟩ := Assn.holdsV_ex.mp hh
      obtain ⟨⟨-, _, _, _, hC⟩, -⟩ := Assn.holds_pure_elim hh
      cases hC

end InitECandidate.Solver.GuestBound
