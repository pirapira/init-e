import InitECandidate.Solver.GuestBound.RfInstanceM
import InitECandidate.Solver.GuestBound.RfGhost

/-!
# A chain of frames

The running frame owns the globals `ev`, `cur_cont`, `scratch_ptr`,
`frame_mem_ptr`, `evm_empty` and the free gap between the two arena pointers
(`Fr.top`); everything else it owns (`Fr.susp`) is what a frame keeps while a
child runs. `Link c p` says how a child sits on its parent: the continuation
record of the child names the parent and the arena marks, the child's scratch
interval ends at the parent's scratch pointer, and its memory buffer starts
at the parent's `frame_mem_ptr`.

The invariant of `run_frames` is a running frame on a list of suspended
parents; the measure is the sum over the frames of
`4·(gas left + spilled) + running + exception-flag-clear + 1`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The fields of a continuation record other than the done flag. -/
structure RecSt where
  par : Word
  pcc : Word
  kind : Word
  snap : Word
  rmsg : Word
  mark : Word
  mmark : Word
  nac : Word
  ostart : Word
  osize : Word
  caddr : Word
  csnap : Word

/-- The cells of `RecSt`. -/
def RecCells (cc : Word) (C : RecSt) : Assn :=
  .mem cc ↦ .word C.par ⋆ .mem (cc + 8#64) ↦ .word C.pcc ⋆ .mem (cc + 16#64) ↦ .word C.kind ⋆
    .mem (cc + 24#64) ↦ .word C.snap ⋆ .mem (cc + 40#64) ↦ .word C.rmsg ⋆
    .mem (cc + 48#64) ↦ .word C.mark ⋆ .mem (cc + 56#64) ↦ .word C.mmark ⋆
    .mem (cc + 64#64) ↦ .word C.nac ⋆ .mem (cc + 72#64) ↦ .word C.ostart ⋆
    .mem (cc + 80#64) ↦ .word C.osize ⋆ .mem (cc + 88#64) ↦ .word C.caddr ⋆
    .mem (cc + 96#64) ↦ .word C.csnap

/-- The access-table fields of a frame record: the two transaction-wide
tables and their sizes when the frame started. -/
structure AccSt where
  t1 : Word
  t2 : Word
  n1 : Word
  n2 : Word

/-- The cells of `AccSt`. -/
def AccCells (e : Word) (A : AccSt) : Assn :=
  .mem (e + 168#64) ↦ .word A.t1 ⋆ .mem (e + 176#64) ↦ .word A.t2 ⋆
    .mem (e + 264#64) ↦ .word A.n1 ⋆ .mem (e + 272#64) ↦ .word A.n2

/-- The return-data buffer fields of a frame record: pointer, length, capacity. -/
structure RetSt where
  rp : Word
  rn : Word
  rc : Word

/-- The cells of `RetSt`. -/
def RetCells (e : Word) (T : RetSt) : Assn :=
  .mem (e + 144#64) ↦ .word T.rp ⋆ .mem (e + 152#64) ↦ .word T.rn ⋆
    .mem (e + 216#64) ↦ .word T.rc

/-- What frames may know about the world: tables that are live, and heap
ranges that are free blocks. -/
structure WInfo where
  live : Word → Prop
  free : Word → Word → Prop

/-- More is known. -/
def WInfo.le (I I' : WInfo) : Prop :=
  (∀ t, I.live t → I'.live t) ∧ ∀ lo hi, I.free lo hi → I'.free lo hi

/-- A frame: its scratch interval `[X.pv, M)`, tracked cells `K`, record `e`,
`frame_mem_ptr` value `fv`, and the contents of its fields. -/
structure Fr where
  M : Word
  K : Word → Prop
  e : Word
  fv : Word
  X : OpSt
  Y : MemSt
  Z : ExStM
  C : RecSt
  A : AccSt
  T : RetSt

/-- Everything the running frame owns. -/
def Fr.full (F : Fr) : Assn :=
  FrameOp F.M F.K F.e F.fv F.X ⋆ MemExtra F.e F.Y ⋆ ExcExtraM F.e F.Z ⋆ RecCells F.Z.cc F.C ⋆
    AccCells F.e F.A ⋆ RetCells F.e F.T

/-- What only the running frame owns: the globals and the free gap. -/
def Fr.top (F : Fr) : Assn :=
  .glob "ev" ↦ .word F.e ⋆ .glob "scratch_ptr" ↦ .word F.X.pv ⋆
    .glob "frame_mem_ptr" ↦ .word F.fv ⋆ .glob "cur_cont" ↦ .word F.Z.cc ⋆
    .glob "evm_empty" ↦ .word F.Z.ee ⋆ Assn.Range F.fv F.X.pv

/-- The tracked memory cells of a frame. -/
def Fr.cells (F : Fr) : Assn :=
  .mem (F.e + 16#64) ↦ .word F.X.sp ⋆ .mem (F.e + 232#64) ↦ .word F.X.cap ⋆
    .mem (F.e + 8#64) ↦ .word F.X.base ⋆ .mem (F.e + 64#64) ↦ .word F.X.gl ⋆
    .mem (F.e + 184#64) ↦ .word F.X.used ⋆ .mem F.e ↦ .word F.X.pc ⋆
    .mem (F.e + 32#64) ↦ .word F.Y.len ⋆ .mem (F.e + 40#64) ↦ .word F.Y.cap ⋆
    .mem (F.e + 24#64) ↦ .word F.Y.mem ⋆ .mem (F.e + 104#64) ↦ .word F.Y.run ⋆
    .mem (F.e + 120#64) ↦ .word F.Y.rd ⋆ .mem (F.e + 128#64) ↦ .word F.Y.rl ⋆
    .mem (F.e + 72#64) ↦ .word F.Z.sgl ⋆ .mem (F.e + 192#64) ↦ .word F.Z.sp ⋆
    .mem (F.e + 112#64) ↦ .word F.Z.msg ⋆ .mem (F.Z.msg + 48#64) ↦ .word F.Z.r0 ⋆
    .mem (F.e + 160#64) ↦ .word F.Z.code ⋆ .mem (F.Z.cc + 32#64) ↦ .word F.Z.fl ⋆
    RecCells F.Z.cc F.C ⋆ AccCells F.e F.A ⋆ RetCells F.e F.T

/-- What a frame keeps while a child runs: stack buffer, scratch junk, memory
buffer and its tracked cells. -/
def Fr.susp (F : Fr) : Assn :=
  Assn.Range F.X.base (F.X.base + 32#64 * F.X.cap) ⋆ JunkW F.M F.K F.X.pv F.X.base F.X.cap ⋆
    Assn.Range F.Y.mem (F.Y.mem + F.Y.cap) ⋆ F.cells

theorem Fr.full_eq (F : Fr) : F.full = (F.top ⋆ F.susp) := by
  unfold Fr.full Fr.top Fr.susp Fr.cells FrameOp OpW StackW MemExtra MemTail ExcExtraM
  ac_rfl

/-- The pure side of one frame. -/
structure Fr.Ok (I : WInfo) (F : Fr) : Prop where
  ok : FrameOk F.M F.K F.fv F.X
  buf : MBufOk F.Y F.fv
  /-- The access tables are live world tables. -/
  acc : I.live F.A.t1 ∧ I.live F.A.t2
  /-- The return-data buffer is empty or lies in a free block of the heap. -/
  ret : F.T.rc = 0#64 ∨ ∃ lo hi, I.free lo hi ∧ lo.toNat ≤ F.T.rp.toNat ∧
    F.T.rp.toNat + F.T.rc.toNat ≤ hi.toNat

/-- The addresses of a frame's tracked cells. -/
def Fr.addrs (e cc msg : Word) (x : Word) : Prop :=
  x ∈ [e + 16#64, e + 232#64, e + 8#64, e + 64#64, e + 184#64, e, e + 32#64, e + 40#64,
    e + 24#64, e + 104#64, e + 120#64, e + 128#64, e + 72#64, e + 192#64, e + 112#64,
    msg + 48#64, e + 160#64, cc + 32#64, cc, cc + 8#64, cc + 16#64, cc + 24#64, cc + 40#64,
    cc + 48#64, cc + 56#64, cc + 64#64, cc + 72#64, cc + 80#64, cc + 88#64, cc + 96#64,
    e + 168#64, e + 176#64, e + 264#64, e + 272#64, e + 144#64, e + 152#64, e + 216#64]

/-- Child `c` sits directly on parent `p`. -/
structure Link (c p : Fr) : Prop where
  par : c.C.par = p.e
  pcc : c.C.pcc = p.Z.cc
  kind : c.C.kind ≠ 0#64
  mark : c.C.mark = p.X.pv
  mmark : c.C.mmark = p.fv
  top : c.M = p.X.pv
  mem : c.Y.mem = p.fv
  ee : c.Z.ee = p.Z.ee
  room : p.X.sp.toNat < p.X.cap.toNat
  Kdom : ∀ x, c.K x ↔ Fr.addrs c.e c.Z.cc c.Z.msg x
  KM : ∀ x, c.K x → x.toNat < c.M.toNat

/-- A running frame on its suspended parents; the last one has kind 0. -/
def ChainOk (I : WInfo) : Fr → List Fr → Prop
  | F, [] => F.Ok I ∧ F.C.kind = 0#64
  | F, p :: ps => F.Ok I ∧ Link F p ∧ ChainOk I p ps

/-- What the suspended frames own. -/
def suspA : List Fr → Assn
  | [] => ⌜True⌝
  | p :: ps => p.susp ⋆ suspA ps

/-- Gas left plus spilled state gas of a frame. -/
def Fr.gas (F : Fr) : Nat := F.X.gl.toNat + F.Z.sp.toNat

/-- The measure of one frame. -/
def Fr.mu (F : Fr) : Nat :=
  4 * F.gas + (if F.Y.run.toNat = 0 then 0 else 1) + (if F.Z.fl.toNat = 0 then 1 else 0) + 1

def gasSum (ps : List Fr) : Nat := (ps.map Fr.gas).sum

def muSum (ps : List Fr) : Nat := (ps.map Fr.mu).sum

/-- The memory and globals as a view. -/
def viewOf (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word)) : View
  | .mem a => m a
  | .glob x => g x

theorem view_eq (s : St σ) : s.view = viewOf s.globals s.memory := by
  funext k
  cases k <;> rfl

/-- The invariant of `run_frames` at measure at most `n`. `W i` is what the
world state owns and `D i` its live tables, for an index `i` (the world's
registry) that may change from step to step. -/
def chainInv {ι : Type} (W : ι → Assn) (D : ι → WInfo) (n : Nat)
    (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) : Prop :=
  ∃ (i : ι) (F : Fr) (ps : List Fr) (R : Assn), ChainOk (D i) F ps ∧
    F.gas + gasSum ps < 2 ^ 64 - 1 ∧ F.mu + muSum ps ≤ n ∧
    (F.full ⋆ suspA ps ⋆ W i ⋆ R).holdsV (viewOf g m)

theorem ChainOk.head {D : WInfo} {F : Fr} {ps : List Fr} (h : ChainOk D F ps) :
    F.Ok D := by
  cases ps with
  | nil => exact h.1
  | cons p ps => exact h.1

/-- Replacing the running frame by one with the same identity keeps the chain. -/
theorem ChainOk.replace {D : WInfo} {F F' : Fr} {ps : List Fr} (h : ChainOk D F ps)
    (hok : F'.Ok D)
    (hC : F'.C = F.C) (hM : F'.M = F.M) (hK : F'.K = F.K) (he : F'.e = F.e)
    (hmem : F'.Y.mem = F.Y.mem) (hcc : F'.Z.cc = F.Z.cc) (hmsg : F'.Z.msg = F.Z.msg)
    (hee : F'.Z.ee = F.Z.ee) : ChainOk D F' ps := by
  cases ps with
  | nil => exact ⟨hok, by rw [hC]; exact h.2⟩
  | cons p ps =>
    obtain ⟨-, hl, hr⟩ := h
    refine ⟨hok, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hl.room, ?_, ?_⟩, hr⟩
    · rw [hC]; exact hl.par
    · rw [hC]; exact hl.pcc
    · rw [hC]; exact hl.kind
    · rw [hC]; exact hl.mark
    · rw [hC]; exact hl.mmark
    · rw [hM]; exact hl.top
    · rw [hmem]; exact hl.mem
    · rw [hee]; exact hl.ee
    · rw [hK, he, hcc, hmsg]; exact hl.Kdom
    · rw [hK, hM]; exact hl.KM

/-- The loop interface for a chain of frames; the end-of-frame block is assumed. -/
noncomputable def rfChain {ι : Type} (W : ι → Assn) (D : ι → WInfo) (hE : GuestEnv E) (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f)
    (BD BF : Nat) (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ (a : St σ) (n : Nat), chainInv W D n a.globals a.memory →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ ∃ n', n' < n ∧ chainInv W D n' g m)))) :
    RfGhost E where
  InvN := chainInv W D
  DispatchPre := fun a =>
    (∃ l, E.eval ⟨l, a.globals, a.memory, a.ffi⟩ rfC1 = some (.word 0#64)) ∧
      ∃ l, E.eval ⟨l, a.globals, a.memory, a.ffi⟩ rfC2 = some (.word 0#64)
  BD := BD
  BF := BF
  costD := costD
  costF := costF
  pre := fun a _ h1 h2 _ _ => ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  finish := finish
  dispatch := by
    rintro a n ⟨i, F, ps, R, hch, hgas, hmu, hh⟩ ⟨⟨l1, hpre1⟩, ⟨l2, hpre2⟩⟩
    have hF : ∀ s' : St σ, s'.globals = a.globals → s'.memory = a.memory →
        (FrameOp F.M F.K F.e F.fv F.X ⋆ MemExtra F.e F.Y ⋆ ExcExtraM F.e F.Z ⋆
          (RecCells F.Z.cc F.C ⋆ AccCells F.e F.A ⋆ RetCells F.e F.T ⋆ suspA ps ⋆ W i ⋆ R)).holds s' := by
      intro s' hg hm
      have h0 : (F.full ⋆ suspA ps ⋆ W i ⋆ R).holds a := by
        unfold Assn.holds
        rw [view_eq]
        exact hh
      exact Assn.holds_congr hg hm (Assn.holds_perm h0 (by unfold Fr.full; ac_rfl))
    have hfl : F.Z.fl = 0#64 := rfC1_flagM hE (hF ⟨l1, a.globals, a.memory, a.ffi⟩ rfl rfl) hpre1
    have hrun : F.Y.run ≠ 0#64 :=
      rfC2_run hE (hF ⟨l2, a.globals, a.memory, a.ffi⟩ rfl rfl) hpre2
    have hrun' : F.Y.run.toNat ≠ 0 := fun h0 => hrun (by bv_omega)
    have hok := hch.head
    refine WPr.wps (rfDispatch_stepM hE hrest a F.M F.K F.e F.fv
      (RecCells F.Z.cc F.C ⋆ AccCells F.e F.A ⋆ RetCells F.e F.T ⋆ suspA ps ⋆ W i ⋆ R) F.X F.Y F.Z hok.ok hok.buf
      (by unfold Fr.gas at hgas; omega) (hF a rfl rfl)) (fun r hr => ?_)
    rcases hr with ht | ⟨l, g, m, fv', X', Y', Z', rfl, hok', hY', hh', hl, hle, hcase,
      hmem, hcc, hmsg, hee⟩
    · exact Or.inl ht.stopped
    · obtain ⟨F', hF'⟩ : ∃ F' : Fr, F' = ⟨F.M, F.K, F.e, fv', X', Y', Z', F.C, F.A, F.T⟩ := ⟨_, rfl⟩
      have hmuF : F'.mu < F.mu ∧ F'.gas ≤ F.gas := by
        subst hF'
        unfold Fr.mu Fr.gas
        dsimp only
        have ha : (if Y'.run.toNat = 0 then 0 else 1 : Nat) ≤ 1 := by split <;> omega
        have hb : (if Z'.fl.toNat = 0 then 1 else 0 : Nat) ≤ 1 := by split <;> omega
        have ho1 : (if F.Y.run.toNat = 0 then 0 else 1 : Nat) = 1 := if_neg hrun'
        have ho2 : (if F.Z.fl.toNat = 0 then 1 else 0 : Nat) = 1 := by rw [hfl]; rfl
        rw [ho1, ho2]
        refine ⟨?_, hle⟩
        rcases hcase with ⟨_, h2 | h2⟩ | h1
        · omega
        · have : (if Y'.run.toNat = 0 then 0 else 1 : Nat) = 0 := by rw [h2]; rfl
          omega
        · have : (if Z'.fl.toNat = 0 then 1 else 0 : Nat) = 0 := by rw [h1]; rfl
          omega
      refine Or.inr ⟨l, g, m, a.ffi, rfl, ⟨F'.mu + muSum ps, by omega, i, F', ps, R, ?_, by omega,
        Nat.le_refl _, ?_⟩, hl "go" (by decide), hl "done" (by decide)⟩
      · subst hF'
        exact hch.replace ⟨hok', hY', hok.acc, hok.ret⟩ rfl rfl rfl rfl hmem hcc hmsg hee
      · subst hF'
        have h1 : (Fr.full ⟨F.M, F.K, F.e, fv', X', Y', Z', F.C, F.A, F.T⟩ ⋆ suspA ps ⋆ W i ⋆
            R).holds
            (⟨l, g, m, a.ffi⟩ : St σ) := by
          refine Assn.holds_perm hh' ?_
          unfold Fr.full
          dsimp only
          rw [hcc]
          ac_rfl
        unfold Assn.holds at h1
        rw [view_eq] at h1
        exact h1

/-- `run_frames` from a chain of frames of measure at most `k`. -/
theorem run_frames_bound_chain {ι : Type} (W : ι → Assn) (D : ι → WInfo)
    (hE : GuestEnv E)
    (hrest : ∀ f, f ∈ restOpsM → HandlerSpecM E f) (BD BF : Nat)
    (costD : Costs E rfDispatch BD) (costF : Costs E rfEnd BF)
    (finish : ∀ (a : St σ) (n : Nat), chainInv W D n a.globals a.memory →
      WPs E a rfEnd (fun r => ∃ l g m f, r = .normal l g m f ∧
        (l "go" = some (.word 0#64) ∨
          (l "go" = a.locals "go" ∧ ∃ n', n' < n ∧ chainInv W D n' g m))))
    (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "run_frames" E.functions = some (parameters, body))
    (s : St σ) (k : Nat) (hI : chainInv W D k s.globals s.memory) (fuel : Nat) (r : Result σ)
    (n : Nat) (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) :
    n ≤ (k + 1 + 1) * (expCost rfCond + (BD + BF + 200) + 1) + 10 :=
  run_frames_bound_ghost hE (rfChain W D hE hrest BD BF costD costF finish) parameters body hlookup
    s k hI fuel r n hrun hne

end InitECandidate.Solver.GuestBound
