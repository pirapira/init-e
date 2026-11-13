import InitECandidate.Solver.GuestBound.TrieDecLoop
import InitECandidate.Solver.GuestBound.TrieDecodeStep

/-!
# `_decode_witness_node_body`: unconditional statements

With `decIface` the world theorem and the step bound of the witness decoder
depend on the world invariant and the scratch-arena globals only.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- `_decode_witness_node_body` keeps the world invariant and returns a node at level `L0`. -/
theorem decode_witness_body_world (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "_decode_witness_node_body" E.functions =
      some (parameters, body))
    (R0 : Reg) (s : St σ) (r : Result σ) (dbv pw nw sp0 fv : Word) (L0 : Nat)
    (hdb : s.locals "db" = some (.word dbv)) (hp : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat) (h : Runs E s body r) :
    Stopped r ∨ DecQ (decIface hE) R0 s sp0 fv L0 r :=
  decode_body_world hE (decIface hE) parameters body hlookup R0 s r dbv pw nw sp0 fv L0 hdb hp
    hn hW trivial hsp hfv hfs hF h

/-- `_decode_witness_node_body` takes at most `10^182` steps from a world-invariant state. -/
theorem decode_witness_body_cost (hE : GuestEnv E) (parameters : List VarName)
    (body : Prog Word)
    (hlookup : lookupPanFunction "_decode_witness_node_body" E.functions =
      some (parameters, body))
    (R0 : Reg) (fuel : Nat) (s : St σ) (r : Result σ) (n : Nat) (dbv pw nw sp0 fv : Word)
    (L0 : Nat)
    (hdb : s.locals "db" = some (.word dbv)) (hp : s.locals "p" = some (.word pw))
    (hn : s.locals "n" = some (.word nw)) (hW : WorldTJ R0 s.globals s.memory)
    (hsp : s.globals "scratch_ptr" = some (.word sp0))
    (hfv : s.globals "frame_mem_ptr" = some (.word fv)) (hfs : fv.toNat ≤ sp0.toNat)
    (hF : 2952790016 ≤ fv.toNat)
    (hrun : E.run fuel s body = some (r, n)) (hne : r.isError = false) : n ≤ 10 ^ 182 :=
  decode_body_cost hE (decIface hE) parameters body hlookup R0 fuel s r n dbv pw nw sp0 fv L0
    hdb hp hn hW trivial hsp hfv hfs hF hrun hne

end InitECandidate.Solver.GuestBound
