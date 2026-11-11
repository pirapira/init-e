import InitECandidate.Solver.GuestBound.PureLoopBound

/-! # Loops with a syntactic `2^64` iteration bound -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The loop is accepted by one of the syntactic checks. -/
def loopOk (c : Exp Word) (body : Prog Word) : Bool :=
  counterLoop c body || offsetLoop c body || pureLoop body ||
    constLoop (findStep body) c body

/-- An accepted loop costs at most `2^64` iterations of its guard and body,
in runs that do not end in `.error`. -/
theorem loop_costs (hE : WordEnv E) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : loopOk c body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold loopOk at hcheck
  rcases Bool.or_eq_true_iff.mp hcheck with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · rcases Bool.or_eq_true_iff.mp h with h | h
      · exact counterLoop_costs hE c body b h hbody
      · exact offsetLoop_costs hE c body b h hbody
    · exact pureLoop_costs hE c body b h hbody
  · exact constLoop_costs hE _ c body b h hbody

end InitECandidate.Solver.GuestBound
