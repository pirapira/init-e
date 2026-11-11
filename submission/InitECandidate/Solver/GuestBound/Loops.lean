import InitECandidate.Solver.GuestBound.WalkLoopBound
import InitECandidate.Solver.GuestBound.GlobalLoop
import InitECandidate.Solver.GuestBound.HalvingLoop

/-! # Loops with a syntactic `2^64` iteration bound -/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- How deep `calmFn` follows calls from an offset-loop body. -/
def calmDepth : Nat := 8

/-- The loop is accepted by one of the syntactic checks. `decls` is the
declaration list in which callees of offset-loop bodies are looked up. -/
def loopOk (decls : List (Decl Word)) (c : Exp Word) (body : Prog Word) : Bool :=
  counterLoop c body || offsetLoop (calmFn decls calmDepth) c body || pureLoop body ||
    constLoop (findStep body) c body || walkLoop c body ||
    lowerLoop (calmFn decls calmDepth) (findStep body) c body ||
    globalCounterLoop decls calmDepth c body ||
    leLoop (calmFn decls calmDepth) (findStep body) c body || halvingLoop c body

/-- An accepted loop costs at most `2^64` iterations of its guard and body,
in runs that do not end in `.error`. -/
theorem loop_costs (hE : WordEnv E) {decls : List (Decl Word)}
    (hfrom : FunctionsFrom E.functions decls) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : loopOk decls c body = true) (hbody : Costs E body b) :
    Costs E (.while c body) (2 ^ 64 * (expCost c + b + 1)) := by
  unfold loopOk at hcheck
  rcases Bool.or_eq_true_iff.mp hcheck with hcheck | h
  swap
  · exact halvingLoop_costs hE c body b h hbody
  rcases Bool.or_eq_true_iff.mp hcheck with hcheck | h
  swap
  · exact leLoop_costs hE _ (calmFn_sound hfrom calmDepth) _ c body b h hbody
  rcases Bool.or_eq_true_iff.mp hcheck with hcheck | h
  swap
  · exact globalCounterLoop_costs hE hfrom calmDepth c body b h hbody
  rcases Bool.or_eq_true_iff.mp hcheck with hcheck | h
  swap
  · exact lowerLoop_costs hE _ (calmFn_sound hfrom calmDepth) _ c body b h hbody
  rcases Bool.or_eq_true_iff.mp hcheck with h | h
  · rcases Bool.or_eq_true_iff.mp h with h | h
    · rcases Bool.or_eq_true_iff.mp h with h | h
      · rcases Bool.or_eq_true_iff.mp h with h | h
        · exact counterLoop_costs hE c body b h hbody
        · exact offsetLoop_costs hE _ (calmFn_sound hfrom calmDepth) c body b h hbody
      · exact pureLoop_costs hE c body b h hbody
    · exact constLoop_costs hE _ c body b h hbody
  · exact walkLoop_costs hE c body b h hbody

end InitECandidate.Solver.GuestBound
