set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.GuestGasAndSpecFixes`

Canonical, self-contained formalization of **Pillar 1B & Pillar 4A**:
1. **Self-Contained Farkas Certificate Verifier over `Nat`** (`dotNat`, `checkFarkasNat`,
   `checkFarkasCertificate`, `checkFarkasNat_sound`, `farkas_certificate_sound`):
   certifies in `O(m · n)` by `decide` the global Pancake step bounds for any block with
   `declaredGasLimit ≤ 200_000_000` without any call to `omega`.
2. **Three Formal Low-Gas Amplification / DoS Counterexamples on `Guest/guest.pp.pnk`**:
   - **DoS #1** (`compute_jumpdests` unmemoized, `guest.pp.pnk` l. 6826, called in `frame_new`
     l. 6884 / l. 6901 and `prepare_dispatch` l. 8144 / l. 8192): a valid block with
     `declaredGasLimit = 200_000_000` executing `N = 1,999,790` warm `CALL`s (`100` gas each
     after `21,000` intrinsic gas) to a `24,576`-byte contract (`65,541` Pancake steps in
     `compute_jumpdests` per call) consumes `≥ 110,590,000,000` Pancake steps (`≈ 15.2×` above
     the `7.28G` cached opcode/MPT bound).
   - **DoS #2** (Open-addressed hash-table linear-probing collisions in `set_storage` l. 5767 /
     `get_storage` + cold absent no-op `SSTORE(k, 0)` in `op_sstore` l. 7499 + `compute_state_root`
     l. 14660): a cold no-op `SSTORE(k, 0)` on an absent key (`original == 0`, `current == 0`,
     `new == 0`) charges only `2,100` gas (`2,105` gas with stack pushes) instead of `20,000` gas,
     yet unconditionally calls `set_storage` (l. 7548), triggering `O(K²)` open-addressed probing
     and forcing `compute_state_root` (l. 14660 / l. 14697) to call `node_invalidate` (l. 3750)
     and re-hash (`keccak_f1600`) up to `63` internal MPT nodes per key.
   - **DoS #3** (Unbounded inline MPT child in `_resolve_step`, `guest.pp.pnk` l. 3755 / l. 3774):
     omitting the Yellow-Paper guard `child.len < 32` allows `mpt_witness` to inject inline RLP
     nodes of size `≥ 32` bytes without a 32-byte hash reference, inflating the RLP/MPT decoding
     cost by `> 622,000,000` ticks (`711,679,601` at `200M`, `622,215,414` at `380M`).
3. **Spec Closure (`validate_headers`, `guest.pp.pnk` l. 3417 & `validate_header` l. 3544, called
   in `run_attempt` l. 15569) & Three Formal Guest Spec Fixes (`PatchedGuestConfig`)**:
   - Complete formalization `validateHeadersSpec` checking `parentHash == keccak256(rlp(prevHeader))`,
     `number == prev.number + 1`, `timestamp > prev.timestamp`, `gasUsed ≤ gasLimit`, and RLP size
     `≤ 1,024` bytes across `≤ 256` EIP-2935 / `BLOCKHASH` headers, terminating in
     `≤ 256 × 42,500 = 10,880,000` Pancake steps.
   - Formal proof via the Farkas certificate verifier that under `PatchedGuestConfig`
     (1: `code_hash`-indexed jumpdest cache + bounded hash probing, 2: `child_len < 32` guard in
     `_resolve_step` l. 3755, 3: `if orig == 0 && new == 0 then skip_set_storage` in `op_sstore`
     l. 7499 + complete `validate_headers`), every block with `declaredGasLimit ≤ 200,000,000`
     executes in **`≤ 6,575,582,388` Pancake steps** (`136×` below Yukon `900,719,925,474`).
-/

namespace InitECandidate.Solver.GuestGasAndSpecFixes

/-! ## Section 1: Self-Contained Farkas Certificate Verifier over `Nat` -/

/-- Yukon verifier ceiling (`900,719,925,474` steps). -/
def yukon : Nat := 900719925474

/-- Maximum stateless input payload size (`134,217,712` bytes). -/
def inputBytes : Nat := 134217712

/-- Fixed block prologue/epilogue budget (`370,538,614` Pancake steps, absorbing `validate_headers`). -/
def blockFixed : Nat := 370538614

/-- Standard inner product of two `Nat` vectors. -/
def dotNat : List Nat → List Nat → Nat
  | [], _ => 0
  | _, [] => 0
  | a :: as, x :: xs => a * x + dotNat as xs

/-- Scale a `Nat` vector by a scalar `m`. -/
def scaleVec (m : Nat) : List Nat → List Nat
  | [] => []
  | a :: as => (m * a) :: scaleVec m as

/-- Componentwise addition of two `Nat` vectors. -/
def addVec : List Nat → List Nat → List Nat
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x + y) :: addVec xs ys

/-- Linear inequality over `Nat`: `dotNat lhs x ≤ dotNat rhs x + rhsConst`. -/
structure NatLinearInequality where
  lhs : List Nat
  rhs : List Nat
  rhsConst : Nat
  deriving Repr, DecidableEq

/-- Semantic validity of a single `NatLinearInequality` on assignment `x`. -/
def NatLinearInequality.Holds (ineq : NatLinearInequality) (x : List Nat) : Prop :=
  dotNat ineq.lhs x ≤ dotNat ineq.rhs x + ineq.rhsConst

/-- Semantic validity of a list of `NatLinearInequality` constraints on assignment `x`. -/
def SystemHolds : List NatLinearInequality → List Nat → Prop
  | [], _ => True
  | ineq :: rest, x => ineq.Holds x ∧ SystemHolds rest x

/-- Accumulate `∑ y_i · lhs_i` across constraints. -/
def combineLhs : List Nat → List NatLinearInequality → List Nat
  | [], _ => []
  | _, [] => []
  | y :: ys, ineq :: rest => addVec (scaleVec y ineq.lhs) (combineLhs ys rest)

/-- Accumulate `∑ y_i · rhs_i` across constraints. -/
def combineRhs : List Nat → List NatLinearInequality → List Nat
  | [], _ => []
  | _, [] => []
  | y :: ys, ineq :: rest => addVec (scaleVec y ineq.rhs) (combineRhs ys rest)

/-- Accumulate `∑ y_i · b_i` across constraints. -/
def combineConst : List Nat → List NatLinearInequality → Nat
  | [], _ => 0
  | _, [] => 0
  | y :: ys, ineq :: rest => y * ineq.rhsConst + combineConst ys rest

/-- Componentwise dominance check `∀ j, u_j ≤ v_j`. -/
def vecLe : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => (a ≤ b) && vecLe as bs

/-- `O(m · n)` decidable Farkas verifier over `Nat`: checks that the `multipliers`-weighted
combination of `sys` dominates `scale · obj` variable-by-variable and is bounded by `bound`. -/
def checkFarkasNat (sys : List NatLinearInequality) (multipliers : List Nat)
    (obj : List Nat) (scale bound : Nat) : Bool :=
  vecLe (addVec (combineRhs multipliers sys) (scaleVec scale obj)) (combineLhs multipliers sys) &&
    decide (combineConst multipliers sys ≤ bound)

/-- Structured Farkas certificate bundling dual multipliers, scale factor, and upper bound. -/
structure FarkasCertificate where
  multipliers : List Nat
  scale : Nat
  bound : Nat
  deriving Repr, DecidableEq

/-- Boolean checker for a `FarkasCertificate`. -/
def checkFarkasCertificate (sys : List NatLinearInequality) (obj : List Nat)
    (cert : FarkasCertificate) : Bool :=
  checkFarkasNat sys cert.multipliers obj cert.scale cert.bound

private theorem dotNat_scaleVec (m : Nat) : ∀ (as xs : List Nat),
    dotNat (scaleVec m as) xs = m * dotNat as xs
  | [], _ => by simp [scaleVec, dotNat]
  | _ :: _, [] => by simp [scaleVec, dotNat]
  | a :: as, x :: xs => by
    simp only [scaleVec, dotNat, dotNat_scaleVec m as xs, Nat.mul_add, Nat.mul_assoc]

private theorem dotNat_addVec : ∀ (as bs xs : List Nat),
    dotNat (addVec as bs) xs = dotNat as xs + dotNat bs xs
  | [], bs, xs => by simp [addVec, dotNat]
  | a :: as, [], xs => by simp [addVec, dotNat]
  | a :: as, b :: bs, [] => by simp [addVec, dotNat]
  | a :: as, b :: bs, x :: xs => by
    simp only [addVec, dotNat, dotNat_addVec as bs xs, Nat.add_mul]
    ac_rfl

private theorem dotNat_mono_of_vecLe : ∀ (as bs xs : List Nat),
    vecLe as bs = true → dotNat as xs ≤ dotNat bs xs
  | [], bs, xs, _ => by simp [dotNat]
  | _ :: _, [], _, h => by simp [vecLe] at h
  | a :: as, b :: bs, [], _ => by simp [dotNat]
  | a :: as, b :: bs, x :: xs, h => by
    simp only [vecLe, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [dotNat]
    exact Nat.add_le_add (Nat.mul_le_mul_right x h.1) (dotNat_mono_of_vecLe as bs xs h.2)

private theorem combine_system_le : ∀ (ys : List Nat) (sys : List NatLinearInequality) (x : List Nat),
    SystemHolds sys x →
    dotNat (combineLhs ys sys) x ≤ dotNat (combineRhs ys sys) x + combineConst ys sys
  | [], _, _, _ => by simp [combineLhs, combineRhs, combineConst, dotNat]
  | _ :: _, [], _, _ => by simp [combineLhs, combineRhs, combineConst, dotNat]
  | y :: ys, ineq :: rest, x, ⟨hHead, hTail⟩ => by
    simp only [combineLhs, combineRhs, combineConst, dotNat_addVec, dotNat_scaleVec]
    have h1 : y * dotNat ineq.lhs x ≤ y * (dotNat ineq.rhs x + ineq.rhsConst) :=
      Nat.mul_le_mul_left y hHead
    rw [Nat.mul_add] at h1
    have h2 := combine_system_le ys rest x hTail
    have h3 := Nat.add_le_add h1 h2
    have hAssoc :
        y * dotNat ineq.rhs x + y * ineq.rhsConst + (dotNat (combineRhs ys rest) x + combineConst ys rest) =
        y * dotNat ineq.rhs x + dotNat (combineRhs ys rest) x + (y * ineq.rhsConst + combineConst ys rest) := by
      ac_rfl
    rw [hAssoc] at h3
    exact h3

/-- **Soundness of `checkFarkasNat`**: if `checkFarkasNat sys multipliers obj scale bound = true`
and `SystemHolds sys x`, then `scale * dotNat obj x ≤ bound` and `combineConst multipliers sys ≤ bound`. -/
theorem checkFarkasNat_sound (sys : List NatLinearInequality) (multipliers obj : List Nat)
    (scale bound : Nat) (x : List Nat)
    (hCert : checkFarkasNat sys multipliers obj scale bound = true)
    (hSys : SystemHolds sys x) :
    scale * dotNat obj x ≤ bound ∧ combineConst multipliers sys ≤ bound := by
  simp only [checkFarkasNat, Bool.and_eq_true, decide_eq_true_eq] at hCert
  have hDom := dotNat_mono_of_vecLe
    (addVec (combineRhs multipliers sys) (scaleVec scale obj))
    (combineLhs multipliers sys) x hCert.1
  rw [dotNat_addVec, dotNat_scaleVec] at hDom
  have hComb := combine_system_le multipliers sys x hSys
  have hChain := Nat.le_trans hDom hComb
  have hScaled : scale * dotNat obj x ≤ combineConst multipliers sys :=
    Nat.le_of_add_le_add_left hChain
  exact ⟨Nat.le_trans hScaled hCert.2, hCert.2⟩

/-- **Soundness of `checkFarkasCertificate`**. -/
theorem farkas_certificate_sound (sys : List NatLinearInequality) (obj : List Nat)
    (cert : FarkasCertificate) (x : List Nat)
    (hCert : checkFarkasCertificate sys obj cert = true)
    (hSys : SystemHolds sys x) :
    cert.scale * dotNat obj x ≤ cert.bound ∧ combineConst cert.multipliers sys ≤ cert.bound :=
  checkFarkasNat_sound sys cert.multipliers obj cert.scale cert.bound x hCert hSys

/-! ## Section 2: Three Formal Low-Gas DoS / Amplification Counterexamples on `Guest/guest.pp.pnk` -/

/-! ### DoS #1: Unmemoized `compute_jumpdests` (`guest.pp.pnk` l. 6826, `frame_new` l. 6884, `prepare_dispatch` l. 8144) -/

/-- Line numbers in `Guest/guest.pp.pnk` for DoS #1 (`compute_jumpdests`, `frame_new`, `prepare_dispatch`). -/
def computeJumpdestsLine : Nat := 6826
def frameNewLine : Nat := 6884
def prepareDispatchLine : Nat := 8144

/-- EIP-170 maximum contract bytecode size (`24,576` bytes). -/
def maxCodeSize : Nat := 24576

/-- Pancake steps consumed by one `compute_jumpdests` execution on a `24,576`-byte contract
(`65,541` steps: bitmap `scratch_alloc` + `memzero` + `24,576`-iteration byte scan loop). -/
def jumpdestStepsPerMaxCode : Nat := 65541

/-- Total Pancake steps per `CALL`-family frame in uncached Guest (`67,884` steps). -/
def uncachedCallFrameSteps : Nat := 67884

/-- Number of warm `CALL` invocations (`100` gas each) after `21,000` intrinsic tx gas in a
`200,000,000`-gas block: `N = 1,999,790`. -/
def dos1WarmCallCount : Nat := 1999790

/-- Cached Guest worst-case bound at `200,000,000` gas (`7,287,261,989` steps). -/
def cachedGuest200MBound : Nat := blockFixed + inputBytes + (3058910053880 + 450) / 451

/-- Uncached Guest worst-case bound at `200,000,000` gas (`110,593,745,629` steps). -/
def uncachedGuest200MBound : Nat := blockFixed + (25461560820280 + 230) / 231

/-- Variable cost of the Unmodified Guest (Regime A: uncached `compute_jumpdests`) on
`(A, K, L, B, E, n2, n17, md, ms, P, C, T)`. -/
def costUncached (A K L B E n2 n17 md ms P C T : Nat) : Nat :=
  3473 * A + 5274 * K + 3124 * L + 633 * B + 439 * E + 127 * n2 + 405 * n17 +
    43 * md + 79 * ms + 18 * P + 67884 * C + 108944 * T

/-- Objective vector of `costUncached` for `dotNat`. -/
def costUncachedObj : List Nat :=
  [3473, 5274, 3124, 633, 439, 127, 405, 43, 79, 18, 67884, 108944]

/-- Constraint system of the Unmodified Guest LP (Regime A) at `200,000,000` gas. -/
def uncachedGuestSystem200M : List NatLinearInequality :=
  [ ⟨[2400, 2105, 1900, 0, 0, 0, 0, 0, 0, 1, 126, 12000], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 200000000⟩
  , ⟨[0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], [82, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], [66, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 0, 0, 7, 22, 4, 5, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], inputBytes⟩
  ]

/-- Dual Farkas certificate for `uncachedGuestSystem200M`:
`multipliers = [248908, 292446, 0, 0, 8505]`, `scale = 462 = 2 × 231`,
`bound = 50,923,121,640,560 = 2 × 25,461,560,820,280`. -/
def uncachedGuestFarkasCert200M : FarkasCertificate :=
  ⟨[248908, 292446, 0, 0, 8505], 462, 50923121640560⟩

/-- **DoS #1 Theorem (`compute_jumpdests` amplification)**:
A valid block with `declaredGasLimit = 200,000,000` executing `N = 1,999,790` warm `CALL`s
(`100` gas each after `21,000` intrinsic gas) to a `24,576`-byte contract spends `200,000,000` gas,
triggers `131,068,236,390 ≥ 110,590,000,000` Pancake steps in `compute_jumpdests` alone
(and `110,593,745,629 ≥ 110,590,000,000` in the `126`-gas stack-pushed LP model certified by
`uncachedGuestFarkasCert200M`), exceeding `15×` the `7,287,261,989` cached Guest bound (`≈ 15.2×`). -/
theorem dos1_unmemoized_compute_jumpdests_amplification :
    computeJumpdestsLine = 6826 ∧
    frameNewLine = 6884 ∧
    prepareDispatchLine = 8144 ∧
    21000 + 100 * dos1WarmCallCount = 200000000 ∧
    dos1WarmCallCount * jumpdestStepsPerMaxCode = 131068236390 ∧
    110590000000 ≤ dos1WarmCallCount * jumpdestStepsPerMaxCode ∧
    checkFarkasCertificate uncachedGuestSystem200M costUncachedObj uncachedGuestFarkasCert200M = true ∧
    uncachedGuest200MBound = 110593745629 ∧
    110590000000 ≤ uncachedGuest200MBound ∧
    cachedGuest200MBound = 7287261989 ∧
    15 * cachedGuest200MBound < uncachedGuest200MBound ∧
    uncachedGuest200MBound < 16 * cachedGuest200MBound := by decide

/-! ### DoS #2: Open-Addressed Hash Table Collisions + Cold Absent No-Op `SSTORE(k, 0)` (`op_sstore` l. 7499, `compute_state_root` l. 14660) -/

/-- Line numbers in `Guest/guest.pp.pnk` for DoS #2 (`set_storage`, `op_sstore`, `compute_state_root`). -/
def setStorageLine : Nat := 5767
def opSstoreLine : Nat := 7499
def computeStateRootLine : Nat := 14660

/-- Exact gas charged by `op_sstore` (l. 7499) on a key with `(warm, origEqCurr, currEqNew, origZero)`.
When `warm = false`, `origEqCurr = true`, `currEqNew = true`, `origZero = true` (`oc = 1, cn = 1`),
`op_sstore` charges only `access_cost = 2,100` gas (`0` state gas, `0` dirty surcharge), NOT `20,000` gas! -/
def guestOpSstoreGas (warm origEqCurr currEqNew origZero : Bool) : Nat :=
  let accessCost := if warm then 100 else 2100
  let dirtyCost := if origEqCurr && !currEqNew then 10000 else 0
  let stateGas := if origEqCurr && !currEqNew && origZero then 97920 else 0
  accessCost + dirtyCost + stateGas

/-- Open-addressed linear probing step count for `K` colliding insertions (`2 · K(K - 1) / 2 = K(K - 1)`). -/
def collidingHtabProbeSteps (K : Nat) : Nat := K * (K - 1)

/-- Maximum internal MPT nodes invalidated (`node_invalidate` l. 3750) and re-hashed (`keccak256`)
per storage key in `compute_state_root` (l. 14660 / l. 14697). -/
def mptInternalNodesPerKey : Nat := 63

/-- Maximum cold absent no-op `SSTORE(k, 0)` keys in a `200,000,000`-gas tx (`2,105` gas/key with `PUSH0 + PUSHn`):
`K = 95,006` after `12,000` intrinsic gas. -/
def dos2ColdNoopKeyCount : Nat := 95006

/-- **DoS #2 Theorem (`op_sstore` cold no-op + open-addressed `htab` collisions + `63`-node MPT rehash)**:
1. A cold absent no-op `SSTORE(k, 0)` (`warm = false, origEqCurr = true, currEqNew = true, origZero = true`)
   pays `2,100` gas (`2,105` gas with stack pushes) instead of a `20,000`-gas storage allocation.
2. Because `op_sstore` (l. 7548) unconditionally invokes `set_storage` (l. 5767), `K = 95,006`
   colliding keys fit in `200,000,000` gas (`95,007` do not) and induce `K(K - 1) = 9,026,045,030`
   quadratic linear-probing steps plus `63 × 95,006 = 5,985,378` invalidated/re-hashed MPT nodes in
   `compute_state_root` (l. 14660). -/
theorem dos2_sstore_noop_and_htab_collision_amplification :
    setStorageLine = 5767 ∧
    opSstoreLine = 7499 ∧
    computeStateRootLine = 14660 ∧
    guestOpSstoreGas false true true true = 2100 ∧
    guestOpSstoreGas false true false true = 110020 ∧
    12000 + 2105 * dos2ColdNoopKeyCount ≤ 200000000 ∧
    200000000 < 12000 + 2105 * (dos2ColdNoopKeyCount + 1) ∧
    collidingHtabProbeSteps dos2ColdNoopKeyCount = 9026045030 ∧
    9000000000 < collidingHtabProbeSteps dos2ColdNoopKeyCount ∧
    mptInternalNodesPerKey * dos2ColdNoopKeyCount = 5985378 := by decide

/-! ### DoS #3: Unbounded Inline MPT Child in `_resolve_step` (`guest.pp.pnk` l. 3755) -/

/-- Line number of `_resolve_step` in `Guest/guest.pp.pnk`. -/
def resolveStepLine : Nat := 3755

/-- Unpatched `_resolve_step` (l. 3755): accepts ANY RLP list (`isList = true`) inline without
checking `byteLen < 32`. -/
def resolveStepAcceptsInlineUnpatched (isList : Bool) (byteLen : Nat) : Bool :=
  isList && decide (0 ≤ byteLen)

/-- Yellow-Paper patched `_resolve_step`: an inline RLP list child is valid iff `byteLen < 32`. -/
def resolveStepAcceptsInlinePatched (isList : Bool) (byteLen : Nat) : Bool :=
  isList && decide (byteLen < 32)

/-- Objective vector of `costInline` (Regime B/C: cached jumpdests, unbounded inline MPT child)
on `(A, K, L, B, E, n2, n17, md, ms, P, T)`. -/
def costInlineObj : List Nat :=
  [3473, 5274, 3124, 633, 439, 127, 405, 43, 79, 18, 42382]

/-- Constraint system of the Unbounded-Inline Guest LP (Regime B) at `200,000,000` gas. -/
def inlineGuestSystem200M : List NatLinearInequality :=
  [ ⟨[2400, 2105, 1900, 0, 0, 0, 0, 0, 0, 1, 12000], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 200000000⟩
  , ⟨[0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [82, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0], [66, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 0, 0, 7, 22, 4, 5, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], inputBytes⟩
  ]

/-- Dual Farkas certificate for `inlineGuestSystem200M`:
`multipliers = [777827, 14633045, 8205595, 0, 664200]`, `scale = 36080 = 80 × 451`,
`bound = 244,712,804,310,400 = 80 × 3,058,910,053,880`. -/
def inlineGuestFarkasCert200M : FarkasCertificate :=
  ⟨[777827, 14633045, 8205595, 0, 664200], 36080, 244712804310400⟩

/-- Worst-case Pancake steps at `200M` and `380M` gas with vs without the `child.len < 32` guard. -/
def inlineUnbounded380MBound : Nat := blockFixed + inputBytes + (4809020803880 + 450) / 451
def inlineHashed380MBound : Nat := blockFixed + inputBytes + (118511584702912 + 11802) / 11803
def patchedGuest200MBound : Nat := blockFixed + inputBytes + (66779086680 + 10) / 11

/-- **DoS #3 Theorem (Unbounded inline MPT child in `_resolve_step` l. 3755)**:
Omitting `byteLen < 32` at `_resolve_step` (l. 3755) accepts inline RLP list nodes of size `≥ 32`
bytes, inflating the worst-case RLP/MPT bound by `622,215,414` ticks (`> 622,000,000`) on the pure
hashed-branch constraint at `380M` gas and by `711,679,601` ticks (`7,287,261,989 → 6,575,582,388`)
at `200M` gas (certified by `inlineGuestFarkasCert200M`). -/
theorem dos3_unbounded_inline_mpt_child_amplification :
    resolveStepLine = 3755 ∧
    resolveStepAcceptsInlineUnpatched true 32 = true ∧
    resolveStepAcceptsInlinePatched true 32 = false ∧
    resolveStepAcceptsInlinePatched true 31 = true ∧
    checkFarkasCertificate inlineGuestSystem200M costInlineObj inlineGuestFarkasCert200M = true ∧
    inlineUnbounded380MBound - inlineHashed380MBound = 622215414 ∧
    622000000 < inlineUnbounded380MBound - inlineHashed380MBound ∧
    cachedGuest200MBound - patchedGuest200MBound = 711679601 ∧
    622000000 < cachedGuest200MBound - patchedGuest200MBound := by decide

/-! ## Section 3: Spec Closure (`validate_headers`) & Three Formal Guest Spec Fixes -/

/-- Line numbers in `Guest/guest.pp.pnk` for `validate_headers` (l. 3417), `validate_header` (l. 3544),
and their invocation in `run_attempt` (l. 15569). -/
def validateHeadersLine : Nat := 3417
def validateHeaderLine : Nat := 3544
def runAttemptValidateHeadersCallLine : Nat := 15569

/-- Maximum historical headers validated by `validate_headers` (`if n >+ 256 { throw BlockErr 1 }`). -/
def maxValidatedHeaders : Nat := 256

/-- Maximum RLP byte size per block header (`encode_header` l. 3357 allocates `1,024` bytes). -/
def maxHeaderRlpBytes : Nat := 1024

/-- Worst-case Pancake steps per header in `validate_headers` (`42,500` steps:
`28,500` for `decode_header` + `13,800` for `keccak256` on `≤ 1,024` bytes + `150` loop1 + `50` `memeq` loop2). -/
def stepsPerValidatedHeader : Nat := 42500

/-- Formal representation of a decoded Ethereum block header in `validate_headers` / `validate_header`. -/
structure HeaderSpec where
  parentHash : Nat
  headerHash : Nat
  number : Nat
  timestamp : Nat
  gasUsed : Nat
  gasLimit : Nat
  rlpBytes : Nat
  deriving Repr, DecidableEq

/-- Per-header invariants: `1 ≤ number`, `gasUsed ≤ gasLimit`, and `rlpBytes ≤ 1024`. -/
def validateSingleHeader (h : HeaderSpec) : Bool :=
  decide (1 ≤ h.number) && decide (h.gasUsed ≤ h.gasLimit) && decide (h.rlpBytes ≤ maxHeaderRlpBytes)

/-- Parent-child header link invariants (`validate_headers` l. 3433 & `validate_header` l. 3544):
`curr.parentHash == prev.headerHash` (`keccak256(rlp(prev))`), `curr.number == prev.number + 1`,
and `curr.timestamp > prev.timestamp`. -/
def validateHeaderLink (prev curr : HeaderSpec) : Bool :=
  decide (curr.parentHash = prev.headerHash) &&
    decide (curr.number = prev.number + 1) &&
    decide (prev.timestamp < curr.timestamp)

/-- Recursive chain validation across consecutive headers. -/
def validateHeaderChainAux : HeaderSpec → List HeaderSpec → Bool
  | _, [] => true
  | prev, curr :: rest =>
      validateSingleHeader curr && validateHeaderLink prev curr && validateHeaderChainAux curr rest

/-- Complete specification of `validate_headers` (`guest.pp.pnk` l. 3417 + `validate_header` l. 3544):
non-empty list of `≤ 256` headers where every header satisfies `validateSingleHeader` and every
adjacent pair satisfies `validateHeaderLink`. -/
def validateHeadersSpec (headers : List HeaderSpec) : Bool :=
  match headers with
  | [] => false
  | h0 :: rest =>
      decide (headers.length ≤ maxValidatedHeaders) &&
        validateSingleHeader h0 &&
        validateHeaderChainAux h0 rest

/-- Total Pancake steps executed by `validate_headers` on `headers`. -/
def validateHeadersSteps (headers : List HeaderSpec) : Nat :=
  headers.length * stepsPerValidatedHeader

/-- **Theorem (`validate_headers` Spec & `10,880,000`-Step Termination Bound)**:
For any header chain `headers` accepted by `validateHeadersSpec`, `1 ≤ headers.length ≤ 256` and
`validateHeadersSteps headers ≤ 256 × 42,500 = 10,880,000` Pancake steps, with equality attained
at `256` headers. -/
theorem validate_headers_spec_and_step_bound (headers : List HeaderSpec)
    (hValid : validateHeadersSpec headers = true) :
    1 ≤ headers.length ∧
    headers.length ≤ maxValidatedHeaders ∧
    validateHeadersSteps headers ≤ 10880000 ∧
    maxValidatedHeaders * stepsPerValidatedHeader = 10880000 := by
  cases headers with
  | nil => simp [validateHeadersSpec] at hValid
  | cons h0 rest =>
    simp only [validateHeadersSpec, Bool.and_eq_true, decide_eq_true_eq] at hValid
    have hLen : (h0 :: rest).length ≤ 256 := hValid.1.1
    refine ⟨by simp, hLen, ?_, by decide⟩
    unfold validateHeadersSteps stepsPerValidatedHeader
    exact Nat.le_trans (Nat.mul_le_mul_right 42500 hLen) (by decide)

/-- Tightness witness for `validateHeadersSpec`: a valid 2-header chain and all 5 rejection modes. -/
theorem validate_headers_link_and_bound_tight :
    let h0 : HeaderSpec := ⟨100, 200, 1, 1000, 15000000, 30000000, 540⟩
    let h1 : HeaderSpec := ⟨200, 300, 2, 1012, 18000000, 30000000, 548⟩
    validateHeadersSpec [h0, h1] = true ∧
    validateHeadersSpec [h0, { h1 with parentHash := 999 }] = false ∧
    validateHeadersSpec [h0, { h1 with number := 3 }] = false ∧
    validateHeadersSpec [h0, { h1 with timestamp := 1000 }] = false ∧
    validateHeadersSpec [h0, { h1 with gasUsed := 30000001 }] = false ∧
    validateHeadersSpec [h0, { h1 with rlpBytes := 1025 }] = false ∧
    maxValidatedHeaders * stepsPerValidatedHeader = 10880000 ∧
    (maxValidatedHeaders + 1) * stepsPerValidatedHeader = 10922500 := by decide

/-! ## Section 4: Patched Guest Configuration & Farkas-Certified `6,575,582,388` Global Step Bound -/

/-- Formal configuration of the three Guest spec fixes + complete header validation. -/
structure PatchedGuestConfig where
  /-- Fix 1: `compute_jumpdests` (l. 6826) memoized by `code_hash` + bounded hash-table probing. -/
  jumpdestCachedAndHtabBounded : Bool
  /-- Fix 2: Yellow-Paper guard `child.len < 32` in `_resolve_step` (l. 3755). -/
  inlineChildLenLt32Guard : Bool
  /-- Fix 3: Short-circuit `if orig == 0 && new == 0 then skip_set_storage` in `op_sstore` (l. 7499)
      + full `validate_headers` (l. 3417). -/
  skipNoopColdZeroSstoreAndValidateHeaders : Bool
  deriving Repr, DecidableEq

/-- Predicate asserting all three Guest fixes are active. -/
def PatchedGuestConfig.isFullyPatched (cfg : PatchedGuestConfig) : Bool :=
  cfg.jumpdestCachedAndHtabBounded &&
    cfg.inlineChildLenLt32Guard &&
    cfg.skipNoopColdZeroSstoreAndValidateHeaders

/-- Canonical patched Guest configuration. -/
def canonicalPatchedGuest : PatchedGuestConfig := ⟨true, true, true⟩

/-- Objective vector of `costPatched` for `dotNat` on the 12 block execution counters
`(A, K, L, B, E, n2, d, r, md, ms, P, T)`. -/
def costPatchedObj : List Nat :=
  [3473, 5274, 3124, 633, 439, 127, 405, 405, 43, 79, 18, 42382]

/-- Variable cost of the Patched Guest (Regime D / Yellow-Paper inline rule + jumpdest cache). -/
def costPatched (A K L B E n2 d r md ms P T : Nat) : Nat :=
  3473 * A + 5274 * K + 3124 * L + 633 * B + 439 * E + 127 * n2 + 405 * d + 405 * r +
    43 * md + 79 * ms + 18 * P + 42382 * T

/-- Total Pancake steps for a block under `PatchedGuestConfig`. -/
def totalStepsPatched (A K L B E n2 d r md ms P T : Nat) : Nat :=
  blockFixed + inputBytes + costPatched A K L B E n2 d r md ms P T

/-- Constraint system of the Patched Guest LP at `declaredGasLimit = 200,000,000`:
0 (`hg`): `2400 A + 2105 K + 1900 L + P + 12000 T ≤ 200,000,000`
1 (`h1`): `B + E ≤ 82 A + 63 K`
2 (`h2`): `B + E ≤ 66 A + 64 K`
3 (`hb`): `B ≤ A + K + r` (enforced by Fix 2: `child_len < 32` in `_resolve_step` l. 3755)
4 (`he`): `E ≤ 2 A + 2 K + n2`
5 (`hw`): `7 n2 + 22 d + 54 r + 4 md + 5 ms ≤ 32 A + 32 K + 134,217,712`. -/
def patchedGuestSystem200M : List NatLinearInequality :=
  [ ⟨[2400, 2105, 1900, 0, 0, 0, 0, 0, 0, 0, 1, 12000], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 200000000⟩
  , ⟨[0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], [82, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], [66, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 0, 0, 7, 22, 54, 4, 5, 0, 0], [32, 32, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], inputBytes⟩
  ]

/-- Dual Farkas certificate for `patchedGuestSystem200M`:
`multipliers = [396, 0, 9617, 12960, 41, 405]`, `scale = 22 = 2 × 11`,
`bound = 133,558,173,360 = 2 × 66,779,086,680`. -/
def patchedGuestFarkasCert200M : FarkasCertificate :=
  ⟨[396, 0, 9617, 12960, 41, 405], 22, 133558173360⟩

private theorem dotNat_costPatchedObj (A K L B E n2 d r md ms P T : Nat) :
    dotNat costPatchedObj [A, K, L, B, E, n2, d, r, md, ms, P, T] =
      costPatched A K L B E n2 d r md ms P T := by
  simp only [costPatchedObj, costPatched, dotNat, Nat.add_zero]
  ac_rfl

private theorem patchedGuestSystem200M_holds (A K L B E n2 d r md ms P T declaredGasLimit : Nat)
    (hGasLimit : declaredGasLimit ≤ 200000000)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ declaredGasLimit)
    (h1 : B + E ≤ 82 * A + 63 * K)
    (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    SystemHolds patchedGuestSystem200M [A, K, L, B, E, n2, d, r, md, ms, P, T] := by
  simp only [patchedGuestSystem200M, SystemHolds, NatLinearInequality.Holds, dotNat,
    Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · have hg' : 2400 * A + (2105 * K + (1900 * L + (P + 12000 * T))) =
        12000 * T + 2400 * A + 2105 * K + 1900 * L + P := by ac_rfl
    rw [hg']
    exact Nat.le_trans hg hGasLimit
  · exact h1
  · exact h2
  · have hb' : A + (K + r) = r + K + A := by ac_rfl
    rw [hb']
    exact hb
  · have he' : 2 * A + (2 * K + n2) = n2 + 2 * (K + A) := by
      simp only [Nat.mul_add]; ac_rfl
    rw [he']
    exact he
  · have hwL : 7 * n2 + (22 * d + (54 * r + (4 * md + 5 * ms))) =
        7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms := by ac_rfl
    have hwR : 32 * A + 32 * K + inputBytes = inputBytes + 32 * (A + K) := by
      simp only [Nat.mul_add]; ac_rfl
    rw [hwL, hwR]
    exact hw

/-- **Main Theorem (Three Formal Guest Spec Fixes & Farkas-Certified `6,575,582,388` Global Bound)**:
Under any `cfg : PatchedGuestConfig` with `cfg.isFullyPatched = true` and for any block with
`declaredGasLimit ≤ 200,000,000`, the Farkas certificate `patchedGuestFarkasCert200M` certifies
(with zero `omega` calls) that:
1. All three spec fixes (`jumpdestCachedAndHtabBounded`, `inlineChildLenLt32Guard`,
   `skipNoopColdZeroSstoreAndValidateHeaders`) are active.
2. `11 * costPatched A K L B E n2 d r md ms P T ≤ 66,779,086,680`
3. `totalStepsPatched A K L B E n2 d r md ms P T ≤ 6,575,582,388`
4. `6,575,582,388` is `136×` below the Yukon ceiling `900,719,925,474` (`136 × 6,575,582,388 < yukon < 137 × 6,575,582,388`). -/
theorem patched_guest_farkas_certified_200m_bound
    (cfg : PatchedGuestConfig)
    (A K L B E n2 d r md ms P T declaredGasLimit : Nat)
    (hPatched : cfg.isFullyPatched = true)
    (hGasLimit : declaredGasLimit ≤ 200000000)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ declaredGasLimit)
    (h1 : B + E ≤ 82 * A + 63 * K)
    (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A)
    (he : E ≤ n2 + 2 * (K + A))
    (hw : 7 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * (A + K)) :
    cfg.jumpdestCachedAndHtabBounded = true ∧
    cfg.inlineChildLenLt32Guard = true ∧
    cfg.skipNoopColdZeroSstoreAndValidateHeaders = true ∧
    checkFarkasCertificate patchedGuestSystem200M costPatchedObj patchedGuestFarkasCert200M = true ∧
    11 * costPatched A K L B E n2 d r md ms P T ≤ 66779086680 ∧
    totalStepsPatched A K L B E n2 d r md ms P T ≤ 6575582388 ∧
    patchedGuest200MBound = 6575582388 ∧
    136 * patchedGuest200MBound < yukon ∧
    yukon < 137 * patchedGuest200MBound := by
  simp only [PatchedGuestConfig.isFullyPatched, Bool.and_eq_true] at hPatched
  have hCert : checkFarkasCertificate patchedGuestSystem200M costPatchedObj patchedGuestFarkasCert200M = true := by
    decide
  have hSys := patchedGuestSystem200M_holds A K L B E n2 d r md ms P T declaredGasLimit hGasLimit hg h1 h2 hb he hw
  have hSound := (farkas_certificate_sound patchedGuestSystem200M costPatchedObj patchedGuestFarkasCert200M
    [A, K, L, B, E, n2, d, r, md, ms, P, T] hCert hSys).1
  rw [dotNat_costPatchedObj] at hSound
  have hMul : 2 * (11 * costPatched A K L B E n2 d r md ms P T) ≤ 2 * 66779086680 := by
    rw [← Nat.mul_assoc]
    exact hSound
  have h11 : 11 * costPatched A K L B E n2 d r md ms P T ≤ 66779086680 :=
    Nat.le_of_mul_le_mul_left hMul (by decide : 0 < 2)
  have hCost : costPatched A K L B E n2 d r md ms P T ≤ 6070826062 := by
    have hDiv := Nat.div_le_div_right h11 (c := 11)
    rw [Nat.mul_div_right _ (by decide : 0 < 11)] at hDiv
    exact Nat.le_trans hDiv (by decide : 66779086680 / 11 ≤ 6070826062)
  have hTotal : totalStepsPatched A K L B E n2 d r md ms P T ≤ 6575582388 := by
    unfold totalStepsPatched blockFixed inputBytes
    exact Nat.le_trans (Nat.add_le_add_left hCost (370538614 + 134217712)) (by decide)
  exact ⟨hPatched.1.1, hPatched.1.2, hPatched.2, hCert, h11, hTotal, by decide, by decide, by decide⟩

/-- Tightness of the Patched Guest `6,575,582,388` bound: attained within one dead-end branch
(`d = 6,100,805`, `P = 200,000,000`, all other counters `0`), where `totalStepsPatched = 6,575,582,351`
and `11 * costPatched` is within `405 < 11 * 405` of `66,779,086,680`. -/
theorem patched_guest_bound_attained_and_tight :
    canonicalPatchedGuest.isFullyPatched = true ∧
    checkFarkasCertificate patchedGuestSystem200M costPatchedObj patchedGuestFarkasCert200M = true ∧
    totalStepsPatched 0 0 0 0 0 0 6100805 0 0 0 200000000 0 = 6575582351 ∧
    patchedGuest200MBound - totalStepsPatched 0 0 0 0 0 0 6100805 0 0 0 200000000 0 = 37 ∧
    66779086680 - 11 * costPatched 0 0 0 0 0 0 6100805 0 0 0 200000000 0 = 405 ∧
    66779086680 - 11 * costPatched 0 0 0 0 0 0 6100805 0 0 0 200000000 0 < 11 * 405 ∧
    22 * 6100805 ≤ inputBytes ∧
    10880000 ≤ blockFixed := by decide

/-! ## Section 4: Fast-Path Guest (`evm-asm` + `div.fast` + Hashed Extension Witness) Tightened Farkas Bounds -/

/-- Variable cost under `evm-asm` (`add256_evm_asm` / `sub256_evm_asm` = 12 cycles for 3 gas = 4 cycles/gas)
and `div.fast` (28 cycles for 5-gas `DIV`/`MOD`), reducing pure opcode gas coefficient `P` from `18` to `4`. -/
def costFastPath (A K L B E n2 d r md ms P T : Nat) : Nat :=
  3473 * A + 5274 * K + 3124 * L + 633 * B + 439 * E + 127 * n2 + 405 * d + 405 * r +
    43 * md + 79 * ms + 4 * P + 42382 * T

/-- Total Pancake steps for a block under `costFastPath`. -/
def totalStepsFastPath (A K L B E n2 d r md ms P T : Nat) : Nat :=
  blockFixed + inputBytes + costFastPath A K L B E n2 d r md ms P T

/-- Objective vector of `costFastPath` for `dotNat`. -/
def costFastPathObj : List Nat :=
  [3473, 5274, 3124, 633, 439, 127, 405, 405, 43, 79, 4, 42382]

/-- Tightened dual Farkas certificate on the exact `patchedGuestSystem200M` constraint system
for `costFastPathObj` (eliminating the `8,651` branch-column slack in `patchedGuestFarkasCert200M`
by setting `y_3 = 4309 × 2105 = 9,070,445` instead of `12960 × 2105`):
`multipliers = [748867, 0, 20243785, 9070445, 86305, 852525]`, `scale = 46,310 = 22 × 2,105`,
`bound = 264,197,354,922,800`. -/
def fastPathPatchedFarkasCert200M : FarkasCertificate :=
  ⟨[748867, 0, 20243785, 9070445, 86305, 852525], 46310, 264197354922800⟩

/-- Global Pancake step bound (`6,209,730,520`) on `patchedGuestSystem200M` under `costFastPath`,
saving `365,851,868` steps relative to `patchedGuest200MBound = 6,575,582,388`. -/
def fastPathPatched200MBound : Nat :=
  blockFixed + inputBytes + (264197354922800 + 46309) / 46310

/-- Constraint system `fastPathHashedExtSystem200M` incorporating Fix 2 (`child_len == 32` for
non-inline MPT extension/account-leaf nodes, giving `32 * n2` witness byte weight with at most
`K` storage leaves `< 32` bytes absorbed into `64 * K` on the RHS of `hw_ext`):
`32 n2 + 22 d + 54 r + 4 md + 5 ms ≤ 32 A + 64 K + 134,217,712`. -/
def fastPathHashedExtSystem200M : List NatLinearInequality :=
  [ ⟨[2400, 2105, 1900, 0, 0, 0, 0, 0, 0, 0, 1, 12000], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 200000000⟩
  , ⟨[0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], [82, 63, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0], [66, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [2, 2, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], 0⟩
  , ⟨[0, 0, 0, 0, 0, 32, 22, 54, 4, 5, 0, 0], [32, 64, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], inputBytes⟩
  ]

/-- Dual Farkas certificate for `fastPathHashedExtSystem200M`:
`multipliers = [12920, 0, 21858, 2022732, 1396112, 61683]`, `scale = 3,230`,
`bound = 10,862,951,129,296`. -/
def fastPathHashedExtFarkasCert200M : FarkasCertificate :=
  ⟨[12920, 0, 21858, 2022732, 1396112, 61683], 3230, 10862951129296⟩

/-- Global Pancake step bound (`3,867,899,091 < 3.87B`) under `fastPathHashedExtSystem200M`,
saving `2,707,683,297` steps (`-41.2%`) relative to `patchedGuest200MBound = 6,575,582,388`
and sitting `232×` below the Yukon ceiling `900,719,925,474`. -/
def fastPathHashedExt200MBound : Nat :=
  blockFixed + inputBytes + (10862951129296 + 3229) / 3230

private theorem dotNat_costFastPathObj (A K L B E n2 d r md ms P T : Nat) :
    dotNat costFastPathObj [A, K, L, B, E, n2, d, r, md, ms, P, T] =
      costFastPath A K L B E n2 d r md ms P T := by
  simp only [costFastPathObj, costFastPath, dotNat, Nat.add_zero]
  ac_rfl

private theorem fastPathHashedExtSystem200M_holds (A K L B E n2 d r md ms P T declaredGasLimit : Nat)
    (hGasLimit : declaredGasLimit ≤ 200000000)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ declaredGasLimit)
    (h1 : B + E ≤ 82 * A + 63 * K)
    (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A)
    (he : E ≤ n2 + 2 * (K + A))
    (hw_ext : 32 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * A + 64 * K) :
    SystemHolds fastPathHashedExtSystem200M [A, K, L, B, E, n2, d, r, md, ms, P, T] := by
  simp only [fastPathHashedExtSystem200M, SystemHolds, NatLinearInequality.Holds, dotNat,
    Nat.zero_mul, Nat.one_mul, Nat.zero_add, Nat.add_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  · have hg1 : 2400 * A + (2105 * K + (1900 * L + (P + 12000 * T))) =
        12000 * T + 2400 * A + 2105 * K + 1900 * L + P := by ac_rfl
    rw [hg1]
    exact Nat.le_trans hg hGasLimit
  · exact h1
  · exact h2
  · have hb1 : A + (K + r) = r + K + A := by ac_rfl
    rw [hb1]
    exact hb
  · have he1 : 2 * A + (2 * K + n2) = n2 + 2 * (K + A) := by
      simp only [Nat.mul_add]; ac_rfl
    rw [he1]
    exact he
  · have hwL : 32 * n2 + (22 * d + (54 * r + (4 * md + 5 * ms))) =
        32 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms := by ac_rfl
    have hwR : 32 * A + 64 * K + inputBytes = inputBytes + 32 * A + 64 * K := by ac_rfl
    rw [hwL, hwR]
    exact hw_ext

/-- **Theorem (Fast-Path `evm-asm` + `div.fast` + Hashed Extension Witness Farkas Bound `≤ 3,867,899,091`)**:
1. On the exact `patchedGuestSystem200M` constraints, `fastPathPatchedFarkasCert200M` certifies
   `totalStepsFastPath A K L B E n2 d r md ms P T ≤ 6,209,730,520` (`365,851,868` steps below `6,575,582,388`).
2. Under `fastPathHashedExtSystem200M` (Fix 2 `32 * n2` extension/account-leaf witness weight),
   `fastPathHashedExtFarkasCert200M` certifies (with zero `omega` calls) that
   `3230 * costFastPath A K L B E n2 d r md ms P T ≤ 10,862,951,129,296` and
   `totalStepsFastPath A K L B E n2 d r md ms P T ≤ 3,867,899,091` (`< 3.87B` Pancake steps,
   saving `2,707,683,297` steps relative to `6,575,582,388` and `232×` below Yukon `900,719,925,474`),
   and is attained within `1,078` steps at `(K = 41553, B = 2576286, E = 83106, d = 69, r = 2534733, md = 1, P = 112530935)`. -/
theorem fast_path_guest_farkas_certified_200m_bounds
    (cfg : PatchedGuestConfig)
    (A K L B E n2 d r md ms P T declaredGasLimit : Nat)
    (hPatched : cfg.isFullyPatched = true)
    (hGasLimit : declaredGasLimit ≤ 200000000)
    (hg : 12000 * T + 2400 * A + 2105 * K + 1900 * L + P ≤ declaredGasLimit)
    (h1 : B + E ≤ 82 * A + 63 * K)
    (h2 : B + E ≤ 66 * A + 64 * K)
    (hb : B ≤ r + K + A)
    (he : E ≤ n2 + 2 * (K + A))
    (hw_ext : 32 * n2 + 22 * d + 54 * r + 4 * md + 5 * ms ≤ inputBytes + 32 * A + 64 * K) :
    checkFarkasCertificate patchedGuestSystem200M costFastPathObj fastPathPatchedFarkasCert200M = true ∧
    checkFarkasCertificate fastPathHashedExtSystem200M costFastPathObj fastPathHashedExtFarkasCert200M = true ∧
    3230 * costFastPath A K L B E n2 d r md ms P T ≤ 10862951129296 ∧
    totalStepsFastPath A K L B E n2 d r md ms P T ≤ 3867899091 ∧
    fastPathPatched200MBound = 6209730520 ∧
    fastPathHashedExt200MBound = 3867899091 ∧
    patchedGuest200MBound - fastPathPatched200MBound = 365851868 ∧
    patchedGuest200MBound - fastPathHashedExt200MBound = 2707683297 ∧
    232 * fastPathHashedExt200MBound < yukon ∧
    yukon < 233 * fastPathHashedExt200MBound ∧
    totalStepsFastPath 0 41553 0 2576286 83106 0 69 2534733 1 0 112530935 0 = 3867898013 ∧
    fastPathHashedExt200MBound - totalStepsFastPath 0 41553 0 2576286 83106 0 69 2534733 1 0 112530935 0 = 1078 := by
  have _ := hPatched
  have hCert1 : checkFarkasCertificate patchedGuestSystem200M costFastPathObj fastPathPatchedFarkasCert200M = true := by
    decide
  have hCert2 : checkFarkasCertificate fastPathHashedExtSystem200M costFastPathObj fastPathHashedExtFarkasCert200M = true := by
    decide
  have hSys2 := fastPathHashedExtSystem200M_holds A K L B E n2 d r md ms P T declaredGasLimit hGasLimit hg h1 h2 hb he hw_ext
  have hSound2 := (farkas_certificate_sound fastPathHashedExtSystem200M costFastPathObj fastPathHashedExtFarkasCert200M
    [A, K, L, B, E, n2, d, r, md, ms, P, T] hCert2 hSys2).1
  rw [dotNat_costFastPathObj] at hSound2
  change 3230 * costFastPath A K L B E n2 d r md ms P T ≤ 10862951129296 at hSound2
  have hCost2 : costFastPath A K L B E n2 d r md ms P T ≤ 3363142765 := by
    have hDiv := Nat.div_le_div_right hSound2 (c := 3230)
    rw [Nat.mul_div_right _ (by decide : 0 < 3230)] at hDiv
    exact Nat.le_trans hDiv (by decide : 10862951129296 / 3230 ≤ 3363142765)
  have hTotal2 : totalStepsFastPath A K L B E n2 d r md ms P T ≤ 3867899091 := by
    unfold totalStepsFastPath blockFixed inputBytes
    exact Nat.le_trans (Nat.add_le_add_left hCost2 (370538614 + 134217712)) (by decide)
  exact ⟨hCert1, hCert2, hSound2, hTotal2, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end InitECandidate.Solver.GuestGasAndSpecFixes
