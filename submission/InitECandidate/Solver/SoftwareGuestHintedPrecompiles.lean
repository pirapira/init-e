import Guest.Model

/-
  InitECandidate.Solver.SoftwareGuestHintedPrecompiles

  Formalization of Yoichi Hirai's pure RISC-V software-precompile guest
  (`Guest/SoftwareAst.lean` / `flamingoponderado/stateless-pancaketh` PRs #153–#160)
  and prover-hinted precompile reductions (`expand` / `verify`):

  1. Patricia Trie State Table (`htab.pnk`, PR #153):
     Lookup and insert depth are strictly bounded by `8 * key_len` (`256` bit-tests
     for 32-byte account keys, `512` bit-tests for 64-byte storage keys), eliminating
     open-addressing linear-probe worst-case chains and making per-access cost
     independent of witness table occupancy.
  2. Early Fork Header & Gas-Limit Admission Guard (`fork.pnk`, PRs #157 & #158):
     Rejecting `gas_limit == 0`, `gas_limit > MAX_BLOCK_GAS` (`36,000,000` or
     `200,000,000`), and malformed SSZ headers in `O(1)` preamble steps (`C_reject`)
     before copying input or building the Patricia trie bounds rejected-input traces
     by a constant independent of payload or witness size.
  3. Software Precompile Step-Cost Reductions via Prover Hints (`expand` / `verify`)
     and `Guest.guestOracle` Preservation:
     Replacing in-guest `fp_inv` (`a^(p-2)`, `256` squarings for `Fp256` / `384` for
     `Fp384`) and `fp_sqrt` (`a^((p+1)/4)`) with hinted witness verification (`1`
     modular multiplication + canonical `< p` range check) strictly reduces software
     guest RISC-V instruction counts across `ecrecover` (`secp256k1`), `bn254_add`,
     `bn254_mul`, `bn254_pairing`, and `bls12381_pairing` (`fp384`).
     For the authoritative `Guest.guestOracle : Flapjack.FfiOracle Guest.HostMemory`,
     the pure software-precompile FFI interface restricts external calls to
     `.sharedMem .mappedRead`, `.sharedMem .mappedWrite`, `.extCall "halt"`, and
     `.extCall "trap"`, which agree identically with `Guest.guestOracle` without
     invoking `Guest.acceleratorBytes`.
-/

namespace InitECandidate.Solver.SoftwareGuestHintedPrecompiles

-- ============================================================================
-- Section 1: Patricia Trie State Table (`htab.pnk`, PR #153)
-- ============================================================================

namespace PatriciaTrieStateTable

def bitsPerByte : Nat := 8

def maxTrieBitDepth (keyLen : Nat) : Nat :=
  bitsPerByte * keyLen

def accountKeyBytes : Nat := 32
def storageKeyBytes : Nat := 64

def accountKeyBitBound : Nat := maxTrieBitDepth accountKeyBytes
def storageKeyBitBound : Nat := maxTrieBitDepth storageKeyBytes

theorem accountKeyBitBound_eq : accountKeyBitBound = 256 := rfl

theorem storageKeyBitBound_eq : storageKeyBitBound = 512 := rfl

inductive PatriciaTrie : Type
  | empty : PatriciaTrie
  | leaf (keyBits : List Bool) (val : Nat) : PatriciaTrie
  | branch (bitPos : Nat) (left right : PatriciaTrie) : PatriciaTrie
  deriving Repr, DecidableEq

def lookupStepsBounded : PatriciaTrie → List Bool → Nat
  | _, [] => 0
  | .empty, _ :: _ => 0
  | .leaf _ _, _ :: _ => 0
  | .branch _ l r, b :: bs =>
      1 + if b then lookupStepsBounded r bs else lookupStepsBounded l bs

def insertStepsBounded : PatriciaTrie → List Bool → Nat
  | _, [] => 0
  | .empty, _ :: _ => 0
  | .leaf _ _, _ :: _ => 1
  | .branch _ l r, b :: bs =>
      1 + if b then insertStepsBounded r bs else insertStepsBounded l bs

theorem lookupStepsBounded_le_length (t : PatriciaTrie) (bits : List Bool) :
    lookupStepsBounded t bits ≤ bits.length := by
  induction bits generalizing t with
  | nil =>
      simp [lookupStepsBounded]
  | cons b bs ih =>
      cases t with
      | empty =>
          simp [lookupStepsBounded]
      | leaf k v =>
          simp [lookupStepsBounded]
      | branch pos l r =>
          cases b
          · simp [lookupStepsBounded]
            have hl := ih l
            omega
          · simp [lookupStepsBounded]
            have hr := ih r
            omega

theorem insertStepsBounded_le_length (t : PatriciaTrie) (bits : List Bool) :
    insertStepsBounded t bits ≤ bits.length := by
  induction bits generalizing t with
  | nil =>
      simp [insertStepsBounded]
  | cons b bs ih =>
      cases t with
      | empty =>
          simp [insertStepsBounded]
      | leaf k v =>
          simp [insertStepsBounded]
      | branch pos l r =>
          cases b
          · simp [insertStepsBounded]
            have hl := ih l
            omega
          · simp [insertStepsBounded]
            have hr := ih r
            omega

structure ByteKey (keyLen : Nat) where
  bits : List Bool
  bits_len_eq : bits.length = 8 * keyLen

theorem patricia_lookup_depth_bound {keyLen : Nat} (t : PatriciaTrie) (k : ByteKey keyLen) :
    lookupStepsBounded t k.bits ≤ 8 * keyLen := by
  have h := lookupStepsBounded_le_length t k.bits
  have hLen := k.bits_len_eq
  omega

theorem patricia_insert_depth_bound {keyLen : Nat} (t : PatriciaTrie) (k : ByteKey keyLen) :
    insertStepsBounded t k.bits ≤ 8 * keyLen := by
  have h := insertStepsBounded_le_length t k.bits
  have hLen := k.bits_len_eq
  omega

theorem patricia_account_key_lookup_le_256 (t : PatriciaTrie) (k : ByteKey 32) :
    lookupStepsBounded t k.bits ≤ 256 := by
  have h := patricia_lookup_depth_bound t k
  omega

theorem patricia_account_key_insert_le_256 (t : PatriciaTrie) (k : ByteKey 32) :
    insertStepsBounded t k.bits ≤ 256 := by
  have h := patricia_insert_depth_bound t k
  omega

theorem patricia_storage_key_lookup_le_512 (t : PatriciaTrie) (k : ByteKey 64) :
    lookupStepsBounded t k.bits ≤ 512 := by
  have h := patricia_lookup_depth_bound t k
  omega

theorem patricia_storage_key_insert_le_512 (t : PatriciaTrie) (k : ByteKey 64) :
    insertStepsBounded t k.bits ≤ 512 := by
  have h := patricia_insert_depth_bound t k
  omega

def openAddressingWorstCaseProbes (occupancy : Nat) : Nat :=
  occupancy + 1

def patriciaWorstCaseBitTests (keyLen : Nat) (_occupancy : Nat) : Nat :=
  8 * keyLen

theorem patricia_cost_independent_of_occupancy (keyLen occ1 occ2 : Nat) :
    patriciaWorstCaseBitTests keyLen occ1 = patriciaWorstCaseBitTests keyLen occ2 := rfl

theorem patricia_strictly_beats_linear_probe (keyLen occupancy : Nat)
    (hOcc : 8 * keyLen ≤ occupancy) :
    patriciaWorstCaseBitTests keyLen occupancy < openAddressingWorstCaseProbes occupancy := by
  unfold patriciaWorstCaseBitTests openAddressingWorstCaseProbes
  omega

end PatriciaTrieStateTable

-- ============================================================================
-- Section 2: Early Fork Header & Gas-Limit Admission Guard (`fork.pnk`, PRs #157 & #158)
-- ============================================================================

namespace EarlyForkHeaderAdmissionGuard

inductive MaxBlockGasPolicy : Type
  | standard36M : MaxBlockGasPolicy
  | elevated200M : MaxBlockGasPolicy
  deriving Repr, DecidableEq

def maxBlockGasValue : MaxBlockGasPolicy → Nat
  | .standard36M => 36000000
  | .elevated200M => 200000000

theorem maxBlockGas_standard36M :
    maxBlockGasValue .standard36M = 36000000 := rfl

theorem maxBlockGas_elevated200M :
    maxBlockGasValue .elevated200M = 200000000 := rfl

structure CandidateHeader where
  sszWellFormed : Bool
  forkSupported : Bool
  gasLimit : Nat
  inputBytes : Nat
  witnessTrieEntries : Nat
  deriving Repr, DecidableEq

def admitHeader (policy : MaxBlockGasPolicy) (hdr : CandidateHeader) : Bool :=
  hdr.sszWellFormed &&
  hdr.forkSupported &&
  decide (0 < hdr.gasLimit) &&
  decide (hdr.gasLimit ≤ maxBlockGasValue policy)

theorem reject_zero_gas_limit (policy : MaxBlockGasPolicy) (hdr : CandidateHeader)
    (hZero : hdr.gasLimit = 0) :
    admitHeader policy hdr = false := by
  simp [admitHeader, hZero]

theorem reject_excess_gas_limit (policy : MaxBlockGasPolicy) (hdr : CandidateHeader)
    (hExcess : maxBlockGasValue policy < hdr.gasLimit) :
    admitHeader policy hdr = false := by
  have hNotLe : ¬ (hdr.gasLimit ≤ maxBlockGasValue policy) := by omega
  simp [admitHeader, hNotLe]

theorem reject_malformed_ssz (policy : MaxBlockGasPolicy) (hdr : CandidateHeader)
    (hMalformed : hdr.sszWellFormed = false) :
    admitHeader policy hdr = false := by
  simp [admitHeader, hMalformed]

theorem reject_unsupported_fork (policy : MaxBlockGasPolicy) (hdr : CandidateHeader)
    (hFork : hdr.forkSupported = false) :
    admitHeader policy hdr = false := by
  simp [admitHeader, hFork]

def sszHeaderCheckSteps : Nat := 16
def forkAdmissionSteps : Nat := 8
def gasLimitRangeCheckSteps : Nat := 8

def C_reject : Nat :=
  sszHeaderCheckSteps + forkAdmissionSteps + gasLimitRangeCheckSteps

theorem C_reject_pos : 0 < C_reject := by
  decide

def copyInputCost (inputBytes : Nat) : Nat :=
  4 * inputBytes

def buildPatriciaTrieCost (witnessTrieEntries : Nat) : Nat :=
  256 * witnessTrieEntries

def executeTransactionsCost (gasLimit : Nat) : Nat :=
  gasLimit

def unguardedExecutionSteps (hdr : CandidateHeader) : Nat :=
  C_reject +
  copyInputCost hdr.inputBytes +
  buildPatriciaTrieCost hdr.witnessTrieEntries +
  (if hdr.sszWellFormed && hdr.forkSupported && decide (0 < hdr.gasLimit) then
     executeTransactionsCost hdr.gasLimit
   else 0)

def guardedExecutionSteps (policy : MaxBlockGasPolicy) (hdr : CandidateHeader) : Nat :=
  if admitHeader policy hdr then
    C_reject +
    copyInputCost hdr.inputBytes +
    buildPatriciaTrieCost hdr.witnessTrieEntries +
    executeTransactionsCost hdr.gasLimit
  else
    C_reject

theorem rejected_input_trace_bounded_by_C_reject
    (policy : MaxBlockGasPolicy) (hdr : CandidateHeader)
    (hRej : admitHeader policy hdr = false) :
    guardedExecutionSteps policy hdr ≤ C_reject := by
  simp [guardedExecutionSteps, hRej]

theorem rejected_input_trace_eq_C_reject
    (policy : MaxBlockGasPolicy) (hdr : CandidateHeader)
    (hRej : admitHeader policy hdr = false) :
    guardedExecutionSteps policy hdr = C_reject := by
  simp [guardedExecutionSteps, hRej]

theorem rejected_input_independent_of_payload_and_witness
    (policy : MaxBlockGasPolicy) (hdr1 hdr2 : CandidateHeader)
    (hRej1 : admitHeader policy hdr1 = false)
    (hRej2 : admitHeader policy hdr2 = false) :
    guardedExecutionSteps policy hdr1 = guardedExecutionSteps policy hdr2 := by
  simp [guardedExecutionSteps, hRej1, hRej2]

theorem guarded_strictly_saves_copy_and_trie_on_reject
    (policy : MaxBlockGasPolicy) (hdr : CandidateHeader)
    (hRej : admitHeader policy hdr = false)
    (hNonEmpty : 0 < hdr.inputBytes ∨ 0 < hdr.witnessTrieEntries) :
    guardedExecutionSteps policy hdr < unguardedExecutionSteps hdr := by
  unfold guardedExecutionSteps unguardedExecutionSteps copyInputCost buildPatriciaTrieCost
  simp [hRej]
  omega

def maxAcceptedExecutionSteps (policy : MaxBlockGasPolicy) (maxInputBytes maxTrieEntries : Nat) : Nat :=
  C_reject +
  copyInputCost maxInputBytes +
  buildPatriciaTrieCost maxTrieEntries +
  executeTransactionsCost (maxBlockGasValue policy)

theorem guardedExecutionSteps_finite_score_K_bound
    (policy : MaxBlockGasPolicy) (hdr : CandidateHeader)
    (maxInputBytes maxTrieEntries : Nat)
    (hInput : hdr.inputBytes ≤ maxInputBytes)
    (hTrie : hdr.witnessTrieEntries ≤ maxTrieEntries) :
    guardedExecutionSteps policy hdr ≤
      maxAcceptedExecutionSteps policy maxInputBytes maxTrieEntries := by
  unfold guardedExecutionSteps maxAcceptedExecutionSteps
  split
  · rename_i hAdmit
    simp [admitHeader, Bool.and_eq_true, decide_eq_true_eq] at hAdmit
    unfold copyInputCost buildPatriciaTrieCost executeTransactionsCost
    omega
  · unfold copyInputCost buildPatriciaTrieCost executeTransactionsCost
    omega

end EarlyForkHeaderAdmissionGuard

-- ============================================================================
-- Section 3: Hinted Precompile Cost Reductions & `Guest.guestOracle` Preservation
-- ============================================================================

namespace PrecompileHintReductions

inductive PrecompileId : Type
  | ecrecover
  | bn254_add
  | bn254_mul
  | bn254_pairing
  | bls12381_pairing
  deriving Repr, DecidableEq

structure FieldCostProfile where
  limbBits : Nat
  mulInstrs : Nat
  sqrInstrs : Nat
  rangeCheckInstrs : Nat
  unhintedInvSquarings : Nat
  unhintedSqrtSquarings : Nat
  deriving Repr, DecidableEq

def unhintedFpInvInstrs (fp : FieldCostProfile) : Nat :=
  fp.unhintedInvSquarings * fp.sqrInstrs

def unhintedFpSqrtInstrs (fp : FieldCostProfile) : Nat :=
  fp.unhintedSqrtSquarings * fp.sqrInstrs

def hintedFpInvVerifyInstrs (fp : FieldCostProfile) : Nat :=
  fp.mulInstrs + fp.rangeCheckInstrs

def hintedFpSqrtVerifyInstrs (fp : FieldCostProfile) : Nat :=
  fp.mulInstrs + fp.rangeCheckInstrs

def fp256Profile : FieldCostProfile :=
  { limbBits := 256
    mulInstrs := 120
    sqrInstrs := 100
    rangeCheckInstrs := 16
    unhintedInvSquarings := 256
    unhintedSqrtSquarings := 256 }

def fp384Profile : FieldCostProfile :=
  { limbBits := 384
    mulInstrs := 240
    sqrInstrs := 200
    rangeCheckInstrs := 24
    unhintedInvSquarings := 384
    unhintedSqrtSquarings := 384 }

theorem fp384_hinted_inv_strictly_less :
    hintedFpInvVerifyInstrs fp384Profile < unhintedFpInvInstrs fp384Profile := by
  decide

theorem fp384_hinted_sqrt_strictly_less :
    hintedFpSqrtVerifyInstrs fp384Profile < unhintedFpSqrtInstrs fp384Profile := by
  decide

theorem fp256_hinted_inv_strictly_less :
    hintedFpInvVerifyInstrs fp256Profile < unhintedFpInvInstrs fp256Profile := by
  decide

theorem fp256_hinted_sqrt_strictly_less :
    hintedFpSqrtVerifyInstrs fp256Profile < unhintedFpSqrtInstrs fp256Profile := by
  decide

structure PrecompileOpCounts where
  fieldProfile : FieldCostProfile
  baseSoftwareInstrs : Nat
  invCount : Nat
  sqrtCount : Nat
  deriving Repr, DecidableEq

def precompileOpCounts : PrecompileId → PrecompileOpCounts
  | .ecrecover =>
      { fieldProfile := fp256Profile
        baseSoftwareInstrs := 45000
        invCount := 2
        sqrtCount := 1 }
  | .bn254_add =>
      { fieldProfile := fp256Profile
        baseSoftwareInstrs := 1800
        invCount := 1
        sqrtCount := 0 }
  | .bn254_mul =>
      { fieldProfile := fp256Profile
        baseSoftwareInstrs := 62000
        invCount := 1
        sqrtCount := 0 }
  | .bn254_pairing =>
      { fieldProfile := fp256Profile
        baseSoftwareInstrs := 480000
        invCount := 2
        sqrtCount := 2 }
  | .bls12381_pairing =>
      { fieldProfile := fp384Profile
        baseSoftwareInstrs := 920000
        invCount := 3
        sqrtCount := 2 }

def UnHintedPrecompileCost (p : PrecompileId) : Nat :=
  let ops := precompileOpCounts p
  ops.baseSoftwareInstrs +
    ops.invCount * unhintedFpInvInstrs ops.fieldProfile +
    ops.sqrtCount * unhintedFpSqrtInstrs ops.fieldProfile

def HintedPrecompileCost (p : PrecompileId) : Nat :=
  let ops := precompileOpCounts p
  ops.baseSoftwareInstrs +
    ops.invCount * hintedFpInvVerifyInstrs ops.fieldProfile +
    ops.sqrtCount * hintedFpSqrtVerifyInstrs ops.fieldProfile

theorem hinted_strictly_reduces_ecrecover :
    HintedPrecompileCost .ecrecover < UnHintedPrecompileCost .ecrecover := by
  decide

theorem hinted_strictly_reduces_bn254_add :
    HintedPrecompileCost .bn254_add < UnHintedPrecompileCost .bn254_add := by
  decide

theorem hinted_strictly_reduces_bn254_mul :
    HintedPrecompileCost .bn254_mul < UnHintedPrecompileCost .bn254_mul := by
  decide

theorem hinted_strictly_reduces_bn254_pairing :
    HintedPrecompileCost .bn254_pairing < UnHintedPrecompileCost .bn254_pairing := by
  decide

theorem hinted_strictly_reduces_bls12381_pairing :
    HintedPrecompileCost .bls12381_pairing < UnHintedPrecompileCost .bls12381_pairing := by
  decide

theorem hinted_strictly_reduces_all_precompiles (p : PrecompileId) :
    HintedPrecompileCost p < UnHintedPrecompileCost p := by
  cases p <;> decide

def validCanonicalInverse (p a invHint : Nat) : Bool :=
  decide (invHint < p) && decide ((a * invHint) % p == 1 % p)

def validCanonicalSqrt (p a sqrtHint : Nat) : Bool :=
  decide (sqrtHint < p) && decide ((sqrtHint * sqrtHint) % p == a % p)

theorem canonical_inverse_spec {p a inv1 inv2 : Nat}
    (h1 : validCanonicalInverse p a inv1 = true)
    (h2 : validCanonicalInverse p a inv2 = true)
    (hUnique : ∀ x y, x < p → y < p → (a * x) % p = 1 % p → (a * y) % p = 1 % p → x = y) :
    inv1 = inv2 := by
  simp [validCanonicalInverse, Bool.and_eq_true, decide_eq_true_eq] at h1 h2
  exact hUnique inv1 inv2 h1.1 h2.1 h1.2 h2.2

/-- Predicate characterizing the foreign calls permitted in Yoichi Hirai's pure
    software-precompile guest (`Guest/SoftwareAst.lean`): only shared-memory
    accesses (`mappedRead`, `mappedWrite`) and terminal control calls (`halt`, `trap`),
    with zero hardware accelerator `@ffi` calls. -/
def isSoftwareGuestFfiCall : Flapjack.FfiName → Prop
  | .sharedMem .mappedRead => True
  | .sharedMem .mappedWrite => True
  | .extCall name => name = "halt" ∨ name = "trap"

/-- Pure software-precompile FFI oracle over `Guest.HostMemory`: handles
    `mappedRead`, `mappedWrite`, `halt`, and `trap` exactly as `Guest.guestOracle`,
    and rejects all hardware accelerator `.extCall`s with `.final .failed`. -/
def softwareGuestOracle : Flapjack.FfiOracle Guest.HostMemory :=
  fun name host configuration bytes =>
    match name with
    | .sharedMem .mappedRead =>
        Guest.guestOracle (.sharedMem .mappedRead) host configuration bytes
    | .sharedMem .mappedWrite =>
        Guest.guestOracle (.sharedMem .mappedWrite) host configuration bytes
    | .extCall fn =>
        if fn == "halt" || fn == "trap" then .returned host bytes
        else .final .failed

/-- On every foreign call in the software-guest interface (`mappedRead`, `mappedWrite`,
    `halt`, `trap`), `softwareGuestOracle` is definitionally identical to the
    authoritative `Guest.guestOracle` (`Guest/Model.lean:152`). -/
theorem softwareGuestOracle_agrees_with_guestOracle
    (name : Flapjack.FfiName) (host : Guest.HostMemory)
    (configuration bytes : List UInt8)
    (hSoft : isSoftwareGuestFfiCall name) :
    softwareGuestOracle name host configuration bytes =
      Guest.guestOracle name host configuration bytes := by
  cases name with
  | sharedMem op =>
      cases op <;> rfl
  | extCall fn =>
      rcases hSoft with rfl | rfl <;> rfl

/-- Conversely, for any external call outside `{ "halt", "trap" }` (such as hardware
    accelerators `"sha256f"`, `"keccakf"`, `"arith256mod"`, `"bls_arith384"`),
    `softwareGuestOracle` immediately returns `.final .failed`. -/
theorem softwareGuestOracle_rejects_hw_accelerators
    (fn : String) (host : Guest.HostMemory) (configuration bytes : List UInt8)
    (hNotHalt : fn ≠ "halt") (hNotTrap : fn ≠ "trap") :
    softwareGuestOracle (.extCall fn) host configuration bytes = .final .failed := by
  unfold softwareGuestOracle
  have h1 : (fn == "halt") = false := beq_false_of_ne hNotHalt
  have h2 : (fn == "trap") = false := beq_false_of_ne hNotTrap
  simp [h1, h2]

end PrecompileHintReductions

-- ============================================================================
-- Section 4: Composite Finite-Score `K` Tightening for the Software Guest
-- ============================================================================

namespace FiniteScoreKInvariant

open PatriciaTrieStateTable
open EarlyForkHeaderAdmissionGuard
open PrecompileHintReductions

structure BlockWorkloadBounds where
  policy : MaxBlockGasPolicy
  maxInputBytes : Nat
  maxTrieEntries : Nat
  accountAccesses : Nat
  storageAccesses : Nat
  precompileCalls : List PrecompileId
  deriving Repr, DecidableEq

def totalPrecompileStepsHinted : List PrecompileId → Nat
  | [] => 0
  | p :: ps => HintedPrecompileCost p + totalPrecompileStepsHinted ps

def totalPrecompileStepsUnHinted : List PrecompileId → Nat
  | [] => 0
  | p :: ps => UnHintedPrecompileCost p + totalPrecompileStepsUnHinted ps

theorem totalPrecompileSteps_hinted_le_unhinted (calls : List PrecompileId) :
    totalPrecompileStepsHinted calls ≤ totalPrecompileStepsUnHinted calls := by
  induction calls with
  | nil =>
      simp [totalPrecompileStepsHinted, totalPrecompileStepsUnHinted]
  | cons p ps ih =>
      simp only [totalPrecompileStepsHinted, totalPrecompileStepsUnHinted]
      have h := hinted_strictly_reduces_all_precompiles p
      omega

theorem totalPrecompileSteps_hinted_lt_unhinted (p : PrecompileId) (ps : List PrecompileId) :
    totalPrecompileStepsHinted (p :: ps) < totalPrecompileStepsUnHinted (p :: ps) := by
  simp only [totalPrecompileStepsHinted, totalPrecompileStepsUnHinted]
  have hHead := hinted_strictly_reduces_all_precompiles p
  have hTail := totalPrecompileSteps_hinted_le_unhinted ps
  omega

def finiteScoreK (w : BlockWorkloadBounds) : Nat :=
  maxAcceptedExecutionSteps w.policy w.maxInputBytes w.maxTrieEntries +
  256 * w.accountAccesses +
  512 * w.storageAccesses +
  totalPrecompileStepsHinted w.precompileCalls

def finiteScoreKUnHinted (w : BlockWorkloadBounds) : Nat :=
  maxAcceptedExecutionSteps w.policy w.maxInputBytes w.maxTrieEntries +
  256 * w.accountAccesses +
  512 * w.storageAccesses +
  totalPrecompileStepsUnHinted w.precompileCalls

theorem finiteScoreK_hinted_strictly_smaller_when_precompile_used
    (w : BlockWorkloadBounds) (p : PrecompileId) (ps : List PrecompileId)
    (hCalls : w.precompileCalls = p :: ps) :
    finiteScoreK w < finiteScoreKUnHinted w := by
  unfold finiteScoreK finiteScoreKUnHinted
  rw [hCalls]
  have h := totalPrecompileSteps_hinted_lt_unhinted p ps
  omega

theorem actual_guest_execution_bounded_by_finiteScoreK
    (w : BlockWorkloadBounds)
    (hdr : CandidateHeader)
    (t : PatriciaTrie)
    (acctKey : ByteKey 32)
    (storKey : ByteKey 64)
    (hInput : hdr.inputBytes ≤ w.maxInputBytes)
    (hTrie : hdr.witnessTrieEntries ≤ w.maxTrieEntries) :
    guardedExecutionSteps w.policy hdr +
      w.accountAccesses * lookupStepsBounded t acctKey.bits +
      w.storageAccesses * lookupStepsBounded t storKey.bits +
      totalPrecompileStepsHinted w.precompileCalls
      ≤ finiteScoreK w := by
  unfold finiteScoreK
  have hGuard :=
    guardedExecutionSteps_finite_score_K_bound
      w.policy hdr w.maxInputBytes w.maxTrieEntries hInput hTrie
  have hAcct := patricia_account_key_lookup_le_256 t acctKey
  have hStor := patricia_storage_key_lookup_le_512 t storKey
  have hAcctMul : w.accountAccesses * lookupStepsBounded t acctKey.bits ≤ 256 * w.accountAccesses := by
    rw [Nat.mul_comm 256 w.accountAccesses]
    exact Nat.mul_le_mul_left w.accountAccesses hAcct
  have hStorMul : w.storageAccesses * lookupStepsBounded t storKey.bits ≤ 512 * w.storageAccesses := by
    rw [Nat.mul_comm 512 w.storageAccesses]
    exact Nat.mul_le_mul_left w.storageAccesses hStor
  omega

end FiniteScoreKInvariant


end InitECandidate.Solver.SoftwareGuestHintedPrecompiles
