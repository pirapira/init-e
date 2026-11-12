import InitECandidate.Solver.GuestBound.Heap
import InitECandidate.Solver.GuestBound.Keepers

/-!
# Functions that never write memory

`memKeeper` relates states with the same memory; its leaves are the
statements that change only locals, plus assignments to globals. `keepFn`
then decides, following calls, that a function performs no store at all, and
`noStore_sound` turns the check into "memory after any run of the body is the
memory before". 204 of the 813 guest functions have this property (readers
such as `htab_get` and `rlp_item_header`, arithmetic). The allocators are not
among them, because `trap_with` writes its diagnostics through the shared
memory before trapping; their memory facts are `alloc_runs` and `ScratchPost`.
The instances below are ones the witness-decoding loop needs (issue #21).
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- Leaves that write no memory. -/
def memLeaf : Prog Word → Bool
  | .assign .global _ _ => true
  | p => quietLeaf p

/-- Memory is unchanged. -/
def memKeeper (E : Env σ) : Keeper E where
  rel s s' := s'.memory = s.memory
  refl _ := rfl
  trans h₁ h₂ := h₂.trans h₁
  right_locals _ h := h
  left_locals _ h := h
  allow := memLeaf
  leaf := by
    intro fuel p s r n hallow hrun
    by_cases hq : quietLeaf p = true
    · exact ((quietKeeper E).leaf fuel p s r n hq hrun).2.1
    · cases p with
      | assign kind name value =>
        cases kind with
        | «local» => exact absurd rfl hq
        | global =>
          have hr := runs_assign_global.mp (Runs.of_run hrun)
          subst hr
          split
          · split <;> rfl
          · rfl
      | _ => exact absurd hallow hq

/-- A function accepted by the check never changes memory. -/
theorem noStore_sound (hE : GuestEnv E) (depth : Nat) (f : FunName)
    (h : keepFn memLeaf Guest.Software.guestAst depth f = true) : FunKeeps (memKeeper E) f :=
  keepFn_sound (memKeeper E) hE.functions depth f h

theorem nodedb_lookup_mem (hE : GuestEnv E) : FunKeeps (memKeeper E) "nodedb_lookup" :=
  noStore_sound hE 3 "nodedb_lookup" (by decide +kernel)

theorem htab_get_mem (hE : GuestEnv E) : FunKeeps (memKeeper E) "htab_get" :=
  noStore_sound hE 2 "htab_get" (by decide +kernel)

theorem mpt_fail_mem (hE : GuestEnv E) : FunKeeps (memKeeper E) "mpt_fail" :=
  noStore_sound hE 1 "mpt_fail" (by decide +kernel)

theorem rlp_read_length_mem (hE : GuestEnv E) : FunKeeps (memKeeper E) "rlp_read_length" :=
  noStore_sound hE 2 "rlp_read_length" (by decide +kernel)

theorem rlp_item_header_mem (hE : GuestEnv E) : FunKeeps (memKeeper E) "rlp_item_header" :=
  noStore_sound hE 3 "rlp_item_header" (by decide +kernel)

theorem rlp_item_total_unchecked_mem (hE : GuestEnv E) : FunKeeps (memKeeper E) "rlp_item_total_unchecked" :=
  noStore_sound hE 3 "rlp_item_total_unchecked" (by decide +kernel)

theorem rlp_fail_mem (hE : GuestEnv E) : FunKeeps (memKeeper E) "rlp_fail" :=
  noStore_sound hE 1 "rlp_fail" (by decide +kernel)

theorem htab_find_leaf_mem (hE : GuestEnv E) : FunKeeps (memKeeper E) "htab_find_leaf" :=
  noStore_sound hE 1 "htab_find_leaf" (by decide +kernel)

theorem memeq_mem (hE : GuestEnv E) : FunKeeps (memKeeper E) "memeq" :=
  noStore_sound hE 1 "memeq" (by decide +kernel)

end InitECandidate.Solver.GuestBound
