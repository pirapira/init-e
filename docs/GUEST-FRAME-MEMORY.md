# Guest interpreter: where the per-frame data lives

Read-through of `guest/src` at the commit this file was added in, produced by
a code-reading agent for issues #9 and #20. **Not machine-checked.** Use it
to plan the interpreter invariant; re-read the cited lines before relying on
any row in a proof.

Points that matter most for the invariant:

- Every per-frame object (frame record, continuation, child message, operand
  stack, jumpdest bitmap, log list, delete table) is in the **scratch arena**;
  EVM byte memory is in the **frame-memory arena**; only return data, the MCO
  record and top-level messages are on the heap.
- `scratch_ptr` and `frame_mem_ptr` are released to marks loaded from frame
  records (`CK_MARK`, `CK_MEM_MARK`, `EV_STACK_MARK`, `EV_MEM_MARK`,
  `MCO_*_MARK`), so "the arena pointers are in range" depends on those
  records being intact. `heap_ptr` is only ever released to local marks.
- `extend_memory` grows EVM memory in place and relies, without checking, on
  `frame_mem_ptr == EV_MEM + EV_MEM_CAP` for the current frame.

All paths below are under /home/yoichi-bkp/guest-bound/init-e/guest/src. Allocators are in lib/mem.pnk: `alloc` at :37, `frame_mem_alloc` at :61 (traps code 6 if it would pass `scratch_ptr`), `scratch_alloc` at :88 (moves down, traps code 7 if it would go below `frame_mem_ptr`). The mark/release pairs are at :49/:53, :74/:78 and :98/:102. Each release just assigns the global back. Outside mem.pnk nothing writes `heap_ptr`, `scratch_ptr` or `frame_mem_ptr` directly (grep `\b(heap_ptr|scratch_ptr|frame_mem_ptr)\b` excluding lib/mem.pnk returned nothing).

## 1. Allocation of per-frame objects
| Object | Allocating function (file:line) | Allocator | Size |
|---|---|---|---|
| Frame record `ev` | `frame_new` evm.pnk:518 `var 1 e = scratch_alloc(EV_SIZE);` (EV_SIZE=280, evm.pnk:117), zeroed at :519 | scratch_alloc | EV_SIZE |
| Continuation `cur_cont` | `frame_open` evm_calls.pnk:523 `var 1 rec = scratch_alloc(CK_SIZE);` (CK_SIZE=104, :517), zeroed at :524 | scratch_alloc | CK_SIZE |
| Message, child frames | `child_message` evm_calls.pnk:922 calls `msg_new_scratch` evm.pnk:509 `scratch_alloc(MSG_SIZE)` (MSG_SIZE=176, :81) | scratch_alloc | MSG_SIZE |
| Message, top level / system tx | `msg_new` evm.pnk:503 `alloc(MSG_SIZE)`, called at fork.pnk:297 (`process_unchecked_system_transaction`) and fork.pnk:581 (`process_transaction`) | alloc | MSG_SIZE |
| Operand stack, initial | `frame_new` evm.pnk:520 `scratch_alloc(STACK_INIT_CAP * 32)` (STACK_INIT_CAP=32, :156); EV_STACK_CAP set to 32 at :523 | scratch_alloc | 1024 bytes |
| Operand stack, growth | `stack_push` evm.pnk:316 `scratch_alloc(ncap * 32)` with ncap = min(2*cap, 1024), then memcpy of `sp*32` bytes (:317). The old stack is not freed | scratch_alloc | ncap*32 |
| EVM memory, initial | `frame_new` evm.pnk:524 `frame_mem_alloc(1024)`; EV_MEM_CAP=1024 at :527. EV_MEM_LEN is never set here, so it stays 0 from the memzero | frame_mem_alloc | 1024 |
| EVM memory, growth | `extend_memory` evm.pnk:412 `frame_mem_alloc(ncap - cap);` (return value ignored; see section 5) | frame_mem_alloc | ncap-cap |
| Return-data buffer | Initially `evm_empty` (evm.pnk:550; EV_RETDATA_CAP=0 at :551). `set_retdata` evm_calls.pnk:959 `dst = alloc(n + 8);` only when `cap <+ n`, otherwise it reuses the buffer. `evm_empty` is `alloc(8)` in `evm_init` (evm_calls.pnk:63) | alloc | n+8 |
| Output buffer | No dedicated allocation in the interpreter. `op_return` evm_calls.pnk:107 and `op_revert` :122 set `st ev + EV_OUTPUT, MEM_PTR(s);`, a pointer into the frame's EVM memory. Otherwise it is `evm_empty` (evm.pnk:549, evm_calls.pnk:540, :627, :868), `msg+MSG_DATA` (precompiles.pnk:46), or a precompile result (`st ev + EV_OUTPUT, ...` in precompiles*.pnk; I did not check which allocator each precompile uses) | n/a | n/a |
| MCO record | `process_message_call` evm_calls.pnk:1397 `var 1 out = alloc(MCO_SIZE);` (MCO_SIZE=96, :35), zeroed at :1398 | alloc | MCO_SIZE |

Other per-frame scratch allocated in `frame_new`:
- Jumpdest bitmap: `compute_jumpdests` evm.pnk:451, `scratch_alloc(((n+63)>>>6)*8+8)`.
- EV_LOGS: `lst_new_scratch(8,4)` (evm.pnk:534, defined at bal.pnk:45).
- EV_DELETE: `htab_new_scratch(20,4)` (evm.pnk:538, defined at lib/htab.pnk:66, which uses scratch_alloc).

Allocation order inside one child's scratch region is: generic_call/generic_create take `child_mark`, then the msg, then (inside frame_new, which takes its own marks first) EV, stack, jumpdests, logs and delete table, then the CK record. So for kind 1 and 2 children, `CK_MARK` (taken before the msg) sits at or above `EV_STACK_MARK`.

## 2. Mark fields and releases
Searches run over all of guest/src: grep `_MARK|heap_release|scratch_release|frame_mem_release|_mark\(\)|heap_mark|scratch_mark|frame_mem_mark`. In evm.pnk, evm_calls.pnk, fork.pnk and state.pnk the only fields that hold allocator marks are EV_STACK_MARK, EV_MEM_MARK, CK_MARK, CK_MEM_MARK, MCO_SCRATCH_MARK and MCO_MEM_MARK.

**Writes to mark fields (exhaustive):**
- evm.pnk:521 `st e + EV_STACK_MARK, stack_mark;`, where `stack_mark = scratch_mark()` at :516 (taken before the EV allocation).
- evm.pnk:525 `st e + EV_MEM_MARK, mem_mark;`, where `mem_mark = frame_mem_mark()` at :517.
- evm_calls.pnk:751 `st cur_cont + CK_MARK, child_mark;` and :752 `st cur_cont + CK_MEM_MARK, child_mem_mark;` in `start_child`. These are parameters supplied by:
  - `generic_create`: :1047 `scratch_mark()` and :1048 `frame_mem_mark()`, passed at :1053.
  - `generic_call`: :1127 and :1128, passed at :1133.
  - In both, the marks are taken before `child_message` / `msg_new_scratch`.
- evm_calls.pnk:1430 `st out + MCO_SCRATCH_MARK, lds 1 (frame + EV_STACK_MARK);`
- evm_calls.pnk:1431 `st out + MCO_MEM_MARK, lds 1 (frame + EV_MEM_MARK);`
- Implicit zero writes:
  - For kind-0 frames (`process_message`), CK_MARK and CK_MEM_MARK stay 0 from the memzero at :524.
  - The MCO marks stay 0 on the address-collision early return at :1407, because of the memzero at :1398.

**scratch_release / frame_mem_release in these four files (exhaustive):**
| Site | Function | Value released |
|---|---|---|
| evm_calls.pnk:674 | finish_child | `child_mark`, loaded at :613 from `rec + CK_MARK` (`rec` = `cur_cont` captured at :607) |
| evm_calls.pnk:675 | finish_child | `child_mem_mark`, loaded at :614 from `rec + CK_MEM_MARK` |
| evm_calls.pnk:806 | process_message (catch path, `perr == E_REVERT`) | `lds 1 (child + EV_STACK_MARK)` |
| evm_calls.pnk:807 | same | `lds 1 (child + EV_MEM_MARK)` |
| fork.pnk:328 | process_unchecked_system_transaction | `system_mark`, loaded at :318 from `out + MCO_SCRATCH_MARK`; guarded by `if system_mark != 0` |
| fork.pnk:329 | same | `lds 1 (out + MCO_MEM_MARK)` |
| fork.pnk:718 | process_transaction | `tx_frame_mark`, loaded at :716 from `out + MCO_SCRATCH_MARK`; guarded by `!= 0` |
| fork.pnk:719 | same | `lds 1 (out + MCO_MEM_MARK)` |

state.pnk has no scratch or frame_mem releases.

**heap_release in these four files:** every one releases a local `mark = heap_mark()` taken in the same function. None load a mark from memory.
- evm.pnk: :875/:880 (op_keccak), :994/:998 (op_mcopy), :1019/:1023, :1349/:1353.
- evm_calls.pnk: :42/:51 (evm_init), :197/:216,:220, :972/:985 (compute_contract_address), :991/:1000 (compute_create2_contract_address).
- fork.pnk: :109/:111 (block_rlp_length).
- state.pnk: :233/:237 (ws_account_leaf), :281/:285 (ws_get_storage).

**Elsewhere:** `scratch_release` also appears in lib/rlp.pnk:211,214 and mpt.pnk:505,519,522,938,941,1109. All use local `scratch_mark()` locals except mpt.pnk:505, which I did not inspect for its mark's origin.

## 3. Assignments to `ev` and `cur_cont`
I used grep `(^|[^a-zA-Z0-9_.])(ev|cur_cont)[[:space:]]*=[^=]` and also `\b(ev|cur_cont)\b\s*=` excluding `==`, over all of guest/src. A shadowing check (locals or parameters named `ev` or `cur_cont`) found none.

| File:line | Function | Assignment |
|---|---|---|
| evm.pnk:166 | global | `var 1 ev = 0;` |
| evm_calls.pnk:21 | global | `var 1 cur_cont = 0;` |
| evm_calls.pnk:529-530 | frame_open | `ev = child;` and `cur_cont = rec;` |
| evm_calls.pnk:634-635 | finish_child | `ev = parent;` (from `rec + CK_PARENT`, :609) and `cur_cont = lds 1 (rec + CK_PARENT_CONT);` |
| evm_calls.pnk:709-710 | run_frames (kind 0 done) | `ev = lds 1 (cur_cont + CK_PARENT);` and `cur_cont = lds 1 (cur_cont + CK_PARENT_CONT);` |
| evm_calls.pnk:808-809 | process_message (catch path, REVERT) | `ev = parent;` and `cur_cont = parent_cont;` (locals saved at :795-796) |
| evm_calls.pnk:817-818 | process_message (catch path, other errors) | same as above |
| evm_calls.pnk:861 | process_create_message | `ev = child;` (`cur_cont` is not changed) |
| evm_calls.pnk:871 | process_create_message | `ev = parent;` (restores `ev` saved at :860) |

## 4. Operand stack discipline
**Helpers:**
- `stack_pop` evm.pnk:295 checks only `sp == 0`, throwing E_STACK_UNDERFLOW. It then decrements sp, stores `EV_SP`, and returns `lds {1,1,1,1} ((lds 1 (ev + EV_STACK)) + sp * 32)`.
- `stack_push` evm.pnk:305 checks, in order:
  1. If `sp >=+ cap` (cap from EV_STACK_CAP): if `cap >=+ STACK_DEPTH_LIMIT` (1024) it throws E_STACK_OVERFLOW; otherwise it grows the stack (`ncap = min(cap*2, 1024)`, scratch_alloc, memcpy, update EV_STACK and EV_STACK_CAP, :312-319).
  2. Then `if sp == STACK_DEPTH_LIMIT` it throws E_STACK_OVERFLOW (:321).
  3. Then it stores `st (lds 1 (ev + EV_STACK)) + sp * 32, v;` (:324) and `EV_SP = sp + 1` (:325).
- Wrappers that only call `stack_push`: `stack_push_word` :329 and `stack_push_bool` :334.

**Direct stack accesses that bypass the helpers:**
- `op_dup` :1030 reads `EV_STACK + (sp-1-item)*32` after checking `item >=+ sp`.
- `stack_swap_positions` :1042 reads and writes slots `(sp-1-i)` and `(sp-1-j)` and does no checks itself. Its callers check first:
  - `op_swap` :1057: `item >=+ sp`.
  - `op_swapn` :1100: `n + 1 >+ sp`.
  - `op_exchange` :1127: `mx + 1 >+ sp`.
- `op_dupn` :1086 checks `n >+ sp`.
- `op_log` :1146 checks `sp <+ ntopics`.

**Writes to EV_SP:** only evm.pnk:301 and :325. `frame_new` leaves it 0 via the memzero.

## 5. EVM memory expansion
- **`extend_memory(expand_by)`, evm.pnk:400.**
  - If `nlen = len + expand_by >+ cap`, then `ncap = cap*2`, or `nlen + 1024` if that is still smaller.
  - It calls `frame_mem_alloc(ncap - cap)` and ignores the return value. It then zeroes `EV_MEM + cap .. ncap` (:413) and sets EV_MEM_CAP (:414).
  - EV_MEM is never changed and old contents are not copied. Growth is in place, which implicitly assumes `frame_mem_ptr == EV_MEM + cap` at that point. The code does not check this; the only justification is the comment at lib/mem.pnk:58-60. Writes to EV_MEM: only evm.pnk:526.
  - It always zeroes `EV_MEM + len` for `expand_by` bytes (:416) and sets EV_MEM_LEN (:417).
- **Cost helpers:**
  - `extend_memory_cost1` :357 returns `<cost, after-before>` with `after`/`before` being ceil32 values. It saturates to WORD_MAX when `endp == WORD_MAX` (:365) or when the cost is WORD_MAX (:376). In those cases expand_by is 0, but `charge_gas` then fails because the cost is WORD_MAX.
  - `extend_memory_cost2` :383 temporarily writes EV_MEM_LEN (:390) and restores it (:392).
- **`charge_with_memory`** :422 runs cost1, then `charge_gas(add_sat(base, cost))`, then `extend_memory`.
- **Pointer macro:** `MEM_PTR(off) ((lds 1 (ev + EV_MEM)) + (off))` at evm.pnk:446. It has no bounds check; it relies on the gas charge plus extension done beforehand.
- **Opcode write paths:**
  - MSTORE (:944) and MSTORE8 (:954) use `charge_with_memory(3, start, <32|1,...>)`, then `sat_word`, then write via MEM_PTR (:949 / :959).
  - CALLDATACOPY (:1386) and CODECOPY (:1399) use `copy_from_buffer` (:1367): cost1, `charge_gas`, `extend_memory`, then `buffer_read(..., MEM_PTR(ms))` if n != 0.
  - EXTCODECOPY (:1431) follows the same pattern, writing at :1449.
  - RETURNDATACOPY (:1462): cost1, `charge_gas`, a bounds check `endp >+ EV_RETDATA_N` (E_OUT_OF_BOUNDS_READ), `extend_memory`, then memcpy (:1479).
  - MCOPY (:981): cost2, `charge_gas`, `extend_memory`, then copy through a temporary heap buffer.
  - `finish_child` :671 memcpys into `MEM_PTR(out_start)`. The parent's extension for that range was done in `op_call`/`op_callcode`/`op_delegatecall`/`op_staticcall` via cost2 plus `extend_memory` before the child was started.

## 6. Per-function summary (all in evm_calls.pnk unless noted)
- **`frame_open`** (:520)
  - Writes: CK_PARENT (old `ev`), CK_PARENT_CONT (old `cur_cont`), CK_KIND and CK_MSG on the new record. Sets globals `ev` and `cur_cont`.
  - Calls: `frame_new`, `scratch_alloc`, `memzero`.
- **`frame_new`** (evm.pnk:515)
  - Writes: EV_STACK_MARK, EV_STACK, EV_STACK_CAP, EV_MEM_MARK, EV_MEM, EV_MEM_CAP, EV_CODE, EV_CODE_N, EV_GAS_LEFT (=MSG_GAS), EV_STATE_GAS_LEFT (=MSG_RESERVOIR), EV_JUMPDESTS, EV_LOGS, EV_RUNNING=1, EV_MSG, EV_DELETE, EV_ACC_ADDRS, EV_ACC_KEYS, EV_ACC_ADDRS_N, EV_ACC_KEYS_N, EV_OUTPUT, EV_RETDATA and EV_RETDATA_CAP=0. Everything else stays 0 from the memzero.
  - Calls: `scratch_mark`, `frame_mem_mark`, `scratch_alloc`, `frame_mem_alloc`, `memzero`, `compute_jumpdests`, `lst_new_scratch`, `htab_new_scratch`, `htab_count`.
- **`frame_start`** (:581)
  - Writes: CK_DONE=1 on `cur_cont` if the prologue returned 1.
  - Calls: `frame_prologue` under try/catch EvmErr, which calls `frame_exception`.
- **`frame_prologue`** (:552)
  - Writes: no EV/CK fields directly.
  - Calls: `move_ether`, `memeq`, `emit_transfer_log` (when value transfer is set and nonzero), `precompile_index`, `run_precompile` (precompiles write EV_OUTPUT and EV_OUTPUT_N on `ev`).
  - Returns 1 for a precompile target.
- **`frame_exception`** (:536)
  - Calls `refill_frame_state_gas` (writes EV_GAS_LEFT, EV_STATE_GAS_LEFT, EV_STATE_GAS_SPILLED).
  - If err != E_REVERT: calls `frame_halt` (writes EV_REGULAR_GAS_USED, EV_GAS_LEFT=0, EV_ERROR), then sets EV_OUTPUT=evm_empty and EV_OUTPUT_N=0.
  - Otherwise: sets EV_ERROR=err.
  - Always sets CK_DONE=1 on `cur_cont`.
- **`frame_epilogue`** (:595)
  - Writes: no fields.
  - Calls `state_restore(CK_SNAPSHOT)` if EV_ERROR != 0.
- **`finish_child`** (:606)
  - Reads CK_PARENT, CK_KIND, CK_MSG, CK_NEW_ACCOUNT, CK_MARK, CK_MEM_MARK, CK_OUT_START, CK_OUT_SIZE, CK_CONTRACT and CK_CSNAPSHOT.
  - Kind 2, while still on the child: calls `create_finish` (which calls `charge_gas`/`charge_state_gas` on the child, `alloc`, `set_code`). On error it calls `state_restore`, `refill_frame_state_gas`, `frame_halt`, and sets the child's EV_OUTPUT and EV_OUTPUT_N.
  - Then it switches `ev` and `cur_cont` to the parent. On the parent, error or success:
    - `rollback_child_access`
    - `incorporate_child_on_error` (writes EV_GAS_LEFT, EV_STATE_GAS_LEFT, EV_REGULAR_GAS_USED)
    - or `incorporate_child_on_success` (additionally writes EV_STATE_GAS_SPILLED, EV_REFUND and EV_LOGS via `log_append`, EV_DELETE via `htab_union_into`)
    - `credit_state_gas_refund`
    - `set_retdata` (writes EV_RETDATA, EV_RETDATA_N, EV_RETDATA_CAP; may `alloc`)
    - `stack_push`
  - Kind 1 also memcpys into parent memory.
  - Finally it calls `scratch_release`, `frame_mem_release`, and `pc_add(1)` (writes EV_PC).
- **`start_child`** (:729)
  - Kind 2 first: `state_snapshot`, `destroy_storage`, `mark_account_created`, `increment_nonce`.
  - Depth check: throws E_STACK_DEPTH_LIMIT if MSG_DEPTH > 1024.
  - Calls `frame_open(cm, kind)`, then `state_snapshot`.
  - Writes on the new `cur_cont`: CK_SNAPSHOT, CK_CSNAPSHOT, CK_MARK, CK_MEM_MARK, CK_NEW_ACCOUNT, CK_OUT_START, CK_OUT_SIZE and CK_CONTRACT.
  - Then calls `frame_start`.

Not verified: whether frame_mem_ptr really equals EV_MEM+EV_MEM_CAP for `ev` whenever `extend_memory` runs. My reasoning, not checked against every path, is this:
- A child's `child_mem_mark` is taken after the parent's `extend_memory` in the call and create ops.
- `frame_new` then takes the same value as EV_MEM_MARK, since no frame_mem_alloc happens in between.
- Every frame_mem_alloc call in these files is a multiple of 8 (1024, or ncap-cap where ncap is 2*cap or nlen+1024, nlen ≡ 0 mod 32), so the alloc's 8-byte rounding does not shift the frame_mem_ptr == EV_MEM+EV_MEM_CAP invariant.

No frame_mem_alloc calls were found outside evm.pnk:412,524.
