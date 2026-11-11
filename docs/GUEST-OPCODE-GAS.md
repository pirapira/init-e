# Guest opcode gas table (for the `run_frames` iteration bound)

> Status: a read-through by an automated agent on 2026-11-11, not machine-checked. The SSTORE
> refund path and the `charge_state_gas` / `credit_state_gas_refund` / `incorporate_child_*`
> bodies were re-read by hand; the per-opcode rows were not. See pirapira/init-e#9.

Source read: `guest/src/evm.pnk`, `guest/src/evm_calls.pnk`, `guest/src/precompiles.pnk`
(plus greps of `state.pnk`, `fork.pnk`, `precompiles_*.pnk`, `lib/`). Paths below are
relative to `guest/src/`. "(inferred)" marks a conclusion that is reasoned, not read
off a single line.

Terminology: iteration kind (a) = `op_dispatch` on the current frame
(evm_calls.pnk:698); kind (b) = `frame_epilogue` + exit / `finish_child`
(evm_calls.pnk:705-718). `gl` = `EV_GAS_LEFT`, `sgl` = `EV_STATE_GAS_LEFT`,
`spilled` = `EV_STATE_GAS_SPILLED`.

## Summary

### (i) Does every frame-continuing normal return charge >= 1 gas?

**Charge: yes. Net decrease of the gas fields: no.**

- Every handler path that returns normally, leaves `EV_RUNNING != 0` and pushes no
  frame calls `charge_gas(n)` with `n >= 1`. The minimum is JUMPDEST, `charge_gas(1)`
  (evm.pnk:937). There is no early `return` before the charge in any handler. The only
  handlers that can charge 0 are STOP (no charge, evm.pnk:888-892) and RETURN
  (`charge_gas(x.0)` with `x.0 == 0` possible, evm_calls.pnk:99-100); both set
  `EV_RUNNING = 0`, so they are not frame-continuing.
- **Counterexample to "gas of live frames decreases by >= 1 per continuing iteration":
  SSTORE.** On the path `current != new`, `original == new`, `original == 0`
  (evm.pnk:1263-1265) it calls `credit_state_gas_refund(SG_STORAGE_SET)` (97920,
  evm.pnk:158). On that path `oc == 0`, so the regular charge is only `access_cost`
  (100 warm, evm.pnk:1232, 1244-1247, 1266). Net effect of the iteration:
  `gl + sgl` changes by **+97920 - 100 = +97820**; `gl` alone rises by
  `min(97920, spilled) - 100`, the rest goes to `sgl` (evm.pnk:270-277). This fails
  for the measure "regular gas only" (when `spilled > 0`) and for "regular + state".
- No other frame-continuing handler path has a net increase (inferred from the
  per-site analysis in section 3): the CALL-family "no frame" paths give back exactly
  what the same handler subtracted, plus the 2300 stipend, which is covered by the
  11300 `G_CALL_VALUE` charged in the same handler.

### (ii) Every place `gl` / `sgl` can increase

| # | Site | What | Bound |
|---|------|------|-------|
| 1 | evm.pnk:273, 275 `credit_state_gas_refund` | `gl += min(amount, spilled)`, `sgl += amount - that` | exactly `amount` in total. Callers: SSTORE evm.pnk:1264 (97920); CALL insufficient balance evm_calls.pnk:1221; `generic_call` depth limit :1119; `generic_create` collision :1039; `finish_child` on child error :642, :657 (all 183600 = `SG_NEW_ACCOUNT`, each guarded by `new_account_charged`, i.e. a `charge_state_gas(SG_NEW_ACCOUNT)` at :1029 or :1201 earlier for the same call) |
| 2 | evm.pnk:287-288 `refill_frame_state_gas` | `gl += spilled`; `sgl := MSG_RESERVOIR` | `spilled + (MSG_RESERVOIR - sgl)` = `frame_state_gas_used` (evm.pnk:280-283). Called only when the frame is ending: `frame_exception` evm_calls.pnk:537, `finish_child` create failure :625 (and outside the loop :815, :866) |
| 3 | evm_calls.pnk:880-881 `incorporate_child_on_error` (also called by `_on_success`, :887) | parent `gl += child.gl`, parent `sgl += child.sgl` | child's fields; the child is popped in the same `finish_child`, so the sum over live frames is unchanged |
| 4 | evm_calls.pnk:894 `incorporate_child_on_success` | `gl += rep`, `sgl -= rep`, `rep = min(sgl, spilled)` (:890-896) | transfer state -> regular; `gl + sgl` unchanged; regular-only measure rises by `rep` |
| 5 | evm_calls.pnk:1116-1117 `generic_call` depth-limit path | `gl += gas` (= `mcg.1` = g + stipend), `sgl += reservoir` | g was charged at :1206/:1273/:1330/:1376; reservoir was zeroed at :1210/:1277/:1334/:1380; stipend 2300 is extra (see 7) |
| 6 | evm_calls.pnk:1218-1219 (CALL), :1285-1286 (CALLCODE) insufficient-balance path | `gl += mcg.1`, `sgl += reservoir` | same as 5 |
| 7 | Stipend: evm_calls.pnk:1140-1143, 1156 | child gets / parent is handed back `g + 2300` while `charge_gas(mcg.0)` took only `g` | stipend is nonzero only when value != 0 (:1141); the same condition adds `G_CALL_VALUE` = 11300 to the charge at :1181-1185 (CALL) / :1256-1260 (CALLCODE). DELEGATECALL / STATICCALL pass value 0 (:1329, :1375), so no stipend |
| 8 | evm.pnk:530-531 `frame_new` | child `gl := MSG_GAS`, `sgl := MSG_RESERVOIR` | CALL family: `MSG_GAS = mcg.1` (:1129, :1228), reservoir = parent's whole `sgl`, zeroed in the parent first. CREATE: `MSG_GAS = create_gas`, subtracted from the parent by a direct store at evm_calls.pnk:1032-1033; reservoir zeroed at :1044-1045 |

No handler other than those above writes `EV_GAS_LEFT` / `EV_STATE_GAS_LEFT`
(grep over `guest/src`; precompile files only call `charge_gas`).

### (iii) Open questions

1. **Is every SSTORE credit (evm.pnk:1264) preceded by a matching
   `charge_state_gas(SG_STORAGE_SET)` (evm.pnk:1260-1267) in the same transaction?**
   The credit needs `original == 0 && current != 0`. I believe a 0 -> nonzero write
   under `original == current == 0` (which charges) is the only way to reach that
   state (inferred), but `get_storage_original` returns 0 for any account in
   `TS_CREATED` (state.pnk:411-415) and otherwise reads block-level writes / the
   witness (state.pnk:416-422); I did not trace `set_storage`, `destroy_storage`
   (state.pnk:540), `mark_account_created` (state.pnk:587) and `account_has_storage`
   (state.pnk:462-475) far enough to prove a created account can never carry a
   nonzero slot that was not charged. If the pairing holds, a potential such as
   `sum(gl + sgl) + 97920 * #(slots with original == 0, current != 0)` would repair
   the measure for SSTORE (inferred, not checked against reverts).
2. **Refill at frame end** (item 2) raises `gl + sgl` of the ending frame by
   `frame_state_gas_used`, which then flows to the parent (item 3). I believe this
   never returns more than the frame was given (it undoes state-gas charges of the
   frame and its successful descendants) (inferred); not proved. `frame_state_gas_used`
   is documented as signed (evm.pnk:279).
3. `finish_child` is wrapped in `try ... catch EvmErr` (evm_calls.pnk:714-717). I found
   no reachable `EvmErr` throw inside it outside the inner `try` at :622: `state_restore`
   has no throw (state.pnk:181-193), `lib/` contains no `EvmErr` (grep), and the
   `stack_push` at :645/:650/:660/:664 follows >= 3 pops by the parent's handler, so
   `sp < 1024` (inferred). If one did fire before :634 the same child would get a
   second kind-(b) iteration (see section 3).
4. Non-`EvmErr` exceptions (`StateErr` from `move_ether` state.pnk:609, `BlockErr 50`
   from BLOCKHASH evm.pnk:1562, `BlockErr 99` precompiles.pnk:248, `TrapErr`) are not
   caught by `run_frames`; they leave the loop. I did not trace where they land.
5. `htab_*`, `alloc`, `keccak256`, `u256_*`, `get_account`, `get_code`, `get_storage`,
   `set_storage` were not read; I only checked (grep) that none of `lib/`, `state.pnk`,
   `mpt.pnk`, `bal.pnk`, `tx.pnk` throws `EvmErr` or writes a gas field.

## 1. `op_dispatch` coverage

`op_dispatch` (evm_calls.pnk:384-490) never returns normally without calling a
handler: every `return 0` is preceded by a handler call, and each range ends in
`throw EvmErr E_INVALID_OPCODE` (:416 for 0x0c-0x0f, 0x1f; :467 for 0x21-0x2f,
0x4c-0x4f; :488 for 0xa5-0xe5, 0xe9-0xef, 0xf6-0xf9, 0xfb, 0xfc, 0xfe). The trailing
`return 0` at :489 is dead. The throw is caught at :699 and ends the frame via
`frame_exception`.

`pc`: every handler either does `pc_add(k)` with `k >= 1`, or sets `pc` to a jump
destination (JUMP evm.pnk:901, JUMPI :918; pc can go backwards, 8 / 10 gas charged
first), or ends the frame (STOP, RETURN, SELFDESTRUCT; RETURN and SELFDESTRUCT do not
advance pc), or throws, or starts a child (then `pc_add(1)` happens in `finish_child`,
evm_calls.pnk:676).

## 2. Table

"Min gas" = minimum `charge_gas` total on a normally-returning, frame-continuing,
no-new-frame path. All such paths also do `pc_add`. Unless noted, the handler has a
single `charge_gas` before any `return`, cannot end the frame except by throwing, and
creates no frame. Memory-expansion and per-word terms are added with `add_sat`
(evm.pnk:181-187), so the total cannot wrap below the base.

| Opcode(s) | Handler | File:line | Min gas (continuing) | Ends frame? | Creates frame? | Notes |
|---|---|---|---|---|---|---|
| 0x00 STOP | `op_stop` | evm.pnk:888 | n/a (never continues) | yes, `EV_RUNNING = 0` (:889), **0 gas** | no | pc+1 |
| 0x01 ADD | `op_add` | evm.pnk:603 | 3 (:606) | no | no | |
| 0x02 MUL | `op_mul` | evm.pnk:613 | 5 (:616) | no | no | |
| 0x03 SUB | `op_sub` | evm.pnk:623 | 3 (:626) | no | no | |
| 0x04 DIV | `op_div` | evm.pnk:633 | 5 (:636) | no | no | |
| 0x05 SDIV | `op_sdiv` | evm.pnk:643 | 5 (:646) | no | no | |
| 0x06 MOD | `op_mod` | evm.pnk:653 | 5 (:656) | no | no | |
| 0x07 SMOD | `op_smod` | evm.pnk:663 | 5 (:666) | no | no | |
| 0x08 ADDMOD | `op_addmod` | evm.pnk:673 | 8 (:677) | no | no | |
| 0x09 MULMOD | `op_mulmod` | evm.pnk:684 | 8 (:688) | no | no | |
| 0x0a EXP | `op_exp` | evm.pnk:695 | 10 (`G_EXP_BASE + 50*nb`, :699) | no | no | |
| 0x0b SIGNEXTEND | `op_signextend` | evm.pnk:706 | 5 (:709) | no | no | |
| 0x10 LT, 0x11 GT, 0x12 SLT, 0x13 SGT, 0x14 EQ | `op_lt` .. `op_eq` | evm.pnk:717, 727, 737, 747, 757 | 3 (:720, 730, 740, 750, 760) | no | no | |
| 0x15 ISZERO | `op_iszero` | evm.pnk:767 | 3 (:769) | no | no | |
| 0x16 AND, 0x17 OR, 0x18 XOR | `op_and`, `op_or`, `op_xor` | evm.pnk:776, 785, 794 | 3 (:779, 788, 797) | no | no | |
| 0x19 NOT | `op_not` | evm.pnk:803 | 3 (:805) | no | no | |
| 0x1a BYTE | `op_byte` | evm.pnk:811 | 3 (:814) | no | no | |
| 0x1b SHL, 0x1c SHR, 0x1d SAR | `op_shl`, `op_shr`, `op_sar` | evm.pnk:822, 833, 844 | 3 (:825, 836, 847) | no | no | |
| 0x1e CLZ | `op_clz` | evm.pnk:855 | 5 (:857) | no | no | |
| 0x20 KECCAK256 | `op_keccak` | evm.pnk:866 | 30 (`30 + 6w + mem`, :872-873) | no | no | |
| 0x30 ADDRESS | `op_address` | evm.pnk:1300 | 2 (:1301) | no | no | |
| 0x31 BALANCE | `op_balance` | evm.pnk:1308 | 100 (warm; 3000 cold; :1311-1312, `access_gas_cost` :585-591) | no | no | |
| 0x32 ORIGIN | `op_origin` | evm.pnk:1320 | 2 (:1321) | no | no | |
| 0x33 CALLER | `op_caller` | evm.pnk:1329 | 2 (:1330) | no | no | |
| 0x34 CALLVALUE | `op_callvalue` | evm.pnk:1337 | 2 (:1338) | no | no | |
| 0x35 CALLDATALOAD | `op_calldataload` | evm.pnk:1344 | 3 (:1346) | no | no | |
| 0x36 CALLDATASIZE | `op_calldatasize` | evm.pnk:1359 | 2 (:1360) | no | no | |
| 0x37 CALLDATACOPY | `op_calldatacopy` -> `copy_from_buffer` | evm.pnk:1386, 1367 | 3 (`3 + 3w + mem`, :1374-1375) | no | no | |
| 0x38 CODESIZE | `op_codesize` | evm.pnk:1392 | 2 (:1393) | no | no | |
| 0x39 CODECOPY | `op_codecopy` -> `copy_from_buffer` | evm.pnk:1399, 1367 | 3 (:1374-1375) | no | no | |
| 0x3a GASPRICE | `op_gasprice` | evm.pnk:1404 | 2 (:1405) | no | no | |
| 0x3b EXTCODESIZE | `op_extcodesize` | evm.pnk:1419 | 200 (`c + 100`, c = 100 warm, :1422-1423) | no | no | |
| 0x3c EXTCODECOPY | `op_extcodecopy` | evm.pnk:1431 | 200 (`acc + 100 + 3w + mem`, :1441-1442) | no | no | |
| 0x3d RETURNDATASIZE | `op_returndatasize` | evm.pnk:1455 | 2 (:1456) | no | no | |
| 0x3e RETURNDATACOPY | `op_returndatacopy` | evm.pnk:1462 | 3 (`3 + 3w + mem`, :1469-1470) | no | no | throws out-of-bounds after the charge (:1473-1475) |
| 0x3f EXTCODEHASH | `op_extcodehash` | evm.pnk:1485 | 100 (warm, :1488-1489) | no | no | |
| 0x40 BLOCKHASH | `op_blockhash` | evm.pnk:1548 | 20 (:1550) | no | no | early `return` at :1557 is after the charge; `throw BlockErr 50` (:1562) is not an `EvmErr` and escapes `run_frames` |
| 0x41 COINBASE | `op_coinbase` | evm.pnk:1571 | 2 (:1572) | no | no | |
| 0x42 TIMESTAMP | `op_timestamp` | evm.pnk:1580 | 2 (:1581) | no | no | |
| 0x43 NUMBER | `op_number` | evm.pnk:1588 | 2 (:1589) | no | no | |
| 0x44 PREVRANDAO | `op_prevrandao` | evm.pnk:1612 | 2 (:1613) | no | no | |
| 0x45 GASLIMIT | `op_gaslimit` | evm.pnk:1596 | 2 (:1597) | no | no | |
| 0x46 CHAINID | `op_chainid` | evm.pnk:1604 | 2 (:1605) | no | no | |
| 0x47 SELFBALANCE | `op_selfbalance` | evm.pnk:1503 | 5 (:1504) | no | no | |
| 0x48 BASEFEE | `op_basefee` | evm.pnk:1515 | 2 (:1516) | no | no | |
| 0x49 BLOBHASH | `op_blobhash` | evm.pnk:1523 | 3 (:1525) | no | no | |
| 0x4a BLOBBASEFEE | `op_blobbasefee` | evm.pnk:1539 | 2 (:1540) | no | no | |
| 0x4b SLOTNUM | `op_slotnum` | evm.pnk:1621 | 2 (:1622) | no | no | |
| 0x50 POP | `op_pop` | evm.pnk:1006 | 2 (:1008) | no | no | |
| 0x51 MLOAD | `op_mload` -> `charge_with_memory` | evm.pnk:964, 422 | 3 (:966, :424-425) | no | no | |
| 0x52 MSTORE | `op_mstore` | evm.pnk:944 | 3 (:947) | no | no | |
| 0x53 MSTORE8 | `op_mstore8` | evm.pnk:954 | 3 (:957) | no | no | |
| 0x54 SLOAD | `op_sload` | evm.pnk:1200 | 100 (warm :1207; 2100 cold :1209) | no | no | |
| 0x55 SSTORE | `op_sstore` | evm.pnk:1218 | 100 charged (:1232; requires `gl >= 2301`, :1230-1231) | no | no | **Net gas can INCREASE**: `credit_state_gas_refund(97920)` at :1264 while only 100 is charged (see summary). Also `charge_gas(gas_cost - access_cost)` :1266 (0 or 10000), `charge_state_gas` :1267 (0 or 97920). `EV_REFUND` changes at :1250-1256 are a counter, not gas |
| 0x56 JUMP | `op_jump` | evm.pnk:894 | 8 (:896) | no | no | sets pc = dest (:901), no `pc_add` |
| 0x57 JUMPI | `op_jumpi` | evm.pnk:905 | 10 (:908) | no | no | early `return` at :912 is after the charge |
| 0x58 PC | `op_pc` | evm.pnk:922 | 2 (:923) | no | no | |
| 0x59 MSIZE | `op_msize` | evm.pnk:974 | 2 (:975) | no | no | |
| 0x5a GAS | `op_gas` | evm.pnk:929 | 2 (:930) | no | no | |
| 0x5b JUMPDEST | `op_jumpdest` | evm.pnk:936 | **1** (:937) | no | no | global minimum |
| 0x5c TLOAD | `op_tload` | evm.pnk:1273 | 100 (:1275) | no | no | |
| 0x5d TSTORE | `op_tstore` | evm.pnk:1285 | 100 (:1289) | no | no | |
| 0x5e MCOPY | `op_mcopy` | evm.pnk:981 | 3 (`3 + 3w + mem`, :988-989) | no | no | |
| 0x5f PUSH0 | `op_push(0)` | evm.pnk:1013 | 2 (:1015) | no | no | dispatch evm_calls.pnk:465 |
| 0x60-0x7f PUSH1-PUSH32 | `op_push(op - 95)` | evm.pnk:1013 | 3 (:1017) | no | no | dispatch evm_calls.pnk:470; pc += 1 + nbytes (:1025) |
| 0x80-0x8f DUP1-DUP16 | `op_dup(op - 128)` | evm.pnk:1030 | 3 (:1031) | no | no | dispatch evm_calls.pnk:471 |
| 0x90-0x9f SWAP1-SWAP16 | `op_swap(op - 143)` | evm.pnk:1055 | 3 (:1056) | no | no | dispatch evm_calls.pnk:472 |
| 0xa0-0xa4 LOG0-LOG4 | `op_log(op - 160)` | evm.pnk:1143 | 375 (`375 + 375*topics + 8*n + mem`, :1152-1158) | no | no | dispatch evm_calls.pnk:475 |
| 0xe6 DUPN | `op_dupn` | evm.pnk:1082 | 3 (:1083) | no | no | pc += 2 |
| 0xe7 SWAPN | `op_swapn` | evm.pnk:1096 | 3 (:1097) | no | no | pc += 2 |
| 0xe8 EXCHANGE | `op_exchange` | evm.pnk:1108 | 3 (:1109) | no | no | pc += 2 |
| 0xf0 CREATE | `op_create` -> `generic_create` | evm_calls.pnk:1057, 1007 | 12000 (`G_CREATE_ACCESS + 2w + mem`, :1065-1066) | no | **yes** (kind 2, :1053) | see 2.1 |
| 0xf1 CALL | `op_call` -> `generic_call` | evm_calls.pnk:1160, 1109 | 100 net (see 2.2) | no | **yes** (kind 1, :1133) | see 2.2 |
| 0xf2 CALLCODE | `op_callcode` -> `generic_call` | evm_calls.pnk:1237, 1109 | 100 net | no | **yes** | see 2.2 |
| 0xf3 RETURN | `op_return` | evm_calls.pnk:96 | n/a (never continues) | yes, `EV_RUNNING = 0` (:109); charge is the memory cost only and **can be 0** (:99-100) | no | pc not advanced |
| 0xf4 DELEGATECALL | `op_delegatecall` -> `generic_call` | evm_calls.pnk:1301, 1109 | 100 net | no | **yes** | see 2.2 |
| 0xf5 CREATE2 | `op_create2` -> `generic_create` | evm_calls.pnk:1080, 1007 | 12000 (`12000 + 6w + 2w + mem`, :1089-1090) | no | **yes** (kind 2) | see 2.1 |
| 0xfa STATICCALL | `op_staticcall` -> `generic_call` | evm_calls.pnk:1347, 1109 | 100 net | no | **yes** | see 2.2 |
| 0xfd REVERT | `op_revert` | evm_calls.pnk:113 | n/a | always `throw EvmErr E_REVERT` (:124) after `charge_gas(mem)` (may be 0, :117); frame ends via `frame_exception` | no | |
| 0xff SELFDESTRUCT | `op_selfdestruct` | evm_calls.pnk:128 | n/a | yes, `EV_RUNNING = 0` (:164); charges >= 5000 (:133-137), plus `charge_gas(aw)` :151, `charge_state_gas` :152 | no | no credit |
| all other bytes (103 values) | none | evm_calls.pnk:416, 467, 488 | n/a | `throw EvmErr E_INVALID_OPCODE` -> `frame_exception` | no | |

### 2.1 CREATE / CREATE2 (`generic_create`, evm_calls.pnk:1007-1055)

Charged first: >= 12000 via `charge_gas` (:1066 / :1090). Then:

- `msize > MAX_INIT_CODE_SIZE`: throw (:1008-1010).
- Insufficient balance, nonce at max, or `depth + 1 > 1024`: push 0, return 0, no frame
  (:1020-1023); caller does `pc_add(1)` (:1074-1076 / :1099-1101). Continuing, net
  charge >= 12000.
- `charge_state_gas(SG_NEW_ACCOUNT)` if the target is not alive (:1027-1030).
- `create_gas = gl - (gl >> 6)` is subtracted from the parent by a **direct store**,
  not `charge_gas` (:1031-1033).
- Collision (`account_deployable == 0`): `create_gas` is burned (added to
  `EV_REGULAR_GAS_USED`, never returned), the `SG_NEW_ACCOUNT` charge is credited back,
  push 0, no frame (:1035-1043). Continuing; net change <= -12000.
- Otherwise the parent's `sgl` is moved to the child as reservoir and zeroed
  (:1044-1045), child message gets `MSG_GAS = create_gas` (:1049), `start_child` kind 2
  (:1053). **Child gas is fully subtracted from the parent before the child starts; no
  gas is added.**

### 2.2 CALL family (evm_calls.pnk:1160-1391, `calculate_message_call_gas` :1138-1157)

Common shape:

1. `charge_gas(access + transfer + mem)`: access = 100 warm / 3000 cold; transfer =
   11300 only for CALL/CALLCODE with value != 0 (:1176-1185, :1250-1260, :1312-1317,
   :1358-1363). Minimum 100.
2. `charge_gas(dl.2)` (100 / 3000) if the target is a delegation (:1191-1193 etc.).
3. CALL only: `charge_state_gas(SG_NEW_ACCOUNT)` when value != 0 and target not alive
   (:1197-1203).
4. `mcg = calculate_message_call_gas(value, gas, gl, 0, 0)`; with `extra_gas =
   memory_cost = 0` the branch at :1145-1149 is unreachable (`gl < 0` unsigned is
   false) (inferred), so `mcg.0 = g`, `mcg.1 = g + stipend`, `g = min(requested,
   gl - gl/64)` (:1150-1156). `charge_gas(mcg.0)` (:1206, :1273, :1330, :1376).
5. Parent `sgl` saved as `reservoir` and zeroed (:1209-1210, :1276-1277, :1333-1334,
   :1379-1380).

No-frame, frame-continuing paths (caller then does `pc_add(1)`):

- Insufficient balance (CALL :1214-1222, CALLCODE :1281-1286): `gl += g + stipend`,
  `sgl += reservoir`, CALL also credits `SG_NEW_ACCOUNT` if it was charged. Requires
  value != 0, so step 1 charged >= 11400; net regular change <= -(11400 - 2300) = -9100.
- Depth limit `depth + 1 > 1024` in `generic_call` (:1115-1123): same give-back. Net
  regular change <= -100 (value 0) or <= -9100 (value != 0).
- The `SG_NEW_ACCOUNT` charge/credit pair inside one handler restores `gl`, `sgl` and
  `spilled` exactly (inferred from evm.pnk:251-277: the charge spills `rem` and the
  credit takes `min(amount, spilled)` back first).

Frame-creating path: `generic_call` builds the child message with `MSG_GAS = mcg.1`,
`MSG_RESERVOIR = reservoir` (:1129) and calls `start_child` kind 1 (:1133). **The child
receives `g + stipend`; the parent paid `g` plus >= 100 (>= 11400 when the stipend is
nonzero), so parent-decrease minus child-gas >= 100 (value 0) or >= 9100 (value != 0).
The 2300 stipend is the only gas added that was not subtracted, and it is always
covered by the 11300 charged in the same handler.** `EV_REGULAR_GAS_USED -= mcg.1`
(:1207 etc.) is bookkeeping only.

## 3. Frame machinery

### `run_frames` (evm_calls.pnk:683-722)

Kind (a) requires `CK_DONE == 0` (:687), `EV_RUNNING != 0` (:690), `pc < code_n`
(:694). An `EvmErr` from `op_dispatch` goes to `frame_exception(err)` (:699-701),
applied to whatever `ev` is at that time. Otherwise kind (b) (:705-718).

### `frame_exception(err)` (evm_calls.pnk:536-547)

- `refill_frame_state_gas()` (:537; evm.pnk:285-291): `gl += spilled`,
  `sgl := MSG_RESERVOIR`, `spilled := 0`. **Increases gas** (item 2 above).
- `err != E_REVERT`: `frame_halt` (:539; :762-767) sets `gl := 0`, adds the old `gl` to
  `EV_REGULAR_GAS_USED`, sets `EV_ERROR`; output cleared (:540-541). `sgl` stays at
  `MSG_RESERVOIR`.
- `err == E_REVERT`: only `EV_ERROR := err` (:543); `gl` (including the refill) is kept.
- `CK_DONE := 1` on `cur_cont` (:545). Does not touch `EV_RUNNING`, `ev`, `cur_cont`.

### `frame_epilogue()` (evm_calls.pnk:595-600)

`state_restore(CK_SNAPSHOT)` if `EV_ERROR != 0`. Touches no gas field, not `ev`,
`cur_cont`, `EV_RUNNING` or `CK_DONE`. Not under a `try`.

### `finish_child()` (evm_calls.pnk:606-678)

- Kind 2, child without error: `create_finish` (:622; :831-849) under `try`, on the
  child's fields (`ev` is still the child): `charge_gas(6 * words)` (:843),
  `charge_state_gas(n * 1530)` (:844); on `EvmErr`: `state_restore`,
  `refill_frame_state_gas` (increase, item 2), `frame_halt` (child `gl := 0`)
  (:623-629). Kind 2, child with error: `state_restore(csnap)` (:631).
- `ev := parent`, `cur_cont := CK_PARENT_CONT` (:634-635): the child is popped here.
- Child error (either kind): `incorporate_child_on_error` (parent `gl += child.gl`,
  `sgl += child.sgl`, :880-881), `credit_state_gas_refund(SG_NEW_ACCOUNT)` if
  `new_account_charged` (:641-643, :656-658), push 0.
- Child success: `incorporate_child_on_success` (:886-908): the same additions, plus
  `spilled += child.spilled` (:888) and the repay transfer `rep = min(sgl, spilled)`
  from `sgl` to `gl` (:890-896); `EV_REFUND += child refund` (:905, a counter).
- Releases child scratch / memory (:674-675), `pc_add(1)` on the parent (:676).
- Does not write `EV_RUNNING` or `CK_DONE`. The parent's `CK_DONE` is 0 and
  `EV_RUNNING` is 1 on return (inferred: the parent was in a kind-(a) iteration when
  it started the child, `CK_DONE` is only ever set to 1 at :545 / :589 on the current
  frame's record, and `EV_RUNNING` is set to 1 only in `frame_new`, evm.pnk:536).

### Can kind (b) be followed by kind (b) on the same frame without a pop?

Only if `finish_child` throws an `EvmErr` before :634 (then `frame_exception` at :716
would hit the still-current child and the next iteration is kind (b) on it again). The
statements before :634 outside the inner `try` are loads and `state_restore`, and the
inner catch body is `state_restore` / `refill_frame_state_gas` / `frame_halt` / stores;
none throws `EvmErr` (state.pnk:181-193, evm.pnk:285-291, evm_calls.pnk:762-767). So:
**no** (inferred; see open question 3). For kind 0 the loop exits (:708-711).

Consecutive kind-(b) iterations on *different* frames are possible: after the pop the
parent can have `pc >= code_n` (:694), giving one kind-(b) iteration per frame popped.
Hence #kind-(b) iterations = #frames opened (one per frame) (inferred).

### `start_child` / `frame_open` / `frame_start` (evm_calls.pnk:729-759, 520-532, 581-592)

- Kind 2 pre-work: snapshot, `destroy_storage`, `mark_account_created`,
  `increment_nonce` (:732-738).
- `frame_open` (:743): `frame_new` sets child `gl := MSG_GAS`, `sgl := MSG_RESERVOIR`,
  `EV_RUNNING := 1` (evm.pnk:530-536); new zeroed continuation record (`CK_DONE = 0`),
  `ev := child`, `cur_cont := rec` (:523-530).
- `frame_start` -> `frame_prologue` under `try` (:584-587): value transfer
  (:555-565), precompile shortcut (:566-575). An `EvmErr` there goes to
  `frame_exception` on the child. If the prologue returns 1, `CK_DONE := 1` (:588-590).

### Call-depth limit (`STACK_DEPTH_LIMIT` = 1024, evm.pnk:161)

- `generic_call`: `MSG_DEPTH + 1 > 1024` -> soft failure, gas handed back, push 0
  (evm_calls.pnk:1115-1123).
- `generic_create`: `MSG_DEPTH + 1 > 1024` -> push 0 (:1020-1023).
- `start_child`: `MSG_DEPTH(child) > 1024` -> `throw E_STACK_DEPTH_LIMIT` (:739-741);
  unreachable after the two checks above since child depth = parent depth + 1 (:936)
  (inferred).
- `process_message` (transaction level, outside the loop): :791-793.

So child depth <= 1024 and at most 1025 frames are live (inferred).

### Precompiles

Run **inside the kind-(a) iteration of the calling opcode**, on a real frame: the CALL
handler opens the child frame, `frame_prologue` calls `run_precompile(pi)` on it
(evm_calls.pnk:566-574; precompiles.pnk:229-250), which charges the child's `gl` via
`charge_gas` (precompiles.pnk:45, 55, 65, 100, 121, 207 and `precompiles_*.pnk`) and
sets `EV_OUTPUT`; then `CK_DONE := 1` (:588-590). The next iteration is kind (b) for
that frame. A precompile call therefore costs exactly 2 loop iterations and 0 opcode
iterations in the child. A precompile `EvmErr` goes to `frame_exception` on the child
(:585-587). With `MSG_DISABLE_PRECOMPILES` set (delegation target, :370, `dl.0` passed
at :1229) the precompile is skipped but the frame is still marked done (:570-573).
BLAKE2F can charge 0 (`rounds == 0`, precompiles.pnk:119-121); irrelevant since the
frame is done. The transaction-level frame can also be a precompile
(`process_message` -> `frame_start`, :825).

### Minimum gas a parent pays to create a frame

- CALL / CALLCODE / DELEGATECALL / STATICCALL: **100** regular gas (`G_WARM_ACCESS`,
  warm target, zero value, no memory growth, `g` may be 0) at evm_calls.pnk:1185,
  1260, 1317, 1363. This is not transferred to the child.
- CREATE / CREATE2: **12000** (`G_CREATE_ACCESS`) at :1066 / :1090.

So #frames opened inside `run_frames` <= (regular gas charged) / 100, if total
regular gas charged is itself bounded (open questions 1-2).

## 4. Coverage count

153 defined opcodes (12 at 0x00-0x0b, 15 at 0x10-0x1e, KECCAK256, 16 at 0x30-0x3f,
12 at 0x40-0x4b, 16 at 0x50-0x5f, 32 PUSH, 16 DUP, 16 SWAP, 5 LOG, 3 at 0xe6-0xe8,
9 system) plus the 103 byte values that throw `E_INVALID_OPCODE`: all 256 values.
