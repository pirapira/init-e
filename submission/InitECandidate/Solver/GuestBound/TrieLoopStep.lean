import InitECandidate.Solver.GuestBound.TrieLoopExt

/-!
# The insertion loop: the big conditional of one iteration

`ins_step` dispatches on the current node: null, hashed (fails), leaf,
extension or branch; a non-null node has its cache fields cleared first.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ} {s : St σ} {Q : Result σ → Prop}

/-- Leaving the scope of `k`, with the memory frame taken back to an earlier memory. -/
theorem InsMid.exit_k {R0 : Reg} {g0 : VarName → Option (PanValue Word)}
    {m0 m1 : Word → Option (PanValue Word)} {key klen vptr vlen lv sl res : Word}
    {l' g' : VarName → Option (PanValue Word)} {m' : Word → Option (PanValue Word)}
    (old : Option (PanValue Word))
    (h : InsMid R0 g0 m1 key klen vptr vlen lv sl res l' g' m')
    (hm : ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
      m1 addr = m0 addr) :
    InsMid R0 g0 m0 key klen vptr vlen lv sl res (restorePanValueLocal l' "k" old) g' m' := by
  obtain ⟨R, rv, kk, gw, nn, ns, nlv, nd', hle, hW, hg, hmm, a1, a2, a3, a4, a5, a6, a7, a8,
    a9, a10, a11, a12, a13, rest⟩ := h
  exact ⟨R, rv, kk, gw, nn, ns, nlv, nd', hle, hW, hg,
    fun addr ha => (hmm addr ha).trans (hm addr ha),
    by simp (config := { decide := true }) [restorePanValueLocal, a1],
    by simp (config := { decide := true }) [restorePanValueLocal, a2],
    by simp (config := { decide := true }) [restorePanValueLocal, a3],
    by simp (config := { decide := true }) [restorePanValueLocal, a4],
    by simp (config := { decide := true }) [restorePanValueLocal, a5],
    by simp (config := { decide := true }) [restorePanValueLocal, a6],
    by simp (config := { decide := true }) [restorePanValueLocal, a7],
    by simp (config := { decide := true }) [restorePanValueLocal, a8],
    by simp (config := { decide := true }) [restorePanValueLocal, a9],
    by simp (config := { decide := true }) [restorePanValueLocal, a10],
    by simp (config := { decide := true }) [restorePanValueLocal, a11],
    by simp (config := { decide := true }) [restorePanValueLocal, a12],
    by simp (config := { decide := true }) [restorePanValueLocal, a13], rest⟩

/-- The body locals with `k` declared. -/
theorem InsLoc.with_k {l : VarName → Option (PanValue Word)}
    {key klen vptr vlen lv nd sl res : Word} (h : InsLoc l key klen vptr vlen lv nd sl res)
    (k : Word) : InsLoc (updatePanValueMap l "k" (.word k)) key klen vptr vlen lv nd sl res :=
  ⟨by lk [h.key], by lk [h.klen], by lk [h.vptr], by lk [h.vlen], by lk [h.level],
    by lk [h.node], by lk [h.slot], by lk [h.result], by lk [h.r], by lk [h.go], by lk [h.nn],
    by lk [h.ns], by lk [h.nl]⟩

set_option maxHeartbeats 16000000 in
theorem ins_step (hE : GuestEnv E) {R0 : Reg} {key klen vptr vlen lv nd sl res : Word}
    (hL : InsLoc s.locals key klen vptr vlen lv nd sl res)
    (hW : WorldTJ R0 s.globals s.memory) (hnd : nd = 0#64 ∨ ∃ k, R0.Kd nd k)
    (hLn : nd ≠ 0#64 → R0.Lv nd lv.toNat) (hlv : lv.toNat ≤ klen.toNat)
    (hkey : klen ≠ 0#64 → ∃ lo hi, R0.Im lo hi ∧ lo.toNat ≤ key.toNat ∧
      key.toNat + klen.toNat ≤ hi.toNat)
    (hQ : ∀ l' g' m', InsMid R0 s.globals s.memory key klen vptr vlen lv sl res l' g' m' →
      Q (.normal l' g' m' s.ffi)) :
    WPs E s (.ite (.cmp .equal (.var .local "node") (.const 0#64))
      (.call (some (some (.local, "r"), none)) "node_new_leaf"
        [.op .add [.var .local "key", .var .local "level"],
          .op .sub [.var .local "klen", .var .local "level"], .var .local "vptr",
          .var .local "vlen"])
      (.dec "k" .one (.load .one (.op .add [.var .local "node", .const 0#64]))
        (.seq (.ite (.cmp .equal (.var .local "k") (.const 0#64))
            (.call (some (none, none)) "mpt_fail" [.const 2#64]) .skip)
          (.seq (.call (some (none, none)) "node_invalidate" [.var .local "node"])
            (.ite (.cmp .equal (.var .local "k") (.const 1#64))
              (.call (some (some (.local, "r"), none)) "_insert_into_leaf"
                [.var .local "node", .op .add [.var .local "key", .var .local "level"],
                  .op .sub [.var .local "klen", .var .local "level"], .var .local "vptr",
                  .var .local "vlen"])
              (.ite (.cmp .equal (.var .local "k") (.const 2#64))
                (.dec "seg" .one (.load .one (.op .add [.var .local "node", .const 32#64]))
                  (.dec "sl" .one (.load .one (.op .add [.var .local "node", .const 40#64]))
                    (.decCall "pl" .one "common_prefix_length"
                      [.var .local "seg", .var .local "sl",
                        .op .add [.var .local "key", .var .local "level"],
                        .op .sub [.var .local "klen", .var .local "level"]]
                      (.ite (.cmp .equal (.var .local "pl") (.var .local "sl"))
                        (.seq (.assign .local "r" (.var .local "node"))
                          (.seq (.assign .local "next_node"
                              (.load .one (.op .add [.var .local "node", .const 48#64])))
                            (.seq (.assign .local "next_slot"
                                (.op .add [.var .local "node", .const 48#64]))
                              (.seq (.assign .local "next_level"
                                  (.op .add [.var .local "level", .var .local "pl"]))
                                (.assign .local "go" (.const 1#64))))))
                        (.decCall "br" .one "_split_extension"
                          [.var .local "node", .op .add [.var .local "key", .var .local "level"],
                            .op .sub [.var .local "klen", .var .local "level"],
                            .var .local "vptr", .var .local "vlen", .var .local "pl"]
                          (.ite (.cmp .lower (.const 0#64) (.var .local "pl"))
                            (.call (some (some (.local, "r"), none)) "node_new_ext"
                              [.var .local "seg", .var .local "pl", .var .local "br"])
                            (.assign .local "r" (.var .local "br"))))))))
                (.ite (.cmp .equal (.var .local "level") (.var .local "klen"))
                  (.seq (.store (.op .add [.var .local "node", .const 160#64])
                      (.var .local "vptr"))
                    (.seq (.store (.op .add [.var .local "node", .const 168#64])
                        (.var .local "vlen"))
                      (.assign .local "r" (.var .local "node"))))
                  (.dec "idx" .one
                    (.loadByte (.op .add [.var .local "key", .var .local "level"]))
                    (.seq (.assign .local "r" (.var .local "node"))
                      (.seq (.assign .local "next_node" (.load .one (.op .add
                          [.var .local "node", .const 32#64,
                            .panOp .mul [.var .local "idx", .const 8#64]])))
                        (.seq (.assign .local "next_slot" (.op .add [.var .local "node",
                            .const 32#64, .panOp .mul [.var .local "idx", .const 8#64]]))
                          (.seq (.assign .local "next_level"
                              (.op .add [.var .local "level", .const 1#64]))
                            (.assign .local "go" (.const 1#64)))))))))))))) Q := by
  refine WPs.ite_both (fun w hw => ?_)
  obtain ⟨x, y, hx, hy, hwv⟩ := cmp_word_inv hE hw
  rw [evalF_local, hL.node] at hx
  rw [eval_const] at hy
  simp only [Option.some.injEq, PanValue.word.injEq] at hx hy
  subst hx hy
  split
  · rename_i h0
    have hne : nd ≠ 0#64 := by
      rintro rfl
      rw [h0] at hwv
      simp [evalPanCmp] at hwv
    obtain ⟨k, hKd⟩ : ∃ k, R0.Kd nd k := by
      rcases hnd with h | h
      · exact absurd h hne
      · exact h
    obtain ⟨hNd, hRd, hlo, htop, h8⟩ := hW.kd hKd
    obtain ⟨hk3, -, -, -⟩ := hW.node_kind hNd hRd
    refine WPs.dec (w := k) (eval_load_rd hE (eval_addc hE 0#64 hL.node)
      (by rw [BitVec.add_zero]; exact hRd)) ?_
    have hLk := hL.with_k k
    refine WPs.seqG (fun a => a = ⟨updatePanValueMap s.locals "k" (.word k), s.globals,
        s.memory, s.ffi⟩ ∧ k ≠ 0#64) (WPs.ite_both (fun w2 hw2 => ?_)) ?_
    · obtain ⟨x, y, hx, hy, hwv2⟩ := cmp_word_inv hE hw2
      rw [eval_const] at hy
      rw [evalF_local] at hx
      simp (config := { decide := true }) [update_lookup] at hx hy
      subst hx hy
      split
      · rename_i h2
        refine WPs.skip ⟨rfl, ?_⟩
        rintro rfl
        rw [h2] at hwv2
        simp [evalPanCmp] at hwv2
      · exact fun r hr => Or.inl (stops_call_noReturn (mpt_fail_noReturn hE) hr)
    rintro _ ⟨rfl, hk0⟩
    refine WPs.seqG (fun a => ∃ m', a = ⟨updatePanValueMap s.locals "k" (.word k), s.globals,
        m', s.ffi⟩ ∧ WorldTJ R0 s.globals m' ∧
        ∀ addr : Word, (addr.toNat + 8 ≤ HBASE ∨ 2952790016 ≤ addr.toNat) →
          m' addr = s.memory addr) (WPs.call_ret (fun vs g m ffi hret => ?_)) ?_
    · obtain ⟨rfl, rfl, hW1, hm1⟩ := node_invalidate_ret hE hret (a := nd) (k := k)
        (of_eval (by lk [hL.node])) hW hNd hRd hk0
      exact ⟨m, rfl, hW1, hm1⟩
    rintro _ ⟨m1, rfl, hW1, hm1⟩
    have hQk : ∀ l' g' m', InsMid R0 s.globals m1 key klen vptr vlen lv sl res l' g' m' →
        Q (restorePanValueFfiLocal "k" (s.locals "k") (.normal l' g' m' s.ffi)) := by
      intro l' g' m' hmid
      simp only [restorePanValueFfiLocal]
      exact hQ _ _ _ (hmid.exit_k _ hm1)
    have hk1ne : ∀ c : Word, k ≠ c → k.toNat ≠ c.toNat :=
      fun c hc he => hc (BitVec.eq_of_toNat_eq he)
    refine WPs.ite_both (fun w3 hw3 => ?_)
    obtain ⟨x, y, hx, hy, hwv3⟩ := cmp_word_inv hE hw3
    rw [eval_const] at hy
    rw [evalF_local] at hx
    simp (config := { decide := true }) [update_lookup] at hx hy
    subst hx hy
    split
    · rename_i h3
      have hk1 : k ≠ 1#64 := by
        rintro rfl
        rw [h3] at hwv3
        simp [evalPanCmp] at hwv3
      refine WPs.ite_both (fun w4 hw4 => ?_)
      obtain ⟨x, y, hx, hy, hwv4⟩ := cmp_word_inv hE hw4
      rw [eval_const] at hy
      rw [evalF_local] at hx
      simp (config := { decide := true }) [update_lookup] at hx hy
      subst hx hy
      split
      · rename_i h4
        have hk2 : k ≠ 2#64 := by
          rintro rfl
          rw [h4] at hwv4
          simp [evalPanCmp] at hwv4
        have hk3' : k = 3#64 := by
          have a0 := hk1ne 0#64 hk0
          have a1 := hk1ne 1#64 hk1
          have a2 := hk1ne 2#64 hk2
          simp at a0 a1 a2
          exact BitVec.eq_of_toNat_eq (by simp; omega)
        subst hk3'
        exact ins_branch hE hLk hW1 hKd (hLn hne) hlv hkey hQk
      · rename_i h4
        have hk2 : k = 2#64 := by
          by_contra hne2
          exact h4 (by rw [hwv4]; simp [evalPanCmp, hne2])
        subst hk2
        exact ins_ext hE hLk hW1 hKd (hLn hne) hlv hkey hQk
    · rename_i h3
      have hk1 : k = 1#64 := by
        by_contra hne1
        exact h3 (by rw [hwv3]; simp [evalPanCmp, hne1])
      subst hk1
      exact ins_leaf hE hLk hW1 hKd (hLn hne) hlv hkey hQk
  · rename_i h0
    exact ins_null hE hL hW hlv hkey hQ

end InitECandidate.Solver.GuestBound
