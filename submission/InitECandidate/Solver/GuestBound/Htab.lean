import InitECandidate.Solver.GuestBound.Heap

/-!
# Hash tables: construction

Step lemmas for straight-line code that allocates and stores, and the
specification of `htab_new`: the header cells it writes and the four blocks
it allocates one after another.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

theorem Stopped.restore {x : VarName} {old : Option (PanValue Word)} {r : Result σ}
    (h : Stopped r) : Stopped (restorePanValueFfiLocal x old r) := by
  cases r <;> first | trivial | cases h

/-- `store a v; rest` with word operands: stopped, or `rest` runs with the cell rewritten. -/
theorem seq_store (hE : GuestEnv E) {a v : Exp Word} {rest : Prog Word} {s : St σ}
    {r : Result σ} {addr w : Word} (ha : E.eval s a = some (.word addr))
    (hv : E.eval s v = some (.word w)) (h : Runs E s (.seq (.store a v) rest) r) :
    Stopped r ∨ Runs E ⟨s.locals, s.globals, setCell s.memory addr w, s.ffi⟩ rest r := by
  obtain ⟨r₁, h₁, hrest⟩ := runs_seq.mp h
  rcases runs_store_word hE ha hv h₁ with herr | rfl
  · cases r₁ with
    | error l g m f =>
      simp only at hrest
      subst hrest
      exact Or.inl trivial
    | _ => cases herr
  · exact Or.inr hrest

/-- `var x = e; body` with a word value. -/
theorem dec_word_runs {x : VarName} {e : Exp Word} {body : Prog Word} {s : St σ}
    {r : Result σ} {w : Word} (he : E.eval s e = some (.word w))
    (h : Runs E s (.dec x .one e body) r) :
    ∃ r', Runs E ⟨updatePanValueMap s.locals x (.word w), s.globals, s.memory, s.ffi⟩ body r' ∧
      r = restorePanValueFfiLocal x (s.locals x) r' := by
  rw [runs_dec] at h
  simp only [he, shape_word, shape_matches_self, if_true] at h
  exact h

/-- `x + k` for a word local `x`. -/
theorem eval_addc (hE : GuestEnv E) {s : St σ} {x : VarName} {a : Word} (k : Word)
    (hx : s.locals x = some (.word a)) :
    E.eval s (.op .add [.var .local x, .const k]) = some (.word (a + k)) := by
  simp [evalF_op hE.word, evalArgs_cons, evalArgs_nil, evalF_local, hx, wordsProj_cons,
    wordsProj_nil, wordOp]

/-- `if x <+ k { x = k; }`. -/
theorem floorIte_runs (hE : GuestEnv E) {x : VarName} {xv k : Word} {s : St σ} {r : Result σ}
    (hx : s.locals x = some (.word xv)) :
    Runs E s (.ite (.cmp .lower (.var .local x) (.const k)) (.assign .local x (.const k))
      .skip) r →
    ∃ l, r = .normal l s.globals s.memory s.ffi ∧
      l x = some (.word (if xv < k then k else xv)) ∧ ∀ y, y ≠ x → l y = s.locals y := by
  intro h
  rw [runs_ite] at h
  simp only [evalF_cmp hE.word, evalF_local, eval_const, hx] at h
  by_cases hlt : xv < k
  · simp [evalPanCmp, hlt] at h
    rw [runs_assign_local] at h
    simp [eval_const, panValueAssignmentValid, hx, shape_word, shape_matches_self] at h
    subst h
    refine ⟨_, rfl, by simp [update_lookup, hlt], ?_⟩
    intro y hy
    have : (y == x) = false := by simpa using hy
    simp [update_lookup, this]
  · simp [evalPanCmp, hlt] at h
    rw [runs_skip] at h
    subst h
    exact ⟨_, rfl, by simp [hlt, hx], fun _ _ => rfl⟩

-- `ev [facts]`: evaluate an expression over known locals.
set_option hygiene false in
open Lean.Parser.Tactic in
macro "ev" "[" hs:simpLemma,* "]" : tactic => `(tactic|
  simp (config := { decide := true }) [evalF_op hE.word, evalF_panOp, evalArgs_cons,
    evalArgs_nil, evalF_local, update_lookup, wordsProj_cons, wordsProj_nil, wordOp, $hs,*])

/-- The stride of a table: the key length rounded up to 8. -/
def strideOf (kl : Word) : Word :=
  AndOp.and (kl + (7#64 + 0)) (AndOp.and (0#64 - 8#64) (~~~(0 : BitVec 64)))

/-- The node capacity of a table: at least 2. -/
def ncapOf (cp : Word) : Word := if cp < 2#64 then 2#64 else cp

/-- The header cells written by `htab_new`. -/
def htabHeader (m : Word → Option (PanValue Word)) (t kl cp keys nodes order : Word) :
    Word → Option (PanValue Word) :=
  setCell (setCell (setCell (setCell (setCell (setCell (setCell (setCell (setCell (setCell
    (setCell m (t + 0#64) kl) (t + 8#64) (strideOf kl)) (t + 16#64) cp) (t + 24#64) 0#64)
    (t + 32#64) keys) (t + 40#64) nodes) (t + 48#64) order) (t + 56#64) 0#64) (t + 64#64) 1#64)
    (t + 72#64) 0#64) (t + 80#64) (ncapOf cp)

set_option maxHeartbeats 4000000 in
/-- `htab_new`: the table header at the old heap pointer, then the key, node
and order blocks, each past the previous one and inside the heap. -/
theorem htab_new_runs (hE : GuestEnv E) (parameters : List VarName) (body : Prog Word)
    (hlookup : lookupPanFunction "htab_new" E.functions = some (parameters, body))
    (s : St σ) (r : Result σ) (kl cp pv : Word) (hk : s.locals "key_len" = some (.word kl))
    (hc : s.locals "cap" = some (.word cp)) (hp : s.globals "heap_ptr" = some (.word pv))
    (hpH : pv.toNat ≤ 2952790016) (h : Runs E s body r) :
    Stopped r ∨ ∃ (l : VarName → Option (PanValue Word)) (keys nodes order q4 : Word),
      r = .returned l
        (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals
          "heap_ptr" (.word keys)) "heap_ptr" (.word nodes)) "heap_ptr" (.word order))
          "heap_ptr" (.word q4))
        (htabHeader s.memory pv kl cp keys nodes order) s.ffi [.word pv] ∧
      pv.toNat + 88 ≤ keys.toNat ∧
      keys.toNat + ((ncapOf cp + 1#64) * strideOf kl).toNat ≤ nodes.toNat ∧
      nodes.toNat + ((ncapOf cp + 1#64) * 32#64).toNat ≤ order.toNat ∧
      order.toNat + ((ncapOf cp + 1#64) * 8#64).toNat ≤ q4.toNat ∧ q4.toNat ≤ 2952790016 := by
  have hbody := (fun_of_index 128 hE.functions (by guest_decl_at 128) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  rcases decCall_alloc hE (nv := 88#64) (by simp) hp hpH h with hst |
    ⟨q1, r1, hq1, hq1H, -, h1, rfl⟩
  · exact Or.inl hst
  have key : Stopped r1 ∨ ∃ (l : VarName → Option (PanValue Word)) (nodes order q4 : Word),
      r1 = .returned l
        (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals
          "heap_ptr" (.word q1)) "heap_ptr" (.word nodes)) "heap_ptr" (.word order))
          "heap_ptr" (.word q4))
        (htabHeader s.memory pv kl cp q1 nodes order) s.ffi [.word pv] ∧
      q1.toNat + ((ncapOf cp + 1#64) * strideOf kl).toNat ≤ nodes.toNat ∧
      nodes.toNat + ((ncapOf cp + 1#64) * 32#64).toNat ≤ order.toNat ∧
      order.toNat + ((ncapOf cp + 1#64) * 8#64).toNat ≤ q4.toNat ∧ q4.toNat ≤ 2952790016 := by
    obtain ⟨r2, h2, rfl⟩ := dec_word_runs (w := strideOf kl) (by ev [hk, strideOf]) h1
    obtain ⟨r3, h3, rfl⟩ := dec_word_runs (w := cp) (by ev [hc]) h2
    obtain ⟨r₁, hi, hrest⟩ := runs_seq.mp h3
    obtain ⟨l, rfl, hln, hlf⟩ := floorIte_runs hE (x := "ncap") (xv := cp) (k := 2#64)
      (by ev []) hi
    simp only at hrest
    dsimp only at hln hlf
    have hlt : l "t" = some (.word pv) := by rw [hlf "t" (by decide)]; ev []
    have hlk : l "key_len" = some (.word kl) := by rw [hlf "key_len" (by decide)]; ev [hk]
    have hls : l "stride" = some (.word (strideOf kl)) := by
      rw [hlf "stride" (by decide)]; ev []
    have hlc : l "cap" = some (.word cp) := by rw [hlf "cap" (by decide)]; ev [hc]
    have hlnc : l "ncap" = some (.word (ncapOf cp)) := hln
    rcases seq_store hE (addr := pv + 0#64) (w := kl) (by ev [hlt]) (by ev [hlk]) hrest with
      hst | h4
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 8#64) (w := strideOf kl) (by ev [hlt]) (by ev [hls]) h4
      with hst | h5
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 16#64) (w := cp) (by ev [hlt]) (by ev [hlc]) h5 with
      hst | h6
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 24#64) (w := 0#64) (by ev [hlt]) (by simp) h6 with
      hst | h7
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases decCall_alloc hE (nv := (ncapOf cp + 1#64) * strideOf kl) (pv := q1)
      (by ev [hlnc, hls]) (by simp [update_lookup]) hq1H h7 with hst |
      ⟨q2, r4, hq2, hq2H, -, h8, rfl⟩
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 32#64) (w := q1) (by ev [hlt]) (by ev []) h8 with
      hst | h9
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases decCall_alloc hE (nv := (ncapOf cp + 1#64) * 32#64) (pv := q2)
      (by ev [hlnc]) (by simp [update_lookup]) hq2H h9 with hst |
      ⟨q3, r5, hq3, hq3H, -, h10, rfl⟩
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 40#64) (w := q2) (by ev [hlt]) (by ev []) h10 with
      hst | h11
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases decCall_alloc hE (nv := (ncapOf cp + 1#64) * 8#64) (pv := q3)
      (by ev [hlnc]) (by simp [update_lookup]) hq3H h11 with hst |
      ⟨q4, r6, hq4, hq4H, -, h12, rfl⟩
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 48#64) (w := q3) (by ev [hlt]) (by ev []) h12 with
      hst | h13
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 56#64) (w := 0#64) (by ev [hlt]) (by simp) h13 with
      hst | h14
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 64#64) (w := 1#64) (by ev [hlt]) (by simp) h14 with
      hst | h15
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 72#64) (w := 0#64) (by ev [hlt]) (by simp) h15 with
      hst | h16
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 80#64) (w := ncapOf cp) (by ev [hlt]) (by ev [hlnc]) h16
      with hst | h17
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rw [runs_return] at h17
    simp (config := { decide := true }) only [evalF_local, update_lookup, if_false, hlt,
      payload_word, if_true] at h17
    subst h17
    simp only [restorePanValueFfiLocal]
    exact Or.inr ⟨_, q2, q3, q4, rfl, hq2, hq3, hq4, hq4H⟩
  rcases key with hst | ⟨l, nodes, order, q4, rfl, hb1, hb2, hb3, hb4⟩
  · exact Or.inl hst.restore
  · have h88 : (88#64).toNat = 88 := by decide
    exact Or.inr ⟨_, q1, nodes, order, q4, rfl, by omega, hb1, hb2, hb3, hb4⟩

/-- Reading a header field back from a freshly built header. -/
theorem htabHeader_count (m : Word → Option (PanValue Word)) (t kl cp keys nodes order : Word) :
    htabHeader m t kl cp keys nodes order (t + 24#64) = some (.word 0#64) := by
  have h : ∀ a b : Word, (t + a == t + b) = (a == b) := by
    intro a b
    by_cases hab : a = b
    · simp [hab]
    · have : t + a ≠ t + b := by
        intro h
        apply hab
        have := congrArg (fun z => z - t) h
        simpa using this
      simp [hab, this]
  simp (config := { decide := true }) [htabHeader, setCell, h]

end InitECandidate.Solver.GuestBound
