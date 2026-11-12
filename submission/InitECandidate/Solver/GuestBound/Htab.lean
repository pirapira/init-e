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
      order.toNat + ((ncapOf cp + 1#64) * 8#64).toNat ≤ q4.toNat ∧ q4.toNat ≤ 2952790016 ∧
      keys.toNat % 8 = 0 ∧ nodes.toNat % 8 = 0 ∧ order.toNat % 8 = 0 := by
  have hbody := (fun_of_index 128 hE.functions (by guest_decl_at 128) (by decide +kernel)
    hlookup).1
  subst hbody
  dsimp only at h
  rcases decCall_alloc hE (nv := 88#64) (by simp) hp hpH h with hst |
    ⟨q1, r1, hq1, hq1H, hq18, h1, rfl⟩
  · exact Or.inl hst
  have key : Stopped r1 ∨ ∃ (l : VarName → Option (PanValue Word)) (nodes order q4 : Word),
      r1 = .returned l
        (updatePanValueMap (updatePanValueMap (updatePanValueMap (updatePanValueMap s.globals
          "heap_ptr" (.word q1)) "heap_ptr" (.word nodes)) "heap_ptr" (.word order))
          "heap_ptr" (.word q4))
        (htabHeader s.memory pv kl cp q1 nodes order) s.ffi [.word pv] ∧
      q1.toNat + ((ncapOf cp + 1#64) * strideOf kl).toNat ≤ nodes.toNat ∧
      nodes.toNat + ((ncapOf cp + 1#64) * 32#64).toNat ≤ order.toNat ∧
      order.toNat + ((ncapOf cp + 1#64) * 8#64).toNat ≤ q4.toNat ∧ q4.toNat ≤ 2952790016 ∧
      nodes.toNat % 8 = 0 ∧ order.toNat % 8 = 0 := by
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
      ⟨q2, r4, hq2, hq2H, hq28, h8, rfl⟩
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases seq_store hE (addr := pv + 32#64) (w := q1) (by ev [hlt]) (by ev []) h8 with
      hst | h9
    · exact Or.inl (by repeat (first | exact hst | apply Stopped.restore))
    rcases decCall_alloc hE (nv := (ncapOf cp + 1#64) * 32#64) (pv := q2)
      (by ev [hlnc]) (by simp [update_lookup]) hq2H h9 with hst |
      ⟨q3, r5, hq3, hq3H, hq38, h10, rfl⟩
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
    exact Or.inr ⟨_, q2, q3, q4, rfl, hq2, hq3, hq4, hq4H, hq28, hq38⟩
  rcases key with hst | ⟨l, nodes, order, q4, rfl, hb1, hb2, hb3, hb4, hb5, hb6⟩
  · exact Or.inl hst.restore
  · have h88 : (88#64).toNat = 88 := by decide
    exact Or.inr ⟨_, q1, nodes, order, q4, rfl, by omega, hb1, hb2, hb3, hb4, hq18, hb5, hb6⟩

theorem add_beq (t a b : Word) : (t + a == t + b) = (a == b) := by
  by_cases hab : a = b
  · simp [hab]
  · have : t + a ≠ t + b := by
      intro h
      apply hab
      have := congrArg (fun z => z - t) h
      simpa using this
    simp [hab, this]

/-- The cell at `a` holds the word `w`. -/
def Rd (m : Word → Option (PanValue Word)) (a w : Word) : Prop := m a = some (.word w)

/-- The values of a table's header fields. -/
structure HtabV where
  kl : Word
  st : Word
  cp : Word
  nc : Word
  cnt : Word
  keys : Word
  nodes : Word
  order : Word
  root : Word
  next : Word
  free : Word

/-- The header at `t` holds the fields `v`. -/
def HtabHdr (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV) : Prop :=
  Rd m (t + 0#64) v.kl ∧ Rd m (t + 8#64) v.st ∧ Rd m (t + 16#64) v.cp ∧
    Rd m (t + 24#64) v.cnt ∧ Rd m (t + 32#64) v.keys ∧ Rd m (t + 40#64) v.nodes ∧
    Rd m (t + 48#64) v.order ∧ Rd m (t + 56#64) v.root ∧ Rd m (t + 64#64) v.next ∧
    Rd m (t + 72#64) v.free ∧ Rd m (t + 80#64) v.nc

/-- A fresh header reads back as an empty table. -/
theorem htabHeader_hdr (m : Word → Option (PanValue Word)) (t kl cp keys nodes order : Word) :
    HtabHdr (htabHeader m t kl cp keys nodes order) t
      ⟨kl, strideOf kl, cp, ncapOf cp, 0#64, keys, nodes, order, 0#64, 1#64, 0#64⟩ := by
  simp (config := { decide := true }) [HtabHdr, Rd, htabHeader, setCell, add_beq]

/-- A fresh header changes no cell outside the header. -/
theorem htabHeader_frame (m : Word → Option (PanValue Word)) (t kl cp keys nodes order a : Word)
    (ha : 88 ≤ (a - t).toNat) : htabHeader m t kl cp keys nodes order a = m a := by
  have hne : ∀ k : Word, k.toNat < 88 → (a == t + k) = false := by
    intro k hk
    have : a ≠ t + k := by
      intro h
      rw [h] at ha
      have : (t + k - t) = k := by simp
      rw [this] at ha
      omega
    simpa using this
  have h0 : (a == t) = false := by simpa using hne 0#64 (by decide)
  simp [htabHeader, setCell, h0, hne 8#64 (by decide), hne 16#64 (by decide),
    hne 24#64 (by decide), hne 32#64 (by decide), hne 40#64 (by decide), hne 48#64 (by decide),
    hne 56#64 (by decide), hne 64#64 (by decide), hne 72#64 (by decide), hne 80#64 (by decide)]

/-! ### The table invariant -/

/-- Ghost classification of the node indices handed out so far. -/
inductive NodeKind where
  | internal
  | leaf
  | free
  deriving DecidableEq

/-- Address of field `off` of node `i`. -/
def nodeField (v : HtabV) (i off : Nat) : Word := v.nodes + BitVec.ofNat 64 (i * 32 + off)

/-- Address of entry `pos` of the insertion-order array. -/
def orderSlot (v : HtabV) (pos : Nat) : Word := v.order + BitVec.ofNat 64 (pos * 8)

/-- The four blocks of a table lie one after another inside the heap, with
sizes that do not wrap. -/
def HtabLayout (t : Word) (v : HtabV) : Prop :=
  t.toNat + 88 ≤ v.keys.toNat ∧
    v.keys.toNat + (v.nc.toNat + 1) * v.st.toNat ≤ v.nodes.toNat ∧
    v.nodes.toNat + (v.nc.toNat + 1) * 32 ≤ v.order.toNat ∧
    v.order.toNat + (v.nc.toNat + 1) * 8 ≤ 2952790016

/-- `p` is the parent recorded for a live node `i`: none for the root, or an
internal node that has `i` as a child. -/
def ParentOk (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind)
    (i : Nat) (p : Word) : Prop :=
  (p = 0 ∧ v.root.toNat = i) ∨
    (1 ≤ p.toNat ∧ p.toNat < v.next.toNat ∧ kind p.toNat = .internal ∧
      (Rd m (nodeField v p.toNat 8) (BitVec.ofNat 64 i) ∨
        Rd m (nodeField v p.toNat 16) (BitVec.ofNat 64 i)))

/-- A live child link: an index handed out, not free, whose parent field is `i`. -/
def ChildOk (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind)
    (i : Nat) (c : Word) : Prop :=
  1 ≤ c.toNat ∧ c.toNat < v.next.toNat ∧ kind c.toNat ≠ .free ∧
    Rd m (nodeField v c.toNat 0) (BitVec.ofNat 64 i)

/-- The free list: `fl` lists the free nodes from `head`, linked through field 0. -/
def FreeChain (m : Word → Option (PanValue Word)) (v : HtabV) (kind : Nat → NodeKind) :
    Word → List Nat → Prop
  | head, [] => head = 0#64
  | head, i :: rest => head.toNat = i ∧ 1 ≤ i ∧ i < v.next.toNat ∧ kind i = .free ∧ i ∉ rest ∧
      ∃ f : Word, Rd m (nodeField v i 0) f ∧ FreeChain m v kind f rest

theorem FreeChain.kind_mem {m : Word → Option (PanValue Word)} {v : HtabV}
    {kind : Nat → NodeKind} : ∀ (fl : List Nat) (hd : Word), FreeChain m v kind hd fl →
      ∀ i, i ∈ fl → kind i = .free ∧ 1 ≤ i ∧ i < v.next.toNat
  | [], _, _, i, hi => by cases hi
  | j :: rest, _, ⟨_, h2, h3, h4, _, f, _, hc⟩, i, hi => by
      rcases List.mem_cons.mp hi with h | h
      · subst h
        exact ⟨h4, h2, h3⟩
      · exact FreeChain.kind_mem rest f hc i h

/-- A free list survives changes that keep its nodes free and their links readable. -/
theorem FreeChain.congr {m m' : Word → Option (PanValue Word)} {v v' : HtabV}
    {kind kind' : Nat → NodeKind} (hnext : v.next.toNat ≤ v'.next.toNat) :
    ∀ (fl : List Nat) (hd : Word), FreeChain m v kind hd fl →
      (∀ i, i ∈ fl → kind' i = .free ∧
        ∀ w, Rd m (nodeField v i 0) w → Rd m' (nodeField v' i 0) w) →
      FreeChain m' v' kind' hd fl
  | [], _, h, _ => h
  | j :: rest, _, ⟨h1, h2, h3, _, h5, f, hf, hc⟩, hall =>
      ⟨h1, h2, Nat.lt_of_lt_of_le h3 hnext, (hall j List.mem_cons_self).1, h5, f,
        (hall j List.mem_cons_self).2 f hf,
        FreeChain.congr hnext rest f hc (fun i hi => hall i (List.mem_cons_of_mem _ hi))⟩

/-- The table at `t` is well formed in memory `m`, with header fields `v` and
node classification `kind`. -/
structure HtabWF (m : Word → Option (PanValue Word)) (t : Word) (v : HtabV)
    (kind : Nat → NodeKind) : Prop where
  hdr : HtabHdr m t v
  layout : HtabLayout t v
  next_pos : 1 ≤ v.next.toNat
  next_le : v.next.toNat ≤ v.nc.toNat + 1
  cnt_le : v.cnt.toNat ≤ v.nc.toNat
  /-- The root is absent or a live node without a parent. -/
  root_ok : v.root = 0 ∨ (1 ≤ v.root.toNat ∧ v.root.toNat < v.next.toNat ∧
    kind v.root.toNat ≠ .free ∧ Rd m (nodeField v v.root.toNat 0) 0)
  /-- The free nodes on the free list. -/
  free_chain : ∃ fl : List Nat, FreeChain m v kind v.free fl
  /-- An internal node: bit index below the key length, two distinct live children. -/
  internal_ok : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .internal →
    ∃ p l r b : Word, Rd m (nodeField v i 0) p ∧ Rd m (nodeField v i 8) l ∧
      Rd m (nodeField v i 16) r ∧ Rd m (nodeField v i 24) b ∧ b ≠ v.kl * 8#64 ∧
      ParentOk m v kind i p ∧ ChildOk m v kind i l ∧ ChildOk m v kind i r ∧ l ≠ r
  /-- A leaf: kind field is the key length in bits, and its order position names it. -/
  leaf_ok : ∀ i, 1 ≤ i → i < v.next.toNat → kind i = .leaf →
    ∃ p value pos : Word, Rd m (nodeField v i 0) p ∧ Rd m (nodeField v i 8) value ∧
      Rd m (nodeField v i 16) pos ∧ Rd m (nodeField v i 24) (v.kl * 8#64) ∧
      ParentOk m v kind i p ∧ pos.toNat < v.cnt.toNat ∧
      Rd m (orderSlot v pos.toNat) (BitVec.ofNat 64 i)
  /-- Every order entry below the count is a leaf that records that position. -/
  order_ok : ∀ pos, pos < v.cnt.toNat →
    ∃ i : Word, Rd m (orderSlot v pos) i ∧ 1 ≤ i.toNat ∧ i.toNat < v.next.toNat ∧
      kind i.toNat = .leaf ∧ Rd m (nodeField v i.toNat 16) (BitVec.ofNat 64 pos)

/-- A fresh table is well formed, given sizes that do not wrap. -/
theorem htabWF_new (m : Word → Option (PanValue Word)) (t kl cp keys nodes order : Word)
    (hlay : HtabLayout t
      ⟨kl, strideOf kl, cp, ncapOf cp, 0#64, keys, nodes, order, 0#64, 1#64, 0#64⟩) :
    HtabWF (htabHeader m t kl cp keys nodes order) t
      ⟨kl, strideOf kl, cp, ncapOf cp, 0#64, keys, nodes, order, 0#64, 1#64, 0#64⟩
      (fun _ => .free) where
  hdr := htabHeader_hdr m t kl cp keys nodes order
  layout := hlay
  next_pos := by
    show 1 ≤ (1#64).toNat
    decide
  next_le := by
    show (1#64).toNat ≤ _
    have : (1#64).toNat = 1 := by decide
    omega
  cnt_le := by
    show (0#64).toNat ≤ _
    have : (0#64).toNat = 0 := by decide
    omega
  root_ok := Or.inl rfl
  free_chain := ⟨[], rfl⟩
  internal_ok := by intro i _ _ h; cases h
  leaf_ok := by intro i _ _ h; cases h
  order_ok := by
    intro pos h
    have : (0#64).toNat = 0 := by decide
    simp only at h
    omega

end InitECandidate.Solver.GuestBound
