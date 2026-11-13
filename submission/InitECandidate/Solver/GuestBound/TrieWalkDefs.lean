import InitECandidate.Solver.GuestBound.TrieDelStack
import InitECandidate.Solver.GuestBound.TrieFreeze

/-!
# The hashing walk `_node_rlp_fill`: stack invariant, measure, interfaces

`_node_rlp_fill(node)` walks the trie below `node` with an explicit stack of
48-byte frames in the scratch arena (`+0` parent frame, `+8` node, `+16`
cursor, `+24 … +40` data of `_node_rlp_begin`).  A node is pushed only when its
RLP cache (`+8`) is empty; popping a node fills that cache.

* `RStk`: the frames from `top` down to the first one, the nodes they hold
  (pairwise distinct, because levels increase strictly along the stack), each
  with an empty cache.
* `Uset`: the registered nodes with an empty cache.  The loop measure is
  `(Uset R m).ncard + scratch_ptr`: a pop removes the popped node from `Uset`,
  a push lowers the scratch pointer (nothing is released before the end).
* `WalkIface`: what the loop needs of `_node_rlp_begin`, `_node_rlp_finish`
  and `_node_needs_rlp`.  `FrOK` is the (abstract) fact that a frame's data
  are what `_node_rlp_finish` expects; `stable` says which memory changes it
  survives.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- A cache cell (`+8`, `+16`, `+24`) of a registered node that is not a hash stub. -/
def CacheC (R : Reg) (a : Word) : Prop :=
  ∃ x k, R.Kd x k ∧ k ≠ 0#64 ∧ (a = x + 8#64 ∨ a = x + 16#64 ∨ a = x + 24#64)

/-- The registered nodes with an empty RLP cache. -/
def Uset (R : Reg) (m : Word → Option (PanValue Word)) : Set Word :=
  {x | (∃ k, R.Kd x k ∧ k ≠ 0#64) ∧ Rd m (x + 8#64) 0#64}

theorem ncard_word_le (s : Set Word) : s.ncard ≤ 2 ^ 64 := by
  have h := Set.ncard_image_of_injOn (s := s) (f := BitVec.toNat)
    (fun a _ b _ h => BitVec.eq_of_toNat_eq h)
  rw [← h]
  have hsub : BitVec.toNat '' s ⊆ ((Finset.range (2 ^ 64) : Finset Nat) : Set Nat) := by
    rintro _ ⟨x, -, rfl⟩
    simpa using x.isLt
  have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, Finset.card_range] at this
  exact this

/-- Unchanged caches: the same set. -/
theorem Uset.same {R : Reg} {m m' : Word → Option (PanValue Word)}
    (h : ∀ x k, R.Kd x k → m' (x + 8#64) = m (x + 8#64)) : Uset R m' = Uset R m := by
  ext x
  constructor
  · rintro ⟨⟨k, hk, hk0⟩, hr⟩
    refine ⟨⟨k, hk, hk0⟩, ?_⟩
    unfold Rd at hr ⊢
    rw [← h x k hk]
    exact hr
  · rintro ⟨⟨k, hk, hk0⟩, hr⟩
    refine ⟨⟨k, hk, hk0⟩, ?_⟩
    unfold Rd at hr ⊢
    rw [h x k hk]
    exact hr

/-- Filling the cache of one node: a strictly smaller set. -/
theorem Uset.pop {R : Reg} {m m' : Word → Option (PanValue Word)} {nd k buf : Word}
    (hk : R.Kd nd k) (hk0 : k ≠ 0#64) (h0 : Rd m (nd + 8#64) 0#64)
    (hb : Rd m' (nd + 8#64) buf) (hb0 : buf ≠ 0#64)
    (h : ∀ x k', R.Kd x k' → x ≠ nd → m' (x + 8#64) = m (x + 8#64)) :
    (Uset R m').ncard < (Uset R m).ncard := by
  refine Set.ncard_lt_ncard ⟨?_, ?_⟩ (Set.toFinite _)
  · rintro x ⟨⟨k', hk', hk0'⟩, hr⟩
    have hne : x ≠ nd := by
      rintro rfl
      exact hb0 (Rd.inj hb hr)
    refine ⟨⟨k', hk', hk0'⟩, ?_⟩
    unfold Rd at hr ⊢
    rw [← h x k' hk' hne]
    exact hr
  · intro hsub
    have := hsub ⟨⟨k, hk, hk0⟩, h0⟩
    exact hb0 (Rd.inj hb this.2)

/-- The frames of the hashing walk, newest first, and the nodes they hold.
`F fr nd` is the readiness of frame `fr` for node `nd`. -/
inductive RStk (R : Reg) (F : Word → Word → Prop) (m : Word → Option (PanValue Word))
    (lim : Nat) : Nat → Word → List Word → Prop
  | nil {sp : Nat} : RStk R F m lim sp 0#64 []
  | cons {sp : Nat} {top prev nd cur k : Word} {ℓ : Nat} {S : List Word} :
      top ≠ 0#64 → top.toNat % 8 = 0 → sp ≤ top.toNat → top.toNat + 48 ≤ lim →
      Rd m top prev → Rd m (top + 8#64) nd → Rd m (top + 16#64) cur →
      R.Kd nd k → k ≠ 0#64 → R.Lv nd ℓ → Rd m (nd + 8#64) 0#64 → F top nd →
      (∀ x ∈ S, ∃ ℓ' k', R.Lv x ℓ' ∧ ℓ' < ℓ ∧ R.Kd x k') →
      RStk R F m lim (top.toNat + 48) prev S → RStk R F m lim sp top (nd :: S)

theorem RStk.lower {R : Reg} {F : Word → Word → Prop} {m : Word → Option (PanValue Word)}
    {lim sp sp' : Nat} {top : Word} {S : List Word} (hsp : sp' ≤ sp)
    (h : RStk R F m lim sp top S) : RStk R F m lim sp' top S := by
  cases h with
  | nil => exact .nil
  | cons h1 h2 h3 h4 r0 r1 r2 hk hk0 hl hc hF hS ht =>
    exact .cons h1 h2 (by omega) h4 r0 r1 r2 hk hk0 hl hc hF hS ht

/-- The stack survives a change that leaves its frames' cells and its nodes'
caches alone, and under which readiness is kept. -/
theorem RStk.step {R : Reg} {F F' : Word → Word → Prop} {m m' : Word → Option (PanValue Word)}
    {lim sp : Nat} {top : Word} {S : List Word} (hlim : lim < 2 ^ 64)
    (hm : ∀ x : Word, sp ≤ x.toNat → x.toNat < lim → m' x = m x)
    (hc : ∀ x ∈ S, m' (x + 8#64) = m (x + 8#64))
    (hF : ∀ fr nd, sp ≤ fr.toNat → fr.toNat + 48 ≤ lim → F fr nd → F' fr nd)
    (h : RStk R F m lim sp top S) : RStk R F' m' lim sp top S := by
  induction h with
  | nil => exact .nil
  | @cons sp top prev nd cur k ℓ S h1 h2 h3 h4 r0 r1 r2 hk hk0 hl hcz hFt hS _ ih =>
    have e8 : (top + 8#64).toNat = top.toNat + 8 := by bv_omega
    have e16 : (top + 16#64).toNat = top.toNat + 16 := by bv_omega
    refine .cons (cur := cur) h1 h2 h3 h4 ?_ ?_ ?_ hk hk0 hl ?_ (hF top nd h3 h4 hFt) hS
      (ih (fun x hx hx' => hm x (by omega) hx') (fun x hx => hc x (List.mem_cons_of_mem _ hx))
        (fun fr nd' hfr hfr' hf => hF fr nd' (by omega) hfr' hf))
    · unfold Rd at r0 ⊢
      rw [hm top h3 (by omega)]
      exact r0
    · unfold Rd at r1 ⊢
      rw [hm _ (by omega) (by omega)]
      exact r1
    · unfold Rd at r2 ⊢
      rw [hm _ (by omega) (by omega)]
      exact r2
    · unfold Rd at hcz ⊢
      rw [hc nd (List.mem_cons_self ..)]
      exact hcz

/-- What may change around a frame `fr` while it waits: below the heap pointer
`pv` only cache cells and the cells `K`; the frame's own data not at all. -/
def WCh (R : Reg) (K : Word → Prop) (pv fr : Word) (m m' : Word → Option (PanValue Word)) :
    Prop :=
  (∀ a : Word, a.toNat < pv.toNat → ¬ CacheC R a → ¬ K a → m' a = m a) ∧
  ∀ a : Word, fr.toNat + 24 ≤ a.toNat → a.toNat < fr.toNat + 48 → m' a = m a

/-- What the loop of `_node_rlp_fill` needs of the three functions it calls. -/
structure WalkIface (E : Env σ) where
  /-- Cells below the heap pointer, other than cache cells, that hashing may write
  (the Keccak buffers). -/
  K : Word → Prop
  /-- What hashing needs of the registry and the globals. -/
  Pre : Reg → (VarName → Option (PanValue Word)) → Prop
  /-- Frame `fr` holds the data `_node_rlp_finish` expects for node `nd`;
  the second argument is the heap pointer. -/
  FrOK : Reg → Word → (Word → Option (PanValue Word)) → Word → Word → Prop
  pre_glob : ∀ {R : Reg} {g g' : VarName → Option (PanValue Word)}, Pre R g →
    (∀ x, x ≠ "heap_ptr" → x ≠ "scratch_ptr" → g' x = g x) → Pre R g'
  stable : ∀ {R : Reg} {pv pv' fr nd : Word} {m m' : Word → Option (PanValue Word)},
    FrOK R pv m fr nd → pv.toNat ≤ pv'.toNat → WCh R K pv fr m m' → FrOK R pv' m' fr nd
  begin : ∀ (R : Reg) (s : St σ) (e1 e2 : Exp Word) (fr nd k pv : Word)
    (vs : List (PanValue Word)) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (ffi : FfiState σ),
    CalleeRet E s "_node_rlp_begin" [e1, e2] vs g m ffi →
    E.eval s e1 = some (.word fr) → E.eval s e2 = some (.word nd) →
    WorldTJ R s.globals s.memory → Pre R s.globals →
    s.globals "heap_ptr" = some (.word pv) → R.Kd nd k → k ≠ 0#64 →
    2952790016 ≤ fr.toNat → fr.toNat % 8 = 0 → fr.toNat + 48 < 2 ^ 64 →
    ffi = s.ffi ∧ ∃ pv' : Word, g "heap_ptr" = some (.word pv') ∧ pv.toNat ≤ pv'.toNat ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧ WorldTJ R g m ∧ FrOK R pv' m fr nd ∧
      (∀ a : Word, a.toNat < pv.toNat → m a = s.memory a) ∧
      ∀ a : Word, 2952790016 ≤ a.toNat →
        ¬ (fr.toNat + 24 ≤ a.toNat ∧ a.toNat < fr.toNat + 48) → m a = s.memory a
  finish : ∀ (R : Reg) (s : St σ) (e1 e2 : Exp Word) (fr nd k pv : Word)
    (vs : List (PanValue Word)) (g : VarName → Option (PanValue Word))
    (m : Word → Option (PanValue Word)) (ffi : FfiState σ),
    CalleeRet E s "_node_rlp_finish" [e1, e2] vs g m ffi →
    E.eval s e1 = some (.word fr) → E.eval s e2 = some (.word nd) →
    WorldTJ R s.globals s.memory → Pre R s.globals →
    s.globals "heap_ptr" = some (.word pv) → R.Kd nd k → k ≠ 0#64 →
    FrOK R pv s.memory fr nd →
    ffi = s.ffi ∧ ∃ pv' : Word, g "heap_ptr" = some (.word pv') ∧ pv.toNat ≤ pv'.toNat ∧
      (∀ x, x ≠ "heap_ptr" → g x = s.globals x) ∧ WorldTJ R g m ∧
      (∃ buf off, Rd m (nd + 8#64) buf ∧ buf ≠ 0#64 ∧ Rd m (nd + 16#64) off ∧
        off.toNat < 2 ^ 32) ∧
      (∀ a : Word, a.toNat < pv.toNat → ¬ CacheC R a → ¬ K a → m a = s.memory a) ∧
      (∀ x k', R.Kd x k' → x ≠ nd → m (x + 8#64) = s.memory (x + 8#64)) ∧
      ∀ a : Word, 2952790016 ≤ a.toNat → m a = s.memory a
  needs : ∀ (s : St σ) (e : Exp Word) (c : Word) (v : PanValue Word)
    (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (ffi : FfiState σ),
    CalleeRet E s "_node_needs_rlp" [e] [v] g m ffi → E.eval s e = some (.word c) →
    g = s.globals ∧ m = s.memory ∧ ffi = s.ffi ∧ ∃ f : Word, v = .word f ∧
      (f ≠ 0#64 → c ≠ 0#64 ∧ ∃ kk, Rd s.memory c kk ∧ kk ≠ 0#64 ∧ Rd s.memory (c + 8#64) 0#64)

/-- The scratch pointer as a number. -/
def spOf (g : VarName → Option (PanValue Word)) : Nat :=
  match g "scratch_ptr" with
  | some (.word w) => w.toNat
  | _ => 0

/-- The measure of the walk: empty caches plus the scratch pointer. -/
noncomputable def wkMu (R : Reg) (a : St σ) : Nat :=
  (Uset R a.memory).ncard + spOf a.globals

theorem wkMu_le (R : Reg) (a : St σ) : wkMu R a ≤ 2 ^ 65 := by
  unfold wkMu spOf
  have h1 := ncard_word_le (Uset R a.memory)
  split
  · rename_i w _
    have := w.isLt
    omega
  · omega

end InitECandidate.Solver.GuestBound
