import InitECandidate.Solver.GuestBound.RlpSlices

/-!
# Assertions about a part of the state, with the frame rule built in

A `Heap` is a partial map from memory cells and global variables to values.
An `Assn` is a predicate on heaps; `P ⋆ Q` holds of a heap that splits into
disjoint parts satisfying `P` and `Q`. `P.holds s` says that some heap
satisfying `P` is contained in the memory and globals of `s`.

`WPF E s p P Q`: for every frame `R`, if `P ⋆ R` holds of `s` then every run
of `p` from `s` stops or ends in a result `r` whose state satisfies `Q r ⋆ R`.
Since `R` is arbitrary, `P` and `Q` mention only what `p` reads and writes,
and `WPF.frame` adds any untouched assertion to both sides. The shape follows
`cpsTripleWithin` of Verified-zkEVM/riscv-zkvm (`Rv64/Logic/CPSSpec.lean`).

Locals and the FFI state are not resources: `Q` takes the whole result, and
facts about them are stated with `⌜·⌝`.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

/-- What an assertion can own: a memory cell or a global variable. -/
inductive Key where
  | mem (a : Word)
  | glob (x : VarName)
  deriving DecidableEq

/-- The memory and globals of a state. -/
abbrev View := Key → Option (PanValue Word)

/-- An owned part of a view: each owned key with its content (possibly undefined). -/
abbrev Heap := Key → Option (Option (PanValue Word))

namespace Heap

def Disj (h1 h2 : Heap) : Prop := ∀ k, h1 k = none ∨ h2 k = none

def union (h1 h2 : Heap) : Heap := fun k =>
  match h1 k with
  | some v => some v
  | none => h2 k

def Sub (h : Heap) (V : View) : Prop := ∀ k c, h k = some c → V k = c

def empty : Heap := fun _ => none

def single (k : Key) (v : Option (PanValue Word)) : Heap := fun k' => if k' = k then some v else none

theorem Disj.symm {h1 h2 : Heap} (h : Disj h1 h2) : Disj h2 h1 := fun k => (h k).symm

theorem union_comm {h1 h2 : Heap} (h : Disj h1 h2) : union h1 h2 = union h2 h1 := by
  funext k
  unfold union
  rcases h k with e | e
  · rw [e]; cases h2 k <;> rfl
  · rw [e]; cases h1 k <;> rfl

theorem union_assoc (h1 h2 h3 : Heap) : union (union h1 h2) h3 = union h1 (union h2 h3) := by
  funext k
  unfold union
  cases h1 k <;> rfl

theorem empty_union (h : Heap) : union empty h = h := rfl

theorem disj_empty (h : Heap) : Disj empty h := fun _ => Or.inl rfl

theorem union_none {h1 h2 : Heap} {k : Key} :
    union h1 h2 k = none ↔ h1 k = none ∧ h2 k = none := by
  unfold union
  cases h1 k <;> simp

theorem disj_union_left {a b c : Heap} : Disj (union a b) c ↔ Disj a c ∧ Disj b c := by
  constructor
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩
    · rcases h k with e | e
      · exact Or.inl (union_none.mp e).1
      · exact Or.inr e
    · rcases h k with e | e
      · exact Or.inl (union_none.mp e).2
      · exact Or.inr e
  · rintro ⟨h1, h2⟩ k
    rcases h1 k with e1 | e1
    · rcases h2 k with e2 | e2
      · exact Or.inl (union_none.mpr ⟨e1, e2⟩)
      · exact Or.inr e2
    · exact Or.inr e1

theorem disj_union_right {a b c : Heap} : Disj a (union b c) ↔ Disj a b ∧ Disj a c := by
  constructor
  · intro h
    have := disj_union_left.mp h.symm
    exact ⟨this.1.symm, this.2.symm⟩
  · rintro ⟨h1, h2⟩
    exact (disj_union_left.mpr ⟨h1.symm, h2.symm⟩).symm

theorem sub_union {a b : Heap} {V : View} (hd : Disj a b) : Sub (union a b) V ↔ Sub a V ∧ Sub b V := by
  constructor
  · intro h
    refine ⟨fun k v hk => h k v ?_, fun k v hk => h k v ?_⟩
    · unfold union; rw [hk]
    · rcases hd k with e | e
      · unfold union; rw [e]; exact hk
      · rw [e] at hk; cases hk
  · rintro ⟨h1, h2⟩ k v hk
    unfold union at hk
    cases e : a k with
    | some x => rw [e] at hk; exact h1 k v (e.trans hk)
    | none => rw [e] at hk; exact h2 k v hk

theorem single_self (k : Key) (v : Option (PanValue Word)) : single k v k = some v := by
  simp [single]

theorem single_ne {k k' : Key} (v : Option (PanValue Word)) (h : k' ≠ k) : single k v k' = none := by
  simp [single, h]

end Heap

abbrev Assn := Heap → Prop

namespace Assn

/-- Separating conjunction: the heap splits into disjoint parts for `P` and `Q`. -/
def sep (P Q : Assn) : Assn := fun h =>
  ∃ h1 h2, Heap.Disj h1 h2 ∧ h = Heap.union h1 h2 ∧ P h1 ∧ Q h2

def emp : Assn := fun h => h = Heap.empty

/-- A fact that owns nothing. -/
def pure (φ : Prop) : Assn := fun h => φ ∧ h = Heap.empty

/-- The key `k` is owned, with content `c` (`none`: undefined). -/
def cell (k : Key) (c : Option (PanValue Word)) : Assn := fun h => h = Heap.single k c

/-- The cell or global `k` holds `v`. -/
def pts (k : Key) (v : PanValue Word) : Assn := cell k (some v)

def ex {α : Sort _} (P : α → Assn) : Assn := fun h => ∃ x, P x h

/-- Some heap satisfying `P` is contained in `V`. -/
def holdsV (P : Assn) (V : View) : Prop := ∃ h, Heap.Sub h V ∧ P h

end Assn

@[inherit_doc] infixr:35 " ⋆ " => Assn.sep
@[inherit_doc] notation "⌜" φ "⌝" => Assn.pure φ
@[inherit_doc] infix:50 " ↦ " => Assn.pts

namespace Assn

theorem sep_comm (P Q : Assn) : (P ⋆ Q) = (Q ⋆ P) := by
  funext h
  apply propext
  constructor <;>
  · rintro ⟨h1, h2, hd, rfl, hp, hq⟩
    exact ⟨h2, h1, hd.symm, Heap.union_comm hd, hq, hp⟩

theorem sep_assoc (P Q R : Assn) : ((P ⋆ Q) ⋆ R) = (P ⋆ Q ⋆ R) := by
  funext h
  apply propext
  constructor
  · rintro ⟨h12, h3, hd, rfl, ⟨h1, h2, hd12, rfl, hp, hq⟩, hr⟩
    obtain ⟨hd13, hd23⟩ := Heap.disj_union_left.mp hd
    exact ⟨h1, Heap.union h2 h3, Heap.disj_union_right.mpr ⟨hd12, hd13⟩,
      Heap.union_assoc h1 h2 h3, hp, h2, h3, hd23, rfl, hq, hr⟩
  · rintro ⟨h1, h23, hd, rfl, hp, h2, h3, hd23, rfl, hq, hr⟩
    obtain ⟨hd12, hd13⟩ := Heap.disj_union_right.mp hd
    exact ⟨Heap.union h1 h2, h3, Heap.disj_union_left.mpr ⟨hd13, hd23⟩,
      (Heap.union_assoc h1 h2 h3).symm, ⟨h1, h2, hd12, rfl, hp, hq⟩, hr⟩

theorem sep_mono {P P' Q Q' : Assn} (hp : ∀ h, P h → P' h) (hq : ∀ h, Q h → Q' h) :
    ∀ h, (P ⋆ Q) h → (P' ⋆ Q') h := by
  rintro h ⟨h1, h2, hd, rfl, h1p, h2q⟩
  exact ⟨h1, h2, hd, rfl, hp h1 h1p, hq h2 h2q⟩

theorem holdsV_mono {P P' : Assn} {V : View} (hp : ∀ h, P h → P' h) (h : P.holdsV V) :
    P'.holdsV V := by
  obtain ⟨h0, hs, h0p⟩ := h
  exact ⟨h0, hs, hp h0 h0p⟩

/-- A pure fact in front of an assertion. -/
theorem holdsV_pure {φ : Prop} {P : Assn} {V : View} : (⌜φ⌝ ⋆ P).holdsV V ↔ φ ∧ P.holdsV V := by
  constructor
  · rintro ⟨h, hs, h1, h2, -, rfl, ⟨hφ, rfl⟩, hp⟩
    exact ⟨hφ, h2, hs, hp⟩
  · rintro ⟨hφ, h, hs, hp⟩
    exact ⟨h, hs, Heap.empty, h, Heap.disj_empty h, rfl, ⟨hφ, rfl⟩, hp⟩

theorem holdsV_ex {α : Sort _} {P : α → Assn} {R : Assn} {V : View} :
    (ex P ⋆ R).holdsV V ↔ ∃ x, (P x ⋆ R).holdsV V := by
  constructor
  · rintro ⟨h, hs, h1, h2, hd, rfl, ⟨x, hx⟩, hr⟩
    exact ⟨x, _, hs, h1, h2, hd, rfl, hx, hr⟩
  · rintro ⟨x, h, hs, h1, h2, hd, rfl, hx, hr⟩
    exact ⟨_, hs, h1, h2, hd, rfl, ⟨x, hx⟩, hr⟩

/-- An owned key has its value in the state. -/
theorem holdsV_pts {k : Key} {v : PanValue Word} {R : Assn} {V : View}
    (h : (k ↦ v ⋆ R).holdsV V) : V k = some v := by
  obtain ⟨h0, hs, h1, h2, hd, rfl, rfl, -⟩ := h
  exact hs k (some v) (by unfold Heap.union; rw [Heap.single_self])

/-- Changing an owned key keeps the frame. -/
theorem holdsV_update {k : Key} {c : Option (PanValue Word)} {w : PanValue Word} {R : Assn}
    {V V' : View} (h : (Assn.cell k c ⋆ R).holdsV V) (hk : V' k = some w) (ho : ∀ k', k' ≠ k → V' k' = V k') :
    (k ↦ w ⋆ R).holdsV V' := by
  obtain ⟨h0, hs, h1, h2, hd, rfl, rfl, hr⟩ := h
  have h2k : h2 k = none := by
    rcases hd k with e | e
    · rw [Heap.single_self] at e; cases e
    · exact e
  have hd' : Heap.Disj (Heap.single k (some w)) h2 := by
    intro k'
    by_cases e : k' = k
    · subst e; exact Or.inr h2k
    · exact Or.inl (Heap.single_ne (some w) e)
  obtain ⟨-, hs2⟩ := (Heap.sub_union hd).mp hs
  refine ⟨_, (Heap.sub_union hd').mpr ⟨?_, ?_⟩, _, h2, hd', rfl, rfl, hr⟩
  · intro k' x hx
    by_cases e : k' = k
    · subst e; rw [Heap.single_self] at hx; cases hx; exact hk
    · rw [Heap.single_ne (some w) e] at hx; cases hx
  · intro k' x hx
    have e : k' ≠ k := by
      rintro rfl
      rw [h2k] at hx; cases hx
    rw [ho k' e]
    exact hs2 k' x hx

end Assn

variable {σ : Type}

/-- The memory and globals of a state as one heap. -/
def St.view (s : St σ) : View
  | .mem a => s.memory a
  | .glob x => s.globals x

/-- `P` holds of a part of the memory and globals of `s`. -/
def Assn.holds (P : Assn) (s : St σ) : Prop := P.holdsV s.view

theorem Assn.holds_congr {P : Assn} {s s' : St σ} (hg : s'.globals = s.globals)
    (hm : s'.memory = s.memory) (h : P.holds s) : P.holds s' := by
  have : s'.view = s.view := by
    funext k
    cases k <;> simp [St.view, hg, hm]
  unfold Assn.holds
  rw [this]
  exact h

theorem Assn.holds_mem {a : Word} {v : PanValue Word} {R : Assn} {s : St σ}
    (h : (.mem a ↦ v ⋆ R).holds s) : s.memory a = some v :=
  Assn.holdsV_pts h

theorem Assn.holds_glob {x : VarName} {v : PanValue Word} {R : Assn} {s : St σ}
    (h : (.glob x ↦ v ⋆ R).holds s) : s.globals x = some v :=
  Assn.holdsV_pts h

/-- A word store into an owned cell. -/
theorem Assn.holds_setCell {a : Word} {v : PanValue Word} {w : Word} {R : Assn} {s : St σ}
    {l : VarName → Option (PanValue Word)} {f : FfiState σ} (h : (.mem a ↦ v ⋆ R).holds s) :
    (.mem a ↦ .word w ⋆ R).holds (⟨l, s.globals, setCell s.memory a w, f⟩ : St σ) := by
  refine Assn.holdsV_update h ?_ ?_
  · simp [St.view, setCell]
  · intro k' hk'
    cases k' with
    | glob x => rfl
    | mem b =>
      have : b ≠ a := fun e => hk' (by rw [e])
      simp [St.view, setCell, this]

/-- An assignment to an owned global. -/
theorem Assn.holds_setGlobal {x : VarName} {v w : PanValue Word} {R : Assn} {s : St σ}
    {l : VarName → Option (PanValue Word)} {f : FfiState σ} (h : (.glob x ↦ v ⋆ R).holds s) :
    (.glob x ↦ w ⋆ R).holds (⟨l, updatePanValueMap s.globals x w, s.memory, f⟩ : St σ) := by
  refine Assn.holdsV_update h ?_ ?_
  · simp [St.view, updatePanValueMap]
  · intro k' hk'
    cases k' with
    | mem b => rfl
    | glob y =>
      have : y ≠ x := fun e => hk' (by rw [e])
      simp [St.view, updatePanValueMap, this]

variable {E : Env σ} {s : St σ}

/-- Every run of `p` from `s` stops or ends in `Q`, where `P` and `Q` describe
only the part of the memory and globals that `p` uses. -/
def WPF (E : Env σ) (s : St σ) (p : Prog Word) (P : Assn) (Q : Result σ → Assn) : Prop :=
  ∀ R : Assn, (P ⋆ R).holds s → WPs E s p (fun r => (Q r ⋆ R).holds r.st)

/-- The frame rule. -/
theorem WPF.frame {p : Prog Word} {P : Assn} {Q : Result σ → Assn} (F : Assn)
    (h : WPF E s p P Q) : WPF E s p (P ⋆ F) (fun r => Q r ⋆ F) := by
  intro R hR
  rw [Assn.sep_assoc] at hR
  refine WPs.conseq (h (F ⋆ R) hR) (fun r hr => ?_)
  rw [Assn.sep_assoc]
  exact hr

theorem WPF.conseq {p : Prog Word} {P P' : Assn} {Q Q' : Result σ → Assn}
    (h : WPF E s p P Q) (hp : ∀ h, P' h → P h) (hq : ∀ r h, Q r h → Q' r h) :
    WPF E s p P' Q' := by
  intro R hR
  refine WPs.conseq (h R (Assn.holdsV_mono (Assn.sep_mono hp (fun _ h => h)) hR)) (fun r hr => ?_)
  exact Assn.holdsV_mono (Assn.sep_mono (hq r) (fun _ h => h)) hr

/-- A pure fact in the precondition may be assumed. -/
theorem WPF.pure {p : Prog Word} {φ : Prop} {P : Assn} {Q : Result σ → Assn}
    (h : φ → WPF E s p P Q) : WPF E s p (⌜φ⌝ ⋆ P) Q := by
  intro R hR
  rw [Assn.sep_assoc] at hR
  obtain ⟨hφ, hP⟩ := Assn.holdsV_pure.mp hR
  exact h hφ R hP

/-- An existential in the precondition may be opened. -/
theorem WPF.ex {α : Sort _} {p : Prog Word} {P : α → Assn} {Q : Result σ → Assn}
    (h : ∀ x, WPF E s p (P x) Q) : WPF E s p (Assn.ex P) Q := by
  intro R hR
  obtain ⟨x, hx⟩ := Assn.holdsV_ex.mp hR
  exact h x R hx

/-- From a `WPF` back to a statement about whole states. -/
theorem WPF.wps {p : Prog Word} {P : Assn} {Q : Result σ → Assn} (h : WPF E s p P Q)
    (R : Assn) (hR : (P ⋆ R).holds s) : WPs E s p (fun r => (Q r ⋆ R).holds r.st) :=
  h R hR

/-- Sequencing: the intermediate assertion may depend on the state reached. -/
theorem WPF.seq {p q : Prog Word} {P : Assn} {Q : Result σ → Assn} (M : St σ → Assn)
    (hp : WPF E s p P (fun r => match r with
      | .normal l g m f => M ⟨l, g, m, f⟩
      | r => Q r))
    (hq : ∀ s', WPF E s' q (M s') Q) : WPF E s (.seq p q) P Q := by
  intro R hR
  refine WPs.seqG (fun s' => (M s' ⋆ R).holds s') (WPs.conseq (hp R hR) (fun r hr => ?_))
    (fun s' hs' => hq s' R hs')
  cases r <;> exact hr

/-- A word store into an owned cell. The locals and the FFI state are kept. -/
theorem WPF.store (hE : GuestEnv E) {a val : Exp Word} {addr w : Word} {old : PanValue Word}
    (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hv : ∀ y, E.eval s val = some y → y = .word w) :
    WPF E s (.store a val) (.mem addr ↦ old)
      (fun r => ⌜∃ g m, r = .normal s.locals g m s.ffi⌝ ⋆ .mem addr ↦ .word w) := by
  intro R hR r hr
  obtain ⟨fuel, n, hrun⟩ := hr
  rcases store_word_inv' hE.mem hrun with herr | ⟨addr', y, m, ha', hy, rfl, hm⟩
  · exact Or.inl (Stopped.of_error herr)
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  have := hv y hy
  subst this
  obtain ⟨rfl, -⟩ := hm w rfl
  refine Or.inr ?_
  show ((⌜_⌝ ⋆ _) ⋆ R).holds _
  rw [Assn.sep_assoc]
  exact Assn.holdsV_pure.mpr ⟨⟨_, _, rfl⟩, Assn.holds_setCell hR⟩

/-- A word load from an owned cell has the owned value. -/
theorem eval_load_owned (hE : GuestEnv E) {a : Exp Word} {addr : Word} {v : PanValue Word}
    {R : Assn} (ha : ∀ y, E.eval s a = some y → y = .word addr)
    (hR : (.mem addr ↦ v ⋆ R).holds s) :
    ∀ y, E.eval s (.load .one a) = some y → y = v := by
  intro y hy
  obtain ⟨addr', w', ha', rfl, hm⟩ := eval_load_one hE.mem hy
  have := ha _ ha'
  simp only [PanValue.word.injEq] at this
  subst this
  have hv := Assn.holds_mem hR
  rw [hm] at hv
  exact Option.some.inj hv

end InitECandidate.Solver.GuestBound
