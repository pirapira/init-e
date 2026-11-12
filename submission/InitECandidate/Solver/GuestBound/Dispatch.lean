import InitECandidate.Solver.GuestBound.SepFrameOps

/-!
# The dispatcher as a decision tree

`op_dispatch` is a tree of tests on the opcode whose leaves are
`op_X(args); return 0`, ending in `raise EvmErr`. `tree_sound` reduces a
property of the whole tree to the same property of each leaf. It is generic in
the precondition `P` and the postcondition `Q`, so it will also serve the
final machine invariant.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-- The callee of a leaf `f(args); return 0`. -/
def leafFn : Prog Word → Prog Word → Option FunName
  | .call (some (none, none)) f _, .return (.const k) => if k = 0#64 then some f else none
  | _, _ => none

/-- `raise EvmErr k; return _`. -/
def raiseLeaf : Prog Word → Prog Word → Bool
  | .raise e (.const _), .return _ => e == "EvmErr"
  | _, _ => false

/-- A tree of tests whose leaves call functions accepted by `ok`. -/
def dispTree (ok : FunName → Bool) : Prog Word → Bool
  | .skip => true
  | .raise e (.const _) => e == "EvmErr"
  | .ite _ a b => dispTree ok a && dispTree ok b
  | .seq a b =>
      (match leafFn a b with
        | some f => ok f
        | none => false) || raiseLeaf a b || (dispTree ok a && dispTree ok b)
  | _ => false

theorem leafFn_eq {a b : Prog Word} {f : FunName} (h : leafFn a b = some f) :
    ∃ args, a = .call (some (none, none)) f args ∧ b = .return (.const 0#64) := by
  unfold leafFn at h
  split at h
  · rename_i f' args k
    split at h
    · rename_i hk
      cases h
      exact ⟨args, rfl, by rw [hk]⟩
    · cases h
  · cases h

theorem raiseLeaf_eq {a b : Prog Word} (h : raiseLeaf a b = true) :
    ∃ k e, a = .raise "EvmErr" (.const k) ∧ b = .return e := by
  unfold raiseLeaf at h
  split at h
  · rename_i e' k e
    have : e' = "EvmErr" := by simpa using h
    exact ⟨k, e, by rw [this], rfl⟩
  · cases h

/-- Every run of a tree falls through with the state unchanged, or satisfies
`Q`, provided each leaf does and `Q` holds of the final `raise`. -/
theorem tree_sound {ok : FunName → Bool} {P : St σ → Prop} {Q : Result σ → Prop}
    (hleaf : ∀ f args, ok f = true → ∀ s, P s →
      WPr E s (.seq (.call (some (none, none)) f args) (.return (.const 0#64))) Q)
    (hraise : ∀ (s : St σ) k, P s →
      Q (.raised (fun _ => none) s.globals s.memory s.ffi "EvmErr" (.word k)))
    (hnormal : ∀ l g m f, ¬ Q (.normal l g m f)) :
    ∀ (p : Prog Word), dispTree ok p = true → ∀ s : St σ, P s →
      WPr E s p (fun r => match r with
        | .normal l g m f => (⟨l, g, m, f⟩ : St σ) = s
        | r => Q r)
  | .skip, _, s, _ => WPr.skip rfl
  | .raise e (.const k), hp, s, hs => by
      have he : e = "EvmErr" := by simpa [dispTree] using hp
      subst he
      refine WPr.raise (fun v hv => ?_)
      rw [eval_const] at hv
      cases hv
      exact hraise s k hs
  | .raise _ (.var _ _), hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.rStruct _), hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.rField _ _), hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.load _ _), hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.loadByte _), hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.op _ _), hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.panOp _ _), hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.cmp _ _ _), hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.shift _ _ _), hp, _, _ => by simp [dispTree] at hp
  | .ite _ a b, hp, s, hs => by
      simp only [dispTree, Bool.and_eq_true] at hp
      refine WPr.ite_both (fun w _ => ?_)
      split
      · exact tree_sound hleaf hraise hnormal b hp.2 s hs
      · exact tree_sound hleaf hraise hnormal a hp.1 s hs
  | .seq a b, hp, s, hs => by
      simp only [dispTree, Bool.or_eq_true, Bool.and_eq_true] at hp
      rcases hp with (hl | hr) | ⟨ha, hb⟩
      · cases hf : leafFn a b with
        | none => rw [hf] at hl; cases hl
        | some f =>
          rw [hf] at hl
          obtain ⟨args, rfl, rfl⟩ := leafFn_eq hf
          refine WPr.conseq (hleaf f args hl s hs) (fun r hr => ?_)
          cases r with
          | normal l g m f' => exact absurd hr (hnormal l g m f')
          | _ => exact hr
      · obtain ⟨k, e, rfl, rfl⟩ := raiseLeaf_eq hr
        refine WPr.seq (fun _ => False) (WPr.raise (fun v hv => ?_)) (fun _ h => h.elim)
        rw [eval_const] at hv
        cases hv
        exact hraise s k hs
      · refine WPr.seq (fun s' => s' = s)
          (WPr.conseq (tree_sound hleaf hraise hnormal a ha s hs) (fun r hr => ?_))
          (fun s' hs' => by rw [hs']; exact tree_sound hleaf hraise hnormal b hb s hs)
        cases r <;> exact hr
  | .dec _ _ _ _, hp, _, _ => by simp [dispTree] at hp
  | .assign _ _ _, hp, _, _ => by simp [dispTree] at hp
  | .primitive _ _ _, hp, _, _ => by simp [dispTree] at hp
  | .store _ _, hp, _, _ => by simp [dispTree] at hp
  | .store32 _ _, hp, _, _ => by simp [dispTree] at hp
  | .storeByte _ _, hp, _, _ => by simp [dispTree] at hp
  | .while _ _, hp, _, _ => by simp [dispTree] at hp
  | .break, hp, _, _ => by simp [dispTree] at hp
  | .continue, hp, _, _ => by simp [dispTree] at hp
  | .call _ _ _, hp, _, _ => by simp [dispTree] at hp
  | .decCall _ _ _ _ _, hp, _, _ => by simp [dispTree] at hp
  | .extCall _ _ _ _ _, hp, _, _ => by simp [dispTree] at hp
  | .raise _ .baseAddr, hp, _, _ => by simp [dispTree] at hp
  | .raise _ .topAddr, hp, _, _ => by simp [dispTree] at hp
  | .raise _ .bytesInWord, hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.nField _ _), hp, _, _ => by simp [dispTree] at hp
  | .raise _ (.load32 _), hp, _, _ => by simp [dispTree] at hp
  | .return _, hp, _, _ => by simp [dispTree] at hp
  | .shMemLoad _ _ _ _, hp, _, _ => by simp [dispTree] at hp
  | .shMemStore _ _ _, hp, _, _ => by simp [dispTree] at hp
  | .tick, hp, _, _ => by simp [dispTree] at hp
  | .annot _ _, hp, _, _ => by simp [dispTree] at hp

/-- A handler, as its theorem in `SepFrameOps.lean` states it. -/
def HandlerSpec (E : Env σ) (f : FunName) : Prop :=
  ∀ parameters body, lookupPanFunction f E.functions = some (parameters, body) →
    ∀ (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt),
      FrameOk M K fv X0 → (FrameOp M K e fv X0 ⋆ R).holds s →
      WPr E s body (HandlerQ M K e fv R s.ffi X0)

/-- A leaf of the dispatcher, from the handler's theorem. -/
theorem handler_leaf {f : FunName} (hf : HandlerSpec E f) (args : List (Exp Word))
    (s : St σ) (M : Word) (K : Word → Prop) (e fv : Word) (R : Assn) (X0 : OpSt)
    (hok : FrameOk M K fv X0) (h : (FrameOp M K e fv X0 ⋆ R).holds s) :
    WPr E s (.seq (.call (some (none, none)) f args) (.return (.const 0#64)))
      (HandlerQ M K e fv R s.ffi X0) := by
  refine WPr.seq (fun s' => ∃ g m X n, s' = ⟨s.locals, g, m, s.ffi⟩ ∧ FrameOk M K fv X ∧
      Adv X X0 n ∧ 0 < n ∧ (FrameOp M K e fv X ⋆ R).holds s')
    (WPr.call_spec (HandlerQ M K e fv R s.ffi X0)
      (fun parameters body _ cl hlk _ _ =>
        hf parameters body hlk ⟨cl, s.globals, s.memory, s.ffi⟩ M K e fv R X0 hok
          (Assn.holds_congr rfl rfl h)) ?_ ?_ ?_) ?_
  · rintro l g m ffi vs ((ht | ⟨_, _, _, _, _, _, _, _, _, hC⟩) | ⟨X, n, hokX, hp, hn, hh, _, _, _, hC⟩)
    · exact ht.elim
    · cases hC
    · injection hC with _ _ _ hf' _
      subst hf'
      exact ⟨g, m, X, n, rfl, hokX, hp, hn, Assn.holds_congr rfl rfl hh⟩
  · rintro l g m ffi exc v ((ht | ⟨X, n, hokX, hp, hh, _, _, _, _, hC⟩) | ⟨_, _, _, _, _, _, _, _, _, hC⟩)
    · exact Or.inl (Or.inl ht)
    · injection hC with _ _ _ hf' hx hv
      subst hf' hx hv
      exact Or.inl (Or.inr ⟨X, n, hokX, hp, Assn.holds_congr rfl rfl hh, _, _, _, _, rfl⟩)
    · cases hC
  · intro l g m ffi ev _
    exact Or.inl (Or.inl trivial)
  · rintro _ ⟨g, m, X, n, rfl, hokX, hp, hn, hh⟩
    exact WPr.ret (w := 0#64) (of_eval (eval_const _ _))
      (Or.inr ⟨X, n, hokX, hp, hn, Assn.holds_congr rfl rfl hh, _, _, _, rfl⟩)

end InitECandidate.Solver.GuestBound
