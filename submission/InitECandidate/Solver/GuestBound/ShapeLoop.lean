import InitECandidate.Solver.GuestBound.ShapeFrame
import InitECandidate.Solver.GuestBound.WalkMBound
import InitECandidate.Solver.GuestBound.ExpCostEval
import Flapjack.PanValueShapeInversion

/-!
# Loops over struct-valued locals

A loop whose body passes `shapeOk` changes only a few locals and keeps their
shapes. When those shapes are known flat records of words (from the enclosing
declarations, tracked by `CostsIn`), the loop-head states embed into a finite
type, and a returning run cannot visit a state twice.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type} {E : Env σ}

/-! ### A loop over finitely many states -/

/-- The invariant holds again when the loop head is reached. -/
def KeepI (I : St σ → Prop) : Result σ → Prop
  | .normal l g m f | .continued l g m f => I ⟨l, g, m, f⟩
  | _ => True

open Classical in
/-- With the codes in `V` already visited by longer runs, at most `N - |V|` iterations remain. -/
theorem finite_core {α : Type} [Fintype α] (I : St σ → Prop) (enc : St σ → α)
    (hinj : ∀ s s', I s → I s' → enc s = enc s' → s = s') (N : Nat)
    (hcard : Fintype.card α ≤ N) {c : Exp Word} {body : Prog Word} {b : Nat}
    (hbody : Triple E I body b (KeepI I)) (r : Result σ) (hne : r.isError = false) :
    ∀ (fuel : Nat) (V : Finset α) (s : St σ) (m : Nat),
      I s → E.run fuel s (.while c body) = some (r, m) →
      (∀ code ∈ V, ∃ s' fuel' m', I s' ∧ enc s' = code ∧ fuel ≤ fuel' ∧
        m < m' ∧ E.run fuel' s' (.while c body) = some (r, m')) →
      m + V.card * (panValueExpStepCost c + b + 1) ≤ N * (panValueExpStepCost c + b + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro V s m _ hrun
    simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel ih =>
    intro V s m hok hrun0 hV
    have hrun := hrun0
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    have hnotV : enc s ∉ V := by
      intro hmem
      obtain ⟨s', fuel', m', hok', henc, hfuel, hlt, hrun'⟩ := hV _ hmem
      have hs : s' = s := hinj _ _ hok' hok henc
      have hsame := run_mono hfuel hrun0
      rw [hs] at hrun'
      rw [hrun'] at hsame
      simp only [Option.some.injEq, Prod.mk.injEq] at hsame
      omega
    have hcard' : V.card + 1 ≤ N :=
      Nat.le_trans (Finset.card_lt_univ_of_notMem hnotV) hcard
    have hroom : V.card * (panValueExpStepCost c + b + 1) + (panValueExpStepCost c + b + 1) ≤
        N * (panValueExpStepCost c + b + 1) := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ hcard'
    cases hcond : panValueIteCondition E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory c E.memoryAccess with
    | none =>
      rw [hcond] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, -⟩ := hrun
      exact Bool.noConfusion hne
    | some pair =>
      obtain ⟨v, kc⟩ := pair
      rw [hcond] at hrun
      have hkc : kc ≤ panValueExpStepCost c :=
        condCost (E := E) (fun _ => True) c s v kc trivial hcond
      simp only [Option.elim_some] at hrun
      by_cases hv : (v == 0) = true
      · rw [if_pos hv] at hrun
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      · rw [if_neg hv] at hrun
        cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
            E.functions E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals
            s.memory s.ffi body (memoryAccess := E.memoryAccess)
            (contracts := E.contracts) (memoryHandler := E.memoryHandler) with
        | none => rw [hb] at hrun; simp at hrun
        | some pair =>
          obtain ⟨rb, nb⟩ := pair
          rw [hb] at hrun
          have again : ∀ l g mem f, nb ≤ b → I ⟨l, g, mem, f⟩ →
              (do
                let (loopResult, loopSteps) ← evalPanValueFfiProgSteps E.context E.primitive
                  E.handler E.structs E.functions E.baseAddress E.topAddress E.bytesInWord fuel
                  l g mem f (.while c body) (memoryAccess := E.memoryAccess)
                  (contracts := E.contracts) (memoryHandler := E.memoryHandler)
                pure (loopResult, kc + nb + loopSteps + 1)) = some (r, m) →
              m + V.card * (panValueExpStepCost c + b + 1) ≤
                N * (panValueExpStepCost c + b + 1) := by
            intro l g mem f hnb hok' hrun
            cases hloop : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
                E.functions E.baseAddress E.topAddress E.bytesInWord fuel l g mem f
                (.while c body) (memoryAccess := E.memoryAccess) (contracts := E.contracts)
                (memoryHandler := E.memoryHandler) with
            | none => rw [hloop] at hrun; simp at hrun
            | some pair =>
              obtain ⟨rl, nl⟩ := pair
              rw [hloop] at hrun
              simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
                Option.some.injEq, Prod.mk.injEq] at hrun
              obtain ⟨rfl, rfl⟩ := hrun
              have hV' : ∀ code ∈ insert (enc s) V, ∃ s' fuel' m', I s' ∧
                  enc s' = code ∧ fuel ≤ fuel' ∧ nl < m' ∧
                  E.run fuel' s' (.while c body) = some (rl, m') := by
                intro code hcode
                rcases Finset.mem_insert.mp hcode with rfl | hcode
                · exact ⟨s, fuel + 1, _, hok, rfl, Nat.le_succ _, by omega, hrun0⟩
                · obtain ⟨s', fuel', m', hok'', henc, hfuel, hlt, hrun'⟩ := hV code hcode
                  exact ⟨s', fuel', m', hok'', henc, by omega, by omega, hrun'⟩
              have hih := ih (insert (enc s) V) ⟨l, g, mem, f⟩ nl hok' hloop hV'
              rw [Finset.card_insert_of_notMem hnotV, Nat.succ_mul] at hih
              omega
          cases rb with
          | normal l g mem f =>
            obtain ⟨hnb, hI'⟩ := hbody fuel s _ nb hok hb rfl
            exact again l g mem f hnb hI' hrun
          | continued l g mem f =>
            obtain ⟨hnb, hI'⟩ := hbody fuel s _ nb hok hb rfl
            exact again l g mem f hnb hI' hrun
          | broke l g mem f =>
            have hnb : nb ≤ b := (hbody fuel s _ nb hok hb rfl).1
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            omega
          | _ =>
            simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def,
              Option.some.injEq, Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            have hnb : nb ≤ b := (hbody fuel s _ nb hok hb hne).1
            omega

/-! ### Flat shapes -/

/-- All fields are single words. -/
def allOne : List Shape → Bool
  | [] => true
  | .one :: rest => allOne rest
  | _ => false

/-- Number of words of a word or a flat record of words. -/
def flatSize : Shape → Option Nat
  | .one => some 1
  | .comb fields => if allOne fields then some fields.length else none
  | _ => none

theorem allOne_eq {fields : List Shape} (h : allOne fields = true) :
    fields = (List.replicate fields.length (0 : Word)).map (fun _ => Shape.one) := by
  induction fields with
  | nil => rfl
  | cons a rest ih =>
    cases a with
    | one =>
      simp only [allOne] at h
      simp only [List.length_cons, List.replicate_succ, List.map_cons]
      rw [← ih h]
    | _ => simp [allOne] at h

/-- The value is present with shape `sh`. -/
def HasShape (structs : StructContext) (sh : Shape) (v : Option (PanValue Word)) : Prop :=
  ∃ pv, v = some pv ∧ panValueShape structs pv = sh

theorem HasShape.of_same {structs : StructContext} {sh : Shape}
    {a b : Option (PanValue Word)} (h : SameShape structs a b) (hb : HasShape structs sh b) :
    HasShape structs sh a := by
  rcases h with rfl | ⟨va, vb, rfl, rfl, hab⟩
  · exact hb
  · obtain ⟨pv, hpv, hs⟩ := hb
    simp only [Option.some.injEq] at hpv
    subst hpv
    exact ⟨va, rfl, hab.trans hs⟩

/-- The words of a value, padded. -/
def flatOf (K : Nat) : Option (PanValue Word) → Fin K → Word
  | some (.word w) => fun _ => w
  | some (.rStruct fields) => fun i =>
      match fields[i.val]? with
      | some (.word w) => w
      | _ => 0
  | _ => fun _ => 0

theorem flat_inj {structs : StructContext} {sh : Shape} {k K : Nat}
    (hsize : flatSize sh = some k) (hk : k ≤ K) (hpos : 0 < K)
    {v v' : Option (PanValue Word)} (hv : HasShape structs sh v) (hv' : HasShape structs sh v')
    (h : flatOf K v = flatOf K v') : v = v' := by
  obtain ⟨pv, rfl, hs⟩ := hv
  obtain ⟨pv', rfl, hs'⟩ := hv'
  cases sh with
  | one =>
    obtain ⟨w, rfl⟩ := panValueShape_matches_one_inv structs pv
      (by rw [hs]; simp [panShapeMatches])
    obtain ⟨w', rfl⟩ := panValueShape_matches_one_inv structs pv'
      (by rw [hs']; simp [panShapeMatches])
    have := congrFun h ⟨0, hpos⟩
    simp only [flatOf] at this
    rw [this]
  | comb fields =>
    simp only [flatSize] at hsize
    split at hsize
    · rename_i hall
      simp only [Option.some.injEq] at hsize
      have hf := allOne_eq hall
      have hmatch : ∀ pv : PanValue Word, panValueShape structs pv = .comb fields →
          panShapeMatches (panValueShape structs pv)
            (.comb ((List.replicate fields.length (0 : Word)).map (fun _ => Shape.one))) = true := by
        intro pv hpv
        rw [hpv, ← hf]
        exact (panShapeMatches_eq_true _ _).mpr rfl
      obtain ⟨ws, rfl, hlen⟩ := panValueShape_matches_word_record_inv structs pv
        (List.replicate fields.length (0 : Word)) (hmatch pv hs)
      obtain ⟨ws', rfl, hlen'⟩ := panValueShape_matches_word_record_inv structs pv'
        (List.replicate fields.length (0 : Word)) (hmatch pv' hs')
      simp only [List.length_replicate] at hlen hlen'
      have hws : ws = ws' := by
        apply List.ext_getElem (by rw [hlen, hlen'])
        intro i h1 h2
        have hiK : i < K := by omega
        have := congrFun h ⟨i, hiK⟩
        simp only [flatOf, List.getElem?_map, List.getElem?_eq_getElem h1,
          List.getElem?_eq_getElem h2, Option.map_some] at this
        exact this
      rw [hws]
    · cases hsize
  | named name => simp [flatSize] at hsize

/-! ### Shapes known from declarations -/

/-- The innermost declared shape of `x`. -/
def findShape : List (VarName × Shape) → VarName → Option Shape
  | [], _ => none
  | (y, sh) :: rest, x => if x == y then some sh else findShape rest x

/-- Every local listed in `D` holds a value of its listed shape. -/
def ShapedAt (structs : StructContext) (D : List (VarName × Shape)) (s : St σ) : Prop :=
  ∀ x sh, findShape D x = some sh → HasShape structs sh (s.locals x)

/-- A step bound for runs from states where the locals in `D` have their declared shapes. -/
def CostsIn (E : Env σ) (D : List (VarName × Shape)) (p : Prog Word) (B : Nat) : Prop :=
  Triple E (ShapedAt E.structs D) p B (fun _ => True)

theorem ShapedAt.frame {structs : StructContext} {D : List (VarName × Shape)} {s s' : St σ}
    (h : ShapedAt structs D s) (hl : ∀ x, SameShape structs (s'.locals x) (s.locals x)) :
    ShapedAt structs D s' :=
  fun x sh hx => HasShape.of_same (hl x) (h x sh hx)

theorem ShapedAt.dec {structs : StructContext} {D : List (VarName × Shape)} {s : St σ}
    {x : VarName} {sh : Shape} {v : PanValue Word} (h : ShapedAt structs D s)
    (hv : panShapeMatches (panValueShape structs v) sh = true)
    (g : VarName → Option (PanValue Word)) (m : Word → Option (PanValue Word))
    (f : FfiState σ) :
    ShapedAt structs ((x, sh) :: D) ⟨updatePanValueMap s.locals x v, g, m, f⟩ := by
  intro y shy hy
  simp only [findShape] at hy
  by_cases hyx : (y == x) = true
  · rw [if_pos hyx] at hy
    simp only [Option.some.injEq] at hy
    subst hy
    exact ⟨v, by simp [updatePanValueMap, hyx], (panShapeMatches_eq_true _ _).mp hv⟩
  · rw [if_neg hyx] at hy
    have := h y shy hy
    simpa [updatePanValueMap, hyx] using this

theorem CostsIn.of_costs {D : List (VarName × Shape)} {p : Prog Word} {B : Nat}
    (h : Costs E p B) : CostsIn E D p B :=
  h.consequence (fun _ _ => trivial) (Nat.le_refl _) (fun _ h => h)

theorem CostsIn.to_costs {p : Prog Word} {B : Nat} (h : CostsIn E [] p B) : Costs E p B :=
  h.consequence (fun _ _ => by intro x sh hx; simp [findShape] at hx) (Nat.le_refl _)
    (fun _ h => h)

theorem CostsIn.seq (callee : FunName → Bool)
    (hcallee : ∀ f, callee f = true → FunKeeps (quietKeeper E) f)
    {D : List (VarName × Shape)} (M : List VarName) {first second : Prog Word} {B₁ B₂ : Nat}
    (hok : shapeOk callee M first = true)
    (h₁ : CostsIn E D first B₁) (h₂ : CostsIn E D second B₂) :
    CostsIn E D (.seq first second) (B₁ + B₂ + 1) := by
  refine Triple.seq (Mid := ShapedAt E.structs D) (Q := fun _ => True) ?_ h₂
  intro fuel s r n hP hrun hne
  refine ⟨(h₁ fuel s r n hP hrun hne).1, ?_⟩
  have hp := shape_sound callee hcallee fuel M first s r n hok hrun
  cases r with
  | normal l g m f => exact ShapedAt.frame hP hp.2.2.2.2
  | _ => trivial

theorem CostsIn.ite {D : List (VarName × Shape)} (c : Exp Word)
    {thenBranch elseBranch : Prog Word} {B₁ B₂ : Nat}
    (h₁ : CostsIn E D thenBranch B₁) (h₂ : CostsIn E D elseBranch B₂) :
    CostsIn E D (.ite c thenBranch elseBranch) (panValueExpStepCost c + max B₁ B₂ + 1) :=
  Triple.ite (condCost _ c) h₁ h₂

theorem CostsIn.dec {D : List (VarName × Shape)} (name : VarName) (shape : Shape)
    (value : Exp Word) {body : Prog Word} {B : Nat}
    (h : CostsIn E ((name, shape) :: D) body B) :
    CostsIn E D (.dec name shape value body) (panValueExpStepCost value + B + 1) := by
  unfold CostsIn Triple
  intro fuel s r n hD hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hacc : panValueDecAccepted E.structs E.baseAddress E.topAddress E.bytesInWord
        s.locals s.globals s.memory value E.memoryAccess shape with
    | none =>
      rw [hacc] at hrun
      simp only [Option.elim_none, Option.some.injEq, Prod.mk.injEq] at hrun
      omega
    | some accepted =>
      rw [hacc] at hrun
      simp only [Option.elim_some] at hrun
      have hacc' : accepted.2 = panValueExpStepCost value ∧
          panShapeMatches (panValueShape E.structs accepted.1) shape = true := by
        simp only [panValueDecAccepted, evalPanValueExpCounted] at hacc
        cases hv : evalPanValueExp E.structs s.locals s.globals s.memory E.baseAddress
            E.topAddress E.bytesInWord value E.memoryAccess with
        | none => rw [hv] at hacc; simp at hacc
        | some evaluated =>
          rw [hv] at hacc
          simp only [Option.map_some] at hacc
          split at hacc
          · rename_i hm
            simp only [Option.some.injEq] at hacc
            rw [← hacc]
            exact ⟨rfl, hm⟩
          · simp at hacc
      obtain ⟨hsteps, hshape⟩ := hacc'
      cases hbody : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
          E.functions E.baseAddress E.topAddress E.bytesInWord fuel
          (updatePanValueMap s.locals name accepted.1) s.globals s.memory s.ffi body
          (memoryAccess := E.memoryAccess) (contracts := E.contracts)
          (memoryHandler := E.memoryHandler) with
      | none => rw [hbody] at hrun; simp at hrun
      | some bodyPair =>
        obtain ⟨rb, nb⟩ := bodyPair
        rw [hbody] at hrun
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        have hnb : nb ≤ B :=
          (h fuel ⟨updatePanValueMap s.locals name accepted.1, s.globals, s.memory, s.ffi⟩
            rb nb (ShapedAt.dec hD hshape _ _ _) hbody
            (by cases rb <;> first | rfl | cases hne)).1
        omega

theorem CostsIn.decCall {D : List (VarName × Shape)} (name : VarName) (shape : Shape)
    {f : FunName} (arguments : List (Exp Word)) {body : Prog Word} {B C : Nat}
    (hf : FunCost E f B) (hbody : CostsIn E ((name, shape) :: D) body C) :
    CostsIn E D (.decCall name shape f arguments body)
      (panValueExpsStepCost arguments + B + C + 1) := by
  unfold CostsIn Triple
  intro fuel s r n hD hrun hne
  refine ⟨?_, trivial⟩
  cases fuel with
  | zero => simp [Env.run, evalPanValueFfiProgSteps] at hrun
  | succ fuel =>
    simp only [Env.run] at hrun
    rw [evalPanValueFfiProgSteps] at hrun
    cases hcall : evalPanValueFfiCallSteps E.context E.primitive E.handler E.structs E.functions
        E.baseAddress E.topAddress E.bytesInWord fuel s.locals s.globals s.memory s.ffi none f
        arguments (memoryAccess := E.memoryAccess) (contracts := E.contracts)
        (memoryHandler := E.memoryHandler) (preserveReturnLocals := true) with
    | none => rw [hcall] at hrun; simp at hrun
    | some callPair =>
      obtain ⟨rc, nc⟩ := callPair
      rw [hcall] at hrun
      have hncOf : rc.isError = false → nc ≤ panValueExpsStepCost arguments + B + 0 := fun hrc =>
        callSteps_le (info := none) (H := 0) hf trivial fuel s arguments true rc nc hcall hrc
      simp only [Option.bind_eq_bind, Option.bind_some] at hrun
      split at hrun
      · have hnc := hncOf rfl
        split at hrun
        · rename_i returnedLocals g m ffi value hshape
          cases hb : evalPanValueFfiProgSteps E.context E.primitive E.handler E.structs
              E.functions E.baseAddress E.topAddress E.bytesInWord fuel
              (updatePanValueMap s.locals name value) g m ffi body
              (memoryAccess := E.memoryAccess) (contracts := E.contracts)
              (memoryHandler := E.memoryHandler) with
          | none => rw [hb] at hrun; simp at hrun
          | some bodyPair =>
            obtain ⟨rb, nb⟩ := bodyPair
            rw [hb] at hrun
            simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at hrun
            obtain ⟨rfl, rfl⟩ := hrun
            have hnb : nb ≤ C :=
              (hbody fuel ⟨updatePanValueMap s.locals name value, g, m, ffi⟩ rb nb
                (ShapedAt.dec hD hshape _ _ _) hb
                (by cases rb <;> first | rfl | cases hne)).1
            omega
        · simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          obtain ⟨rfl, -⟩ := hrun
          cases hne
      · have hnc := hncOf rfl
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      · have hnc := hncOf rfl
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        omega
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, -⟩ := hrun
        cases hne
      · simp at hrun

/-! ### The loop rule -/

/-- Locals assigned by `p` that `p` does not itself declare. -/
def freeAssigned : Prog Word → List VarName → List VarName → List VarName
  | .assign .local x _, bound, acc => if bound.contains x || acc.contains x then acc else x :: acc
  | .call (some (some (.local, x), none)) _ _, bound, acc =>
      if bound.contains x || acc.contains x then acc else x :: acc
  | .seq first second, bound, acc => freeAssigned second bound (freeAssigned first bound acc)
  | .ite _ thenBranch elseBranch, bound, acc =>
      freeAssigned elseBranch bound (freeAssigned thenBranch bound acc)
  | .while _ body, bound, acc => freeAssigned body bound acc
  | .dec x _ _ body, bound, acc => freeAssigned body (x :: bound) acc
  | .decCall x _ _ _ body, bound, acc => freeAssigned body (x :: bound) acc
  | _, _, acc => acc

/-- The locals a loop body changes across iterations. -/
def loopVars (body : Prog Word) : List VarName := freeAssigned body [] []

/-- Largest flat size among the listed locals (at least 1). -/
def flatMax (D : List (VarName × Shape)) : List VarName → Nat
  | [] => 1
  | x :: rest => max (((findShape D x).bind flatSize).getD 0) (flatMax D rest)

/-- Every listed local has a known flat shape. -/
def coverOk (D : List (VarName × Shape)) (M : List VarName) : Bool :=
  M.all fun x => ((findShape D x).bind flatSize).isSome

/-- The loop body changes only locals of known flat shapes. -/
def shapeLoop (callee : FunName → Bool) (D : List (VarName × Shape)) (body : Prog Word) : Bool :=
  shapeOk callee (loopVars body) body && coverOk D (loopVars body)

/-- Number of states of `n` locals of at most `K` words each. -/
def shapeIters (K n : Nat) : Nat := ((2 ^ 64) ^ K) ^ n

theorem flatMax_pos (D : List (VarName × Shape)) (M : List VarName) : 0 < flatMax D M := by
  induction M with
  | nil => simp [flatMax]
  | cons x rest ih => simp only [flatMax]; omega

theorem flatMax_ge {D : List (VarName × Shape)} {M : List VarName} {x : VarName} {sh : Shape}
    {k : Nat} (hx : x ∈ M) (hfind : findShape D x = some sh) (hsize : flatSize sh = some k) :
    k ≤ flatMax D M := by
  induction M with
  | nil => cases hx
  | cons y rest ih =>
    simp only [flatMax]
    rcases List.mem_cons.mp hx with rfl | hx'
    · simp [hfind, hsize]
    · have := ih hx'
      omega

theorem cover_find {D : List (VarName × Shape)} {M : List VarName} {x : VarName}
    (h : coverOk D M = true) (hx : x ∈ M) :
    ∃ sh k, findShape D x = some sh ∧ flatSize sh = some k := by
  have h' := List.all_eq_true.mp h x hx
  cases hfind : findShape D x with
  | none => rw [hfind] at h'; simp at h'
  | some sh =>
    rw [hfind] at h'
    cases hsize : flatSize sh with
    | none => simp [hsize] at h'
    | some k => exact ⟨sh, k, rfl, hsize⟩

theorem shape_card (K n : Nat) : Fintype.card (Fin n → Fin K → Word) ≤ shapeIters K n := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  exact Nat.pow_le_pow_left (Nat.pow_le_pow_left word_card _) _

/-- A loop that changes only locals of known flat shapes visits each of their
joint values at most once. -/
theorem shapeLoop_costs (callee : FunName → Bool)
    (hcallee : ∀ f, callee f = true → FunKeeps (quietKeeper E) f)
    (D : List (VarName × Shape)) (c : Exp Word) (body : Prog Word) (b : Nat)
    (hcheck : shapeLoop callee D body = true) (hbody : CostsIn E D body b) :
    CostsIn E D (.while c body)
      (shapeIters (flatMax D (loopVars body)) (loopVars body).length * (expCost c + b + 1)) := by
  intro fuel s r m hD hrun hne
  refine ⟨?_, trivial⟩
  rw [← stepCost_eq]
  simp only [shapeLoop, Bool.and_eq_true] at hcheck
  obtain ⟨hok, hcov⟩ := hcheck
  generalize loopVars body = M at hok hcov ⊢
  let I : St σ → Prop := fun a => ShapeFrame E M s a.locals a.globals a.memory a.ffi
  let enc : St σ → (Fin M.length → Fin (flatMax D M) → Word) :=
    fun a j => flatOf (flatMax D M) (a.locals (M.get j))
  have hinj : ∀ a a', I a → I a' → enc a = enc a' → a = a' := by
    intro a a' ha ha' henc
    have hlocals : a.locals = a'.locals := by
      funext x
      by_cases hx : x ∈ M
      · obtain ⟨sh, k, hfind, hsize⟩ := cover_find hcov hx
        have hbase := hD x sh hfind
        have hk := flatMax_ge hx hfind hsize
        obtain ⟨j, rfl⟩ := List.get_of_mem hx
        exact flat_inj hsize hk (flatMax_pos D M) (HasShape.of_same (ha.2.2.2.2 _) hbase)
          (HasShape.of_same (ha'.2.2.2.2 _) hbase) (congrFun henc j)
      · rw [ha.2.2.2.1 x hx, ha'.2.2.2.1 x hx]
    cases a with
    | mk l g mem f =>
      cases a' with
      | mk l' g' mem' f' =>
        simp only at hlocals
        obtain ⟨hg, hm, hf, -, -⟩ := ha
        obtain ⟨hg', hm', hf', -, -⟩ := ha'
        simp only at hg hm hf hg' hm' hf'
        rw [hlocals, hg, hm, hf, hg', hm', hf']
  have hb : Triple E I body b (KeepI I) := by
    intro fuel' s' r' n' hI hrun' hne'
    have hD' : ShapedAt E.structs D s' := ShapedAt.frame hD hI.2.2.2.2
    refine ⟨(hbody fuel' s' r' n' hD' hrun' hne').1, ?_⟩
    have hp := shape_sound callee hcallee fuel' M body s' r' n' hok hrun'
    have ht := ShapePost.trans (s := s) hI hp
    cases r' with
    | normal l g mem f => exact ht
    | continued l g mem f => exact ht
    | _ => trivial
  have h := finite_core I enc hinj _ (shape_card (flatMax D M) M.length) hb r hne fuel ∅ s m
    (ShapeFrame.refl M s) hrun (by intro code hcode; simp at hcode)
  simpa using h

end InitECandidate.Solver.GuestBound
