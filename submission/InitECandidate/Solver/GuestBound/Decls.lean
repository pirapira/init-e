import InitECandidate.Solver.GuestBound.ProgramBound

/-!
# Function tables that come from a declaration list

After `evalPanValueDeclarations`, every registered function body is the body
of a function declaration with that name. `funCost_of_named` then reduces a
`FunCost` to the bodies of the declarations with that name.
-/

namespace InitECandidate.Solver.GuestBound
open Flapjack

variable {σ : Type}

/-- Every function registered in `functions` is declared in `declarations`. -/
def FunctionsFrom (functions : List (FunName × List VarName × Prog Word))
    (declarations : List (Decl Word)) : Prop :=
  ∀ f parameters body, (f, parameters, body) ∈ functions →
    ∃ d, Decl.function d ∈ declarations ∧ d.name = f ∧ d.body = body ∧
      d.params.map Prod.fst = parameters

/-- The function declarations named `f`, as declarations. -/
def declsNamed (f : FunName) : List (Decl Word) → List (Decl Word)
  | [] => []
  | .function d :: rest =>
      if d.name == f then .function d :: declsNamed f rest else declsNamed f rest
  | _ :: rest => declsNamed f rest

theorem mem_declsNamed {f : FunName} {d : FunDecl Word} :
    ∀ {declarations : List (Decl Word)}, Decl.function d ∈ declarations → d.name = f →
      Decl.function d ∈ declsNamed f declarations
  | [], h, _ => by cases h
  | head :: rest, h, hname => by
      rcases List.mem_cons.mp h with rfl | h
      · simp [declsNamed, hname]
      · have ih := mem_declsNamed h hname
        cases head with
        | function d' =>
          simp only [declsNamed]
          split
          · exact List.mem_cons_of_mem _ ih
          · exact ih
        | decl _ _ _ => simpa only [declsNamed] using ih
        | exnDecl _ _ => simpa only [declsNamed] using ih
        | name _ _ => simpa only [declsNamed] using ih

theorem functionsFrom_withStructs (structs : StructContext)
    (memoryAccess : Option (PanValueMemoryAccess Word)) :
    ∀ (declarations all : List (Decl Word)) (state state' : PanValueProgramState Word),
      (∀ d, d ∈ declarations → d ∈ all) → FunctionsFrom state.functions all →
      evalPanValueDeclarationsWithStructs structs state declarations
        (memoryAccess := memoryAccess) = some state' →
      FunctionsFrom state'.functions all
  | [], _, state, state', _, hfrom, h => by
      simp only [evalPanValueDeclarationsWithStructs, Option.some.injEq] at h
      subst h
      exact hfrom
  | .name _ _ :: rest, all, state, state', hsub, hfrom, h => by
      simp only [evalPanValueDeclarationsWithStructs] at h
      exact functionsFrom_withStructs structs memoryAccess rest all state state'
        (fun d hd => hsub d (List.mem_cons_of_mem _ hd)) hfrom h
  | .decl shape name expression :: rest, all, state, state', hsub, hfrom, h => by
      simp only [evalPanValueDeclarationsWithStructs, Option.bind_eq_bind] at h
      cases hv : evalPanValueExp structs (fun _ => none) state.globals state.memory
          state.baseAddress state.topAddress state.bytesInWord expression
          (memoryAccess := memoryAccess) with
      | none => rw [hv] at h; simp at h
      | some value =>
        rw [hv] at h
        simp only [Option.bind_some] at h
        split at h
        · refine functionsFrom_withStructs structs memoryAccess rest all _ state' ?_ ?_ h
          · exact fun d hd => hsub d (List.mem_cons_of_mem _ hd)
          · exact hfrom
        · simp at h
  | .function declaration :: rest, all, state, state', hsub, hfrom, h => by
      simp only [evalPanValueDeclarationsWithStructs] at h
      split at h
      · refine functionsFrom_withStructs structs memoryAccess rest all _ state'
          (fun d hd => hsub d (List.mem_cons_of_mem _ hd)) ?_ h
        intro f parameters body hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · simp only [Prod.mk.injEq] at heq
          exact ⟨declaration, hsub _ (List.mem_cons_self), heq.1.symm, heq.2.2.symm,
            heq.2.1.symm⟩
        · exact hfrom f parameters body hmem
      · simp at h
  | .exnDecl exception shape :: rest, all, state, state', hsub, hfrom, h => by
      simp only [evalPanValueDeclarationsWithStructs] at h
      split at h
      · simp at h
      · split at h
        · refine functionsFrom_withStructs structs memoryAccess rest all _ state' ?_ ?_ h
          · exact fun d hd => hsub d (List.mem_cons_of_mem _ hd)
          · exact hfrom
        · simp at h

/-- After evaluating `declarations` from a state without functions, every
registered function is declared in `declarations`. -/
theorem functionsFrom_declarations (state state' : PanValueProgramState Word)
    (declarations : List (Decl Word)) (memoryAccess : Option (PanValueMemoryAccess Word))
    (hempty : state.functions = [])
    (h : evalPanValueDeclarations state declarations (memoryAccess := memoryAccess) =
      some state') :
    FunctionsFrom state'.functions declarations := by
  simp only [evalPanValueDeclarations, Option.bind_eq_bind] at h
  cases hs : collectPanValueStructs declarations state.structs with
  | none => rw [hs] at h; simp at h
  | some structs =>
    rw [hs] at h
    simp only [Option.bind_some] at h
    refine functionsFrom_withStructs structs memoryAccess declarations declarations _ state'
      (fun _ hd => hd) ?_ h
    intro f parameters body hmem
    simp [hempty] at hmem

/-- Evaluating declarations keeps the word size and the memory. -/
theorem layout_withStructs (structs : StructContext)
    (memoryAccess : Option (PanValueMemoryAccess Word)) :
    (declarations : List (Decl Word)) → (state state' : PanValueProgramState Word) →
    evalPanValueDeclarationsWithStructs structs state declarations
      (memoryAccess := memoryAccess) = some state' →
    state'.bytesInWord = state.bytesInWord ∧ state'.memory = state.memory ∧
      state'.baseAddress = state.baseAddress
  | [], state, state', h => by
      simp only [evalPanValueDeclarationsWithStructs, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
  | .name _ _ :: rest, state, state', h => by
      simp only [evalPanValueDeclarationsWithStructs] at h
      exact layout_withStructs structs memoryAccess rest state state' h
  | .decl shape name expression :: rest, state, state', h => by
      simp only [evalPanValueDeclarationsWithStructs, Option.bind_eq_bind] at h
      cases hv : evalPanValueExp structs (fun _ => none) state.globals state.memory
          state.baseAddress state.topAddress state.bytesInWord expression
          (memoryAccess := memoryAccess) with
      | none => rw [hv] at h; simp at h
      | some value =>
        rw [hv] at h
        simp only [Option.bind_some] at h
        split at h
        · have := layout_withStructs structs memoryAccess rest _ state' h
          exact this
        · simp at h
  | .function declaration :: rest, state, state', h => by
      simp only [evalPanValueDeclarationsWithStructs] at h
      split at h
      · have := layout_withStructs structs memoryAccess rest _ state' h
        exact this
      · simp at h
  | .exnDecl exception shape :: rest, state, state', h => by
      simp only [evalPanValueDeclarationsWithStructs] at h
      split at h
      · simp at h
      · split at h
        · have := layout_withStructs structs memoryAccess rest _ state' h
          exact this
        · simp at h

theorem layout_declarations (state state' : PanValueProgramState Word)
    (declarations : List (Decl Word)) (memoryAccess : Option (PanValueMemoryAccess Word))
    (h : evalPanValueDeclarations state declarations (memoryAccess := memoryAccess) =
      some state') :
    state'.bytesInWord = state.bytesInWord ∧ state'.memory = state.memory ∧
      state'.baseAddress = state.baseAddress := by
  simp only [evalPanValueDeclarations, Option.bind_eq_bind] at h
  cases hs : collectPanValueStructs declarations state.structs with
  | none => rw [hs] at h; simp at h
  | some structs =>
    rw [hs] at h
    simp only [Option.bind_some] at h
    have := layout_withStructs structs memoryAccess declarations _ state' h
    exact this

/-- The constant the last declaration of global `x` assigns, if that declaration
has a constant initializer; `acc` is the value before the list. -/
def finalConst (x : VarName) : List (Decl Word) → Option Word → Option Word
  | [], acc => acc
  | .decl _ name e :: rest, acc =>
      finalConst x rest (if name == x then
        (match e with
          | .const k => some k
          | _ => none) else acc)
  | _ :: rest, acc => finalConst x rest acc

/-- A global whose last declaration has a constant initializer holds that constant. -/
theorem globals_withStructs (structs : StructContext)
    (memoryAccess : Option (PanValueMemoryAccess Word)) (x : VarName) :
    (declarations : List (Decl Word)) → (state state' : PanValueProgramState Word) →
    (acc : Option Word) → (k : Word) →
    evalPanValueDeclarationsWithStructs structs state declarations
      (memoryAccess := memoryAccess) = some state' →
    (∀ k0, acc = some k0 → state.globals x = some (.word k0)) →
    finalConst x declarations acc = some k → state'.globals x = some (.word k)
  | [], state, state', acc, k, h, hacc, hfin => by
      simp only [evalPanValueDeclarationsWithStructs, Option.some.injEq] at h
      subst h
      exact hacc k hfin
  | .name _ _ :: rest, state, state', acc, k, h, hacc, hfin => by
      simp only [evalPanValueDeclarationsWithStructs] at h
      exact globals_withStructs structs memoryAccess x rest state state' acc k h hacc hfin
  | .decl shape name expression :: rest, state, state', acc, k, h, hacc, hfin => by
      simp only [evalPanValueDeclarationsWithStructs, Option.bind_eq_bind] at h
      cases hv : evalPanValueExp structs (fun _ => none) state.globals state.memory
          state.baseAddress state.topAddress state.bytesInWord expression
          (memoryAccess := memoryAccess) with
      | none => rw [hv] at h; simp at h
      | some value =>
        rw [hv] at h
        simp only [Option.bind_some] at h
        split at h
        · refine globals_withStructs structs memoryAccess x rest _ state' _ k h ?_ hfin
          intro k0 hk0
          show updatePanValueMap state.globals name value x = some (.word k0)
          by_cases hn : (name == x) = true
          · rw [if_pos hn] at hk0
            have hx : (x == name) = true := by rw [BEq.comm]; exact hn
            simp only [updatePanValueMap, hx, if_true]
            split at hk0
            · rename_i c
              simp only [Option.some.injEq] at hk0
              subst hk0
              simp [evalPanValueExp] at hv
              rw [hv]
            · cases hk0
          · rw [if_neg hn] at hk0
            have hx : (x == name) = false := by
              rw [BEq.comm]
              simpa using hn
            simp only [updatePanValueMap, hx]
            exact hacc k0 hk0
        · simp at h
  | .function declaration :: rest, state, state', acc, k, h, hacc, hfin => by
      simp only [evalPanValueDeclarationsWithStructs] at h
      split at h
      · exact globals_withStructs structs memoryAccess x rest _ state' acc k h hacc hfin
      · simp at h
  | .exnDecl exception shape :: rest, state, state', acc, k, h, hacc, hfin => by
      simp only [evalPanValueDeclarationsWithStructs] at h
      split at h
      · simp at h
      · split at h
        · exact globals_withStructs structs memoryAccess x rest _ state' acc k h hacc hfin
        · simp at h

theorem globals_declarations (state state' : PanValueProgramState Word)
    (declarations : List (Decl Word)) (memoryAccess : Option (PanValueMemoryAccess Word))
    (x : VarName) (k : Word)
    (h : evalPanValueDeclarations state declarations (memoryAccess := memoryAccess) =
      some state') (hfin : finalConst x declarations none = some k) :
    state'.globals x = some (.word k) := by
  simp only [evalPanValueDeclarations, Option.bind_eq_bind] at h
  cases hs : collectPanValueStructs declarations state.structs with
  | none => rw [hs] at h; simp at h
  | some structs =>
    rw [hs] at h
    simp only [Option.bind_some] at h
    exact globals_withStructs structs memoryAccess x declarations _ state' none k h
      (fun _ hk => by cases hk) hfin

/-- No function declaration other than the one at position `i` is named `f`
(`j` is the position of the head of the list). -/
def uniqueAt (f : FunName) (i : Nat) : List (Decl Word) → Nat → Bool
  | [], _ => true
  | .function d :: rest, j => (j == i || !(d.name == f)) && uniqueAt f i rest (j + 1)
  | _ :: rest, j => uniqueAt f i rest (j + 1)

theorem uniqueAt_mem {f : FunName} {i : Nat} {d : FunDecl Word} :
    ∀ {declarations : List (Decl Word)} {j : Nat}, uniqueAt f i declarations j = true →
      Decl.function d ∈ declarations → d.name = f →
      ∃ k, declarations[k]? = some (Decl.function d) ∧ j + k = i
  | [], _, _, h, _ => by cases h
  | head :: rest, j, hu, h, hname => by
      rcases List.mem_cons.mp h with rfl | h
      · simp only [uniqueAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
          beq_eq_false_iff_ne, ne_eq] at hu
        refine ⟨0, by simp, ?_⟩
        rcases hu.1 with hji | hne
        · simpa using hji
        · exact absurd hname hne
      · have hrest : uniqueAt f i rest (j + 1) = true := by
          cases head with
          | function d' =>
            simp only [uniqueAt, Bool.and_eq_true] at hu
            exact hu.2
          | decl _ _ _ => simpa only [uniqueAt] using hu
          | exnDecl _ _ => simpa only [uniqueAt] using hu
          | name _ _ => simpa only [uniqueAt] using hu
        obtain ⟨k, hk, hjk⟩ := uniqueAt_mem hrest h hname
        exact ⟨k + 1, by simpa using hk, by omega⟩

variable {E : Env σ}

/-- A function costs at most `B` if the declaration at position `i` is the only
one with its name and its body costs at most `B`. -/
theorem funCost_of_index {declarations : List (Decl Word)} {f : FunName} {d : FunDecl Word}
    {B : Nat} (i : Nat) (hfrom : FunctionsFrom E.functions declarations)
    (hget : declarations[i]? = some (Decl.function d))
    (hunique : uniqueAt f i declarations 0 = true) (hbody : Costs E d.body B) :
    FunCost E f B := by
  intro parameters body hlookup
  obtain ⟨d', hmem, hname, hbody', -⟩ := hfrom f parameters body (lookupPanFunction_mem hlookup)
  obtain ⟨k, hk, hik⟩ := uniqueAt_mem hunique hmem hname
  have hki : k = i := by omega
  subst hki
  rw [hget] at hk
  simp only [Option.some.injEq, Decl.function.injEq] at hk
  subst hk
  rw [← hbody']
  exact hbody

/-- A registered body of `f` is the body of the declaration at position `i`,
with its declared parameters, when that is the only declaration named `f`. -/
theorem fun_of_index {declarations : List (Decl Word)} {f : FunName} {d : FunDecl Word}
    (i : Nat) (hfrom : FunctionsFrom E.functions declarations)
    (hget : declarations[i]? = some (Decl.function d))
    (hunique : uniqueAt f i declarations 0 = true) {parameters : List VarName}
    {body : Prog Word} (hlookup : lookupPanFunction f E.functions = some (parameters, body)) :
    body = d.body ∧ parameters = d.params.map Prod.fst := by
  obtain ⟨d', hmem, hname, hbody', hparams⟩ :=
    hfrom f parameters body (lookupPanFunction_mem hlookup)
  obtain ⟨k, hk, hik⟩ := uniqueAt_mem hunique hmem hname
  have hki : k = i := by omega
  subst hki
  rw [hget] at hk
  simp only [Option.some.injEq, Decl.function.injEq] at hk
  subst hk
  exact ⟨hbody'.symm, hparams.symm⟩

end InitECandidate.Solver.GuestBound
