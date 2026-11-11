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

end InitECandidate.Solver.GuestBound
