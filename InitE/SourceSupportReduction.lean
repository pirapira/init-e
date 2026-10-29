import InitE.SourceWitness.CodeReduction

namespace InitE.SourceSupportReduction
open Flapjack Flapjack.PanSemStateFiniteExact Lean Meta Sym Meta.Tactic.Cbv

def Supported {α β : Type} (lookup : α → Option β) : Prop :=
  ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys

theorem supported_empty {α β : Type} : Supported (fun _ : α => (none : Option β)) :=
  ⟨[], by intro key different; exact False.elim (different rfl)⟩

theorem supported_if {α β : Type} [DecidableEq α] (lookup : α → Option β)
    (support : Supported lookup) (name : α) (value : Option β) :
    Supported (fun key => if key = name then value else lookup key) := by
  obtain ⟨keys, hkeys⟩ := support
  refine ⟨name :: keys, ?_⟩
  intro key different
  by_cases equal : key = name
  · simp [equal]
  · exact List.mem_cons_of_mem name (hkeys key (by simpa [equal] using different))

def setOption {α β : Type} [DecidableEq α] (lookup : α → Option β)
    (name : α) (value : Option β) : α → Option β :=
  fun key => if key = name then value else lookup key

scoped cbv_simproc ↓ holdSetOption (@setOption _ _ _ _ _ _) :=
  fun e => return .rfl (done := e.getAppNumArgs == 6)

initialize mapCache : IO.Ref (Std.HashMap Expr Expr) ← IO.mkRef {}

mutual
partial def compactMap (lookup : Expr) : MetaM Expr := do
  let lookup ← instantiateMVars lookup
  let closed := !lookup.hasMVar && !lookup.hasFVar && !lookup.hasLooseBVars
  if closed then
    if let some map := (← mapCache.get)[lookup]? then return map
  let map ← compactMapCore lookup
  if closed && !map.hasMVar && !map.hasFVar && !map.hasLooseBVars then
    mapCache.modify fun cache => cache.insert lookup map |>.insert map.getAppArgs[2]! map
  return map

partial def compactMapCore (lookup : Expr) : MetaM Expr := do
  let codeLookup := mkConst ``InitE.SourceWitness.codeLookup
  if (← isDefEq (← Meta.inferType lookup) (← Meta.inferType codeLookup)) &&
      (← isDefEq lookup codeLookup) then
    return ← mkAppM ``HolFiniteMapExact.mk #[codeLookup,
      mkProj ``HolFiniteMapExact 1 (mkConst ``InitE.SourceWitness.code0890)]
  if let .proj ``HolFiniteMapExact 0 map := lookup then
    let map ← whnf map
    if map.isAppOfArity ``HolFiniteMapExact.mk 4 then
      return ← compactMap map.getAppArgs[2]!
  if lookup.isAppOfArity ``HolFiniteMapExact.lookup 3 then
    let map ← whnf lookup.getAppArgs[2]!
    if map.isAppOfArity ``HolFiniteMapExact.mk 4 then
      return ← compactMap map.getAppArgs[2]!
  if lookup.isAppOfArity ``FUPDATE 5 || lookup.isAppOfArity ``FUPDATE_HOL 5 then
    let args := lookup.getAppArgs
    let map ← compactMap args[3]!
    let base := map.getAppArgs[2]!
    let operation := if lookup.isAppOf ``FUPDATE then ``FUPDATE else ``FUPDATE_HOL
    let update := if lookup.isAppOf ``FUPDATE then ``HolFiniteMapExact.update
      else ``HolFiniteMapExact.updateEq
    let normalized ← mkAppM operation #[base, args[4]!]
    let updated ← mkAppM update #[map, args[4]!]
    return ← mkAppM ``HolFiniteMapExact.mk #[normalized, mkProj ``HolFiniteMapExact 1 updated]
  if lookup.isAppOfArity ``setOption 6 then
    let args := lookup.getAppArgs
    let map ← compactMap args[3]!
    let base := map.getAppArgs[2]!
    let normalized ← mkAppM ``setOption #[base, args[4]!, args[5]!]
    let support ← mkAppM ``supported_if #[base, map.getAppArgs[3]!, args[4]!, args[5]!]
    return ← mkAppM ``HolFiniteMapExact.mk #[normalized, support]
  if let .lam _ domain body _ := lookup then
    if body.isAppOf ``Option.none then
      let type ← Meta.inferType lookup
      let .forallE _ _ range _ := type | throwError "not a function"
      let beta := range.getAppArgs[0]!
      let support ← mkAppOptM ``supported_empty #[domain, beta]
      return ← mkAppM ``HolFiniteMapExact.mk #[lookup, support]
    if body.isAppOfArity ``ite 5 then
      let args := body.getAppArgs
      let condition := args[1]!
      let yes := args[3]!
      let no := args[4]!
      if condition.isAppOfArity ``Eq 3 && no.isApp && no.appArg! == mkBVar 0 then
        let sides := condition.getAppArgs
        if sides[1]! == mkBVar 0 then
          let map ← compactMap no.appFn!
          let base := map.getAppArgs[2]!
          let normalized ← mkAppM ``setOption #[base, sides[2]!, yes]
          let support ← mkAppM ``supported_if #[base, map.getAppArgs[3]!, sides[2]!, yes]
          return ← mkAppM ``HolFiniteMapExact.mk #[normalized, support]
        let test := sides[1]!
        if test.isAppOfArity ``BEq.beq 4 && yes.isAppOfArity ``Option.some 2 &&
            test.getAppArgs[3]! == mkBVar 0 then
          let map ← compactMap no.appFn!
          let base := map.getAppArgs[2]!
          let entry ← mkAppM ``Prod.mk #[test.getAppArgs[2]!, yes.getAppArgs[1]!]
          let normalized ← mkAppM ``FUPDATE #[base, entry]
          let updated ← mkAppM ``HolFiniteMapExact.update #[map, entry]
          return ← mkAppM ``HolFiniteMapExact.mk #[normalized, mkProj ``HolFiniteMapExact 1 updated]
  let reduced ← whnf lookup
  if reduced != lookup then return ← compactMap reduced
  throwError "No compact map for {lookup}"

end

scoped cbv_simproc cbv_eval compactOfExact (@ofExact _ _ _ _ _) := fun e => do
  let args := e.getAppArgs
  unless (← isDefEq args[0]! (mkNatLit 64)) do return .rfl
  let raw := args[3]!
  unless raw.isAppOfArity ``PanSemStateExact.mk 16 do return .rfl
  let mut fields := raw.getAppArgs
  for i in [3, 4, 6, 7] do
    let lookup := fields[i]!
    fields := fields.set! i (← compactMap lookup)
  let result ← Sym.shareCommon (mkAppN (mkConst ``PanSemStateFiniteExact.mk) fields)
  return .step result (← Sym.mkEqRefl result)

end InitE.SourceSupportReduction
