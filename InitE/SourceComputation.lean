import InitE.SourceRun

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitE
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Constant-time membership test for the fixed source's ordinary word cells. -/
theorem ordinaryDomain_iff (a : BitVec 64) :
    ordinaryDomain a ↔ 2701131776 ≤ a.toNat ∧ a.toNat < 33806089704 ∧ a.toNat % 8 = 0 := by
  rw [ordinaryDomain, Compiler.Backend.StackRemove.mem_addresses]
  change (∃ i, i < 3888119741 ∧
    a = BitVec.ofNat 64 2701131776 + BitVec.ofNat 64 i * (8 : BitVec 64)) ↔ _
  have address (i : Nat) (bound : i < 3888119741) :
      (BitVec.ofNat 64 2701131776 + BitVec.ofNat 64 i * (8 : BitVec 64)).toNat =
        2701131776 + 8 * i := by
    rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      ← BitVec.ofNat_mul, ← BitVec.ofNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]
    omega
  constructor
  · rintro ⟨i, bound, rfl⟩
    rw [address i bound]
    omega
  · rintro ⟨lower, upper, aligned⟩
    let i := (a.toNat - 2701131776) / 8
    have bound : i < 3888119741 := by dsimp [i]; omega
    refine ⟨i, bound, BitVec.eq_of_toNat_eq ?_⟩
    rw [address i bound]
    dsimp [i]
    omega

def ordinaryDomainDecidable (a : BitVec 64) : Decidable (ordinaryDomain a) :=
  decidable_of_iff _ (ordinaryDomain_iff a).symm

theorem sharedDomain_iff (a : BitVec 64) : sharedDomain a ↔
    a.toNat % 8 = 0 ∧ ((inputStart ≤ a.toNat ∧ a.toNat < inputEnd) ∨
      (outputStart ≤ a.toNat ∧ a.toNat < outputEnd)) := by
  have log : holLOG2 (64 / 8) = 3 := by simp [holLOG2_eq_log2]
  simp only [sharedDomain, holByteAligned, log, holAligned_iff]

def sharedDomainDecidable (a : BitVec 64) : Decidable (sharedDomain a) :=
  decidable_of_iff _ (sharedDomain_iff a).symm

/-- Declarations never change either address domain. -/
theorem source_declarations_domains {σ : Type}
    (declarations : List (Pancake.PanLang.DeclHOL 64))
    (state : PanSemStateFiniteExact 64 σ) [DecidablePred state.memaddrs]
    (post : PanSemStateFiniteExact 64 σ)
    (run : evaluateDeclsHOLFinite state declarations = some post) :
    post.memaddrs = state.memaddrs ∧ post.shMemaddrs = state.shMemaddrs := by
  induction declarations generalizing state with
  | nil => cases run; exact ⟨rfl, rfl⟩
  | cons declaration declarations ih =>
    cases declaration with
    | name _ _ => exact ih state run
    | function fi =>
      simp only [evaluateDeclsHOLFinite] at run
      split at run
      · exact ih { state with code := state.code.update (fi.name, fi.params, fi.body, fi.returnShape) } run
      · cases run
    | exnDecl name shape =>
      simp only [evaluateDeclsHOLFinite] at run
      split at run
      · exact ih { state with eshapes := state.eshapes.update (name, shape) } run
      · cases run
    | decl shape name expression =>
      simp only [evaluateDeclsHOLFinite] at run
      split at run
      · rename_i value _
        split at run
        · exact @ih (setGlobalHOLFinite name value state) ‹DecidablePred state.memaddrs› run
        · cases run
      · cases run

/-- Compose independently checked declaration chunks, irrespective of the
operational memory deciders used by each chunk. -/
theorem source_declarations_append {σ : Type}
    (xs ys : List (Pancake.PanLang.DeclHOL 64))
    (s t u : PanSemStateFiniteExact 64 σ)
    (ds : DecidablePred s.memaddrs) (dt : DecidablePred t.memaddrs)
    (first : @evaluateDeclsHOLFinite 64 σ _ s ds xs = some t)
    (second : @evaluateDeclsHOLFinite 64 σ _ t dt ys = some u) :
    @evaluateDeclsHOLFinite 64 σ _ s ds (xs ++ ys) = some u := by
  induction xs generalizing s with
  | nil =>
    cases first
    have equal : ds = dt := Subsingleton.elim _ _
    cases equal
    exact second
  | cons declaration xs ih =>
    cases declaration with
    | name _ _ => exact ih s ds first
    | function fn =>
      simp only [List.cons_append, evaluateDeclsHOLFinite] at first ⊢
      split at first
      next valid =>
        rw [if_pos valid]
        exact ih { s with code := s.code.update (fn.name, fn.params, fn.body, fn.returnShape) } ds first
      next invalid => cases first
    | exnDecl name shape =>
      simp only [List.cons_append, evaluateDeclsHOLFinite] at first ⊢
      split at first
      next valid =>
        rw [if_pos valid]
        exact ih { s with eshapes := s.eshapes.update (name, shape) } ds first
      next invalid => cases first
    | decl shape name expression =>
      simp only [List.cons_append, evaluateDeclsHOLFinite] at first ⊢
      split at first
      next value expressionRun =>
        split at first
        next valid =>
          rw [if_pos valid]
          exact ih (setGlobalHOLFinite name value s) ds first
        next invalid => cases first
      next noValue => cases first

/-- Address domains bundled with their operational decision procedures. -/
structure SourceDomains where
  ordinary : BitVec 64 → Prop
  shared : BitVec 64 → Prop
  ordinaryDecider : DecidablePred ordinary
  sharedDecider : DecidablePred shared

private theorem SourceDomains.eq_of_domains (a b : SourceDomains)
    (ordinary : a.ordinary = b.ordinary) (shared : a.shared = b.shared) : a = b := by
  cases a with
  | mk ao ash ad asd =>
    cases b with
    | mk bo bsh bd bsd =>
      dsimp only at ordinary shared
      subst bo
      subst bsh
      have d : ad = bd := Subsingleton.elim _ _
      have sd : asd = bsd := Subsingleton.elim _ _
      cases d
      cases sd
      rfl

/-- The literal declaration and execution interpreters, with explicit domains. -/
def sourceRunWithDomains (domains : SourceDomains) (input : Guest.InputBlob) (clock : Nat) :
    Option (Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 Guest.HostMemory) :=
  match decsStcnamesHOLExact [] (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) with
  | none => none
  | some context =>
    let state : PanSemStateFiniteExact 64 Guest.HostMemory := { sourceInitialState input with
      structs := context
      memaddrs := domains.ordinary
      shMemaddrs := domains.shared }
    letI : DecidablePred state.memaddrs := domains.ordinaryDecider
    match evaluateDeclsHOLFinite state (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) with
    | none => none
    | some entry =>
      let entry : PanSemStateFiniteExact 64 Guest.HostMemory := { entry with
        memaddrs := domains.ordinary
        shMemaddrs := domains.shared
        clock := clock }
      letI : DecidablePred entry.memaddrs := domains.ordinaryDecider
      letI : DecidablePred entry.shMemaddrs := domains.sharedDecider
      some (evaluateHOLFiniteStateWithDeciders entry
        (.call none (Basis.Pure.MlString.ofString "main") []))

def sourceDomains : SourceDomains :=
  ⟨ordinaryDomain, sharedDomain, ordinaryDomainDecidable, sharedDomainDecidable⟩

def arithmeticOrdinaryDomain (a : BitVec 64) : Prop :=
  2701131776 ≤ a.toNat ∧ a.toNat < 33806089704 ∧ a.toNat % 8 = 0

instance (a : BitVec 64) : Decidable (arithmeticOrdinaryDomain a) := by
  unfold arithmeticOrdinaryDomain
  infer_instance

def arithmeticSharedDomain (a : BitVec 64) : Prop :=
  a.toNat % 8 = 0 ∧ ((inputStart ≤ a.toNat ∧ a.toNat < inputEnd) ∨
    (outputStart ≤ a.toNat ∧ a.toNat < outputEnd))

instance (a : BitVec 64) : Decidable (arithmeticSharedDomain a) := by
  unfold arithmeticSharedDomain
  infer_instance

def sourceArithmeticDomains : SourceDomains :=
  ⟨arithmeticOrdinaryDomain, arithmeticSharedDomain, fun _ => inferInstance,
    fun _ => inferInstance⟩

def sourceRun (input : Guest.InputBlob) (clock : Nat) :=
  sourceRunWithDomains sourceDomains input clock

/-- Direct application of the arithmetic interpreters keeps the operational
deciders out of a bundled argument during proof-producing reduction. -/
def sourceRunArithmetic (input : Guest.InputBlob) (clock : Nat) :
    Option (Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 Guest.HostMemory) :=
  match decsStcnamesHOLExact [] (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) with
  | none => none
  | some context =>
    let state : PanSemStateFiniteExact 64 Guest.HostMemory := { sourceInitialState input with
      structs := context
      memaddrs := arithmeticOrdinaryDomain
      shMemaddrs := arithmeticSharedDomain }
    match evaluateDeclsHOLFinite state (Guest.Software.guestAst.map Pancake.PanLang.declToHOL) with
    | none => none
    | some entry =>
      let entry : PanSemStateFiniteExact 64 Guest.HostMemory := { entry with
        memaddrs := arithmeticOrdinaryDomain
        shMemaddrs := arithmeticSharedDomain
        clock := clock }
      some (evaluateHOLFiniteStateWithDeciders entry
        (.call none (Basis.Pure.MlString.ofString "main") []))

theorem sourceRunArithmetic_eq (input : Guest.InputBlob) (clock : Nat) :
    sourceRunArithmetic input clock = sourceRun input clock := by
  change sourceRunWithDomains sourceArithmeticDomains input clock = _
  apply congrArg (fun domains => sourceRunWithDomains domains input clock)
  apply SourceDomains.eq_of_domains
  · funext a
    exact propext (ordinaryDomain_iff a).symm
  · funext a
    exact propext (sharedDomain_iff a).symm

theorem source_declarations_unique {σ : Type}
    (s : PanSemStateFiniteExact 64 σ) (ds : List (Pancake.PanLang.DeclHOL 64))
    (d₁ d₂ : DecidablePred s.memaddrs) (t₁ t₂ : PanSemStateFiniteExact 64 σ)
    (a : @evaluateDeclsHOLFinite 64 σ _ s d₁ ds = some t₁)
    (b : @evaluateDeclsHOLFinite 64 σ _ s d₂ ds = some t₂) : t₁ = t₂ := by
  have equal : d₁ = d₂ := Subsingleton.elim _ _
  subst d₂
  exact Option.some.inj (a.symm.trans b)

theorem sourceBehaviour_of_sourceRun (input : Guest.InputBlob) (clock : Nat)
    (event : HolFinalEvent) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : sourceRun input clock = some (some (.finalFfi event), post)) :
    sourceBehaviour input = .terminate (.ffiOutcome event) post.ffi.ioEvents := by
  classical
  unfold sourceRun sourceRunWithDomains at run
  split at run
  · cases run
  next context pre =>
    dsimp only at run
    split at run
    · cases run
    next entry decl =>
      have domains := @source_declarations_domains Guest.HostMemory
        (Guest.Software.guestAst.map Pancake.PanLang.declToHOL)
        { sourceInitialState input with structs := context } ordinaryDomainDecidable entry decl
      have reset : { entry with
          memaddrs := ordinaryDomain
          shMemaddrs := sharedDomain
          clock := clock } = { entry with clock := clock } := by
        have mem : entry.memaddrs = ordinaryDomain := domains.1
        have shared : entry.shMemaddrs = sharedDomain := domains.2
        rw [← mem, ← shared]
      have execution : evaluateHOLFiniteState { entry with clock := clock }
          (.call none (Basis.Pure.MlString.ofString "main") []) =
          (some (.finalFfi event), post) := by
        have pair := Option.some.inj run
        rw [← evaluateHOLFiniteState_eq_withDeciders] at pair
        exact (congrArg (fun state => evaluateHOLFiniteState state
          (.call none (Basis.Pure.MlString.ofString "main") [])) reset).symm.trans pair
      unfold sourceBehaviour semanticsDecls
      split
      · rename_i h
        rw [pre] at h
        cases h
      next context' pre' =>
        have equal : context = context' := Option.some.inj (pre.symm.trans pre')
        subst context'
        split
        · rename_i noDecl
          have same := congrArg (fun d : DecidablePred
              ({ sourceInitialState input with structs := context }).memaddrs =>
              @evaluateDeclsHOLFinite 64 Guest.HostMemory _
                { sourceInitialState input with structs := context } d
                (Guest.Software.guestAst.map Pancake.PanLang.declToHOL))
            (Subsingleton.elim ordinaryDomainDecidable
              (fun a => Classical.propDecidable _))
          have bad := decl.symm.trans (same.trans noDecl)
          cases bad
        next entry' decl' =>
          have equal := source_declarations_unique
            { sourceInitialState input with structs := context }
            (Guest.Software.guestAst.map Pancake.PanLang.declToHOL)
            ordinaryDomainDecidable (fun a => Classical.propDecidable _) entry entry' decl decl'
          subst entry'
          exact source_semantics_of_final_run entry _ clock event post execution

end InitE
