import InitE.SourceRun

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

/-- The fixed source domain excludes the lower scratch arena. This matters
when interpreting guest routines that allocate scratch below `sourceBase`. -/
theorem scratch_not_ordinaryDomain (a : BitVec 64) (below : a.toNat < scratchEnd) :
    ¬ ordinaryDomain a := by
  rw [ordinaryDomain_iff]
  simp only [scratchEnd] at below
  omega

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

def sourceArithmeticDomains : SourceDomains :=
  { ordinary := fun a => 2701131776 ≤ a.toNat ∧ a.toNat < 33806089704 ∧ a.toNat % 8 = 0
    shared := fun a => a.toNat % 8 = 0 ∧
      ((inputStart ≤ a.toNat ∧ a.toNat < inputEnd) ∨
        (outputStart ≤ a.toNat ∧ a.toNat < outputEnd))
    ordinaryDecider := fun _ => inferInstance
    sharedDecider := fun _ => inferInstance }

def sourceRun (input : Guest.InputBlob) (clock : Nat) :=
  sourceRunWithDomains sourceDomains input clock

/-- Arithmetic domain predicates avoid expanding the recursive address set
when the kernel checks a concrete interpreter computation. -/
def sourceRunArithmetic (input : Guest.InputBlob) (clock : Nat) :=
  sourceRunWithDomains sourceArithmeticDomains input clock

theorem sourceRunArithmetic_eq (input : Guest.InputBlob) (clock : Nat) :
    sourceRunArithmetic input clock = sourceRun input clock := by
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
