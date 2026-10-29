import Lean
import InitE.SourceComputation
import InitE.NameComputation

/-! Keep program syntax suspended until the evaluator inspects its outer
constructor. Each rule is reflexivity and changes evaluation strategy only. -/
namespace InitE.SourceReduction
open Lean Meta Sym Meta.Tactic.Cbv

scoped cbv_simproc ↓ holdUpdate (@Flapjack.FUPDATE _ _ _ _ _) :=
  fun e => return .rfl (done := e.getAppNumArgs == 5)

theorem update_apply {α β : Type} [BEq α] (f : α → Option β)
    (entry : α × β) (key : α) :
    Flapjack.FUPDATE f entry key = if entry.1 == key then some entry.2 else f key := rfl

attribute [scoped cbv_eval] update_apply

scoped cbv_simproc ↓ holdFunDecl (@Flapjack.FunDecl.mk _ _ _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holdHOLFunDecl (@Flapjack.Pancake.PanLang.FunDeclHOL.mk _ _ _ _ _ _ _ _) :=
  fun _ => return .rfl (done := true)

scoped cbv_simproc ↓ sourceSkip (@Flapjack.Prog.skip _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceDec (@Flapjack.Prog.dec _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceAssign (@Flapjack.Prog.assign _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourcePrimitive (@Flapjack.Prog.primitive _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceStore (@Flapjack.Prog.store _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceStore32 (@Flapjack.Prog.store32 _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceStoreByte (@Flapjack.Prog.storeByte _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceSeq (@Flapjack.Prog.seq _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceIte (@Flapjack.Prog.ite _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceWhile (@Flapjack.Prog.while _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceBreak (@Flapjack.Prog.break _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceContinue (@Flapjack.Prog.continue _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceCall (@Flapjack.Prog.call _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceDecCall (@Flapjack.Prog.decCall _ _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceExtCall (@Flapjack.Prog.extCall _ _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceRaise (@Flapjack.Prog.raise _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceReturn (@Flapjack.Prog.return _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceShMemLoad (@Flapjack.Prog.shMemLoad _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceShMemStore (@Flapjack.Prog.shMemStore _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceTick (@Flapjack.Prog.tick _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ sourceAnnot (@Flapjack.Prog.annot _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holSkip (@Flapjack.Pancake.PanLang.ProgHOL.skip _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holDec (@Flapjack.Pancake.PanLang.ProgHOL.dec _ _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holAssign (@Flapjack.Pancake.PanLang.ProgHOL.assign _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holPrimitive (@Flapjack.Pancake.PanLang.ProgHOL.primitive _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holStore (@Flapjack.Pancake.PanLang.ProgHOL.store _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holStore32 (@Flapjack.Pancake.PanLang.ProgHOL.store32 _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holStoreByte (@Flapjack.Pancake.PanLang.ProgHOL.storeByte _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holSeq (@Flapjack.Pancake.PanLang.ProgHOL.seq _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holIte (@Flapjack.Pancake.PanLang.ProgHOL.ite _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holWhile (@Flapjack.Pancake.PanLang.ProgHOL.while _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holBreak (@Flapjack.Pancake.PanLang.ProgHOL.break _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holContinue (@Flapjack.Pancake.PanLang.ProgHOL.continue _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holCall (@Flapjack.Pancake.PanLang.ProgHOL.call _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holDecCall (@Flapjack.Pancake.PanLang.ProgHOL.decCall _ _ _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holExtCall (@Flapjack.Pancake.PanLang.ProgHOL.extCall _ _ _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holRaise (@Flapjack.Pancake.PanLang.ProgHOL.raise _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holReturn (@Flapjack.Pancake.PanLang.ProgHOL.return _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holShMemLoad (@Flapjack.Pancake.PanLang.ProgHOL.shMemLoad _ _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holShMemStore (@Flapjack.Pancake.PanLang.ProgHOL.shMemStore _ _ _ _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holTick (@Flapjack.Pancake.PanLang.ProgHOL.tick _ _) :=
  fun _ => return .rfl (done := true)
scoped cbv_simproc ↓ holAnnot (@Flapjack.Pancake.PanLang.ProgHOL.annot _ _ _ _) :=
  fun _ => return .rfl (done := true)

end InitE.SourceReduction
