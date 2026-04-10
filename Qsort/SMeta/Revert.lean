import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Util
import Lean.Meta.Diagnostics
import Lean.Meta.Tactic.Refl
import Lean.Elab.Binders
import Lean.Elab.Open
import Lean.Elab.Eval
import Lean.Elab.SetOption
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Do

open Lean.Meta
namespace Lean.SMeta

def duplicateMVar (m : MVarId) : MetaM MVarId := do
  let d ← m.getDecl
  let e ← mkFreshExprMVarAt d.lctx d.localInstances d.type d.kind d.userName d.numScopeArgs
  return e.mvarId!

def _root_.Lean.MVarId.redexExpand (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId := do
  let d ← mvarId.getDecl
  let newType := mkApp (← mkLambdaFVars #[.fvar fvarId] d.type) (.fvar fvarId)
  let e ← mkFreshExprMVarAt d.lctx d.localInstances newType d.kind d.userName d.numScopeArgs
  mvarId.assign e
  return e.mvarId!

/--
Revert all forward dependencies of the free variable `fvarId` at goal `mvarId` that appear in the goal type.
-/
def _root_.Lean.MVarId.revertForwardDepsInGoal (mvarId : MVarId) (fvarId : FVarId) (preserveOrder : Bool := false)
    (clearAuxDeclsInsteadOfRevert := false) : MetaM (Array FVarId × MVarId) := do
  mvarId.withContext do
    mvarId.checkNotAssigned `revert
    unless clearAuxDeclsInsteadOfRevert do
      if (← fvarId.getDecl) |>.isAuxDecl then
        throwError "Failed to revert `{mkFVar fvarId}`: It is an auxiliary declaration created to \
          represent a recursive reference to an in-progress definition"
    let fvar := mkFVar fvarId
    let toRevert ← collectForwardDeps #[fvar] preserveOrder
    /- We should clear any `auxDecl` in `toRevert` -/
    let mut mvarId      := mvarId
    let mut toRevertNew := #[]
    for x in toRevert do
      if (← x.fvarId!.getDecl).isAuxDecl then
        mvarId ← mvarId.clear x.fvarId!
      else
        toRevertNew := toRevertNew.push x
    let type ← mvarId.getType
    toRevertNew := toRevertNew.filter fun fv => fv.fvarId! != fvarId
    toRevertNew := toRevertNew.filter fun fv => type.containsFVar fv.fvarId!
    let tag ← mvarId.getTag
    -- TODO: the following code can be optimized because `MetavarContext.revert` will compute `collectDeps` again.
    -- We should factor out the relevant part

    -- Set metavariable kind to natural to make sure `revert` will assign it.
    mvarId.setKind .natural
    let (e, toRevert) ←
      try
        liftMkBindingM <| MetavarContext.revert toRevertNew mvarId preserveOrder
      finally
        mvarId.setKind .syntheticOpaque
    let mvar := e.getAppFn
    mvar.mvarId!.setKind .syntheticOpaque
    mvar.mvarId!.setTag tag
    let newMvarId ← mvar.mvarId!.redexExpand fvarId
    return (toRevert.map Expr.fvarId!, newMvarId)
end Lean.SMeta

namespace Lean.Parser.Tactic
syntax (name := srevert) "srevert" (ppSpace colGt term:max) : tactic
end Lean.Parser.Tactic

namespace Lean.Elab.Tactic
open Meta
open Parser.Tactic

@[tactic Lean.Parser.Tactic.srevert] def evalSRevert : Tactic := fun stx =>
  match stx with
  | `(tactic| srevert $hs) => do
     let (_, mvarId) ← (← getMainGoal).revertForwardDepsInGoal (← getFVarIds #[hs])[0]!
     replaceMainGoal [mvarId]
  | _                     => throwUnsupportedSyntax
