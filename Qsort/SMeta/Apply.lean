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
/--
  Compute the number of expected arguments and whether the result type is of the form
  (?m ...) where ?m is an unassigned metavariable.
-/
def getExpectedNumArgsAux (e : Expr) : MetaM (Nat × Bool) :=
  withDefault <| forallTelescopeReducing e fun xs body =>
    pure (xs.size, body.getAppFn.isMVar)

def getExpectedNumArgs (e : Expr) : MetaM Nat := do
  let (numArgs, _) ← getExpectedNumArgsAux e
  pure numArgs

private def throwApplyError {α} (mvarId : MVarId)
    (eType : Expr) (conclusionType? : Option Expr) (targetType : Expr)
    (term? : Option MessageData) : MetaM α := do
  throwTacticEx `apply mvarId <| MessageData.ofLazyM (es := #[eType, targetType]) do
    let conclusionType := conclusionType?.getD eType
    let note := if conclusionType?.isSome then .note m!"The full type of {term?.getD "the term"} is{indentExpr eType}" else m!""
    let (conclusionType, targetType) ← addPPExplicitToExposeDiff conclusionType targetType
    let conclusion := if conclusionType?.isNone then "type" else "conclusion"
    return m!"could not unify the {conclusion} of {term?.getD "the term"}{indentExpr conclusionType}\n\
      with the goal{indentExpr targetType}{note}{← mkUnfoldAxiomsNote conclusionType targetType}"

def synthAppInstances (tacticName : Name) (mvarId : MVarId) (mvarsNew : Array Expr) (binderInfos : Array BinderInfo)
    (synthAssignedInstances : Bool) (allowSynthFailures : Bool) : MetaM Unit := do
  let mut todo := #[]
  -- Collect metavariables to synthesize
  for mvar in mvarsNew, binderInfo in binderInfos do
    if binderInfo.isInstImplicit then
      if synthAssignedInstances || !(← mvar.mvarId!.isAssigned) then
        todo := todo.push mvar
  while !todo.isEmpty do
    todo ← step todo
where
  /--
  Try to synthesize instances for the metavariables `mvars`.
  Returns metavariables that still need to be synthesized.
  We can view the resulting array as the set of metavariables that we should try again.
  This is needed when applying or rewriting with functions with complex instances.
  For example, consider `rw [@map_smul]` where `map_smul` is
  ```
  map_smul {F : Type u_1} {M : Type u_2} {N : Type u_3} {φ : M → N}
           {X : Type u_4} {Y : Type u_5}
           [SMul M X] [SMul N Y] [FunLike F X Y] [MulActionSemiHomClass F φ X Y]
           (f : F) (c : M) (x : X) : DFunLike.coe f (c • x) = φ c • DFunLike.coe f x
  ```
  and `MulActionSemiHomClass` is defined as
  ```
  class MulActionSemiHomClass (F : Type _)
     {M N : outParam (Type _)} (φ : outParam (M → N))
     (X Y : outParam (Type _)) [SMul M X] [SMul N Y] [FunLike F X Y] : Prop where
  ```
  The left-hand-side of the equation does not bind `N`. Thus, `SMul N Y` cannot
  be synthesized until we synthesize `MulActionSemiHomClass F φ X Y`. Note that
  `N` is an output parameter for `MulActionSemiHomClass`.
  -/
  step (mvars : Array Expr) : MetaM (Array Expr) := do
    -- `ex?` stores the exception for this first synthesis failure in this step.
    let mut ex? := none
    -- `true` if we managed to synthesize an instance after we hit a failure.
    -- That is, there is a chance we may succeed if we try again.
    let mut progressAfterEx := false
    -- Metavariables that we failed to synthesize.
    let mut postponed := #[]
    for mvar in mvars do
      let mvarType ← inferType mvar
      let mvarVal? ← try
        let mvarVal ← synthInstance mvarType
        unless postponed.isEmpty do
          progressAfterEx := true
        pure (some mvarVal)
      catch ex =>
        ex? := some ex
        postponed := postponed.push mvar
        pure none
      if let some mvarVal := mvarVal? then
        unless (← isDefEq mvar mvarVal) do
          -- There is no point in trying again for this kind of failure
          unless allowSynthFailures do
            throwTacticEx tacticName mvarId "failed to assign synthesized instance"
    if let some ex := ex? then
      if progressAfterEx then
        return postponed
      else
        -- There is no point in running `step` again. We should give up (`allowSynthFailures`),
        -- or throw the first exception we found in this `step`.
        if allowSynthFailures then return #[] else throw ex
    else
      -- Done. We successfully synthesized all metavariables.
      return #[]

def appendParentTag (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) : MetaM Unit := do
  let parentTag ← mvarId.getTag
  if newMVars.size == 1 then
    -- if there is only one subgoal, we inherit the parent tag
    newMVars[0]!.mvarId!.setTag parentTag
  else
    unless parentTag.isAnonymous do
      newMVars.size.forM fun i _ => do
        let mvarIdNew := newMVars[i].mvarId!
        unless (← mvarIdNew.isAssigned) do
          unless binderInfos[i]!.isInstImplicit do
            let currTag ← mvarIdNew.getTag
            mvarIdNew.setTag (appendTag parentTag currTag)

/--
If `synthAssignedInstances` is `true`, then `apply` will synthesize instance implicit arguments
even if they have assigned by `isDefEq`, and then check whether the synthesized value matches the
one inferred. The `congr` tactic sets this flag to false.
-/
def postprocessAppMVars (tacticName : Name) (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo)
    (synthAssignedInstances := true) (allowSynthFailures := false) : MetaM Unit := do
  synthAppInstances tacticName mvarId newMVars binderInfos synthAssignedInstances allowSynthFailures
  -- TODO: default and auto params
  appendParentTag mvarId newMVars binderInfos

private def dependsOnOthers (mvar : Expr) (otherMVars : Array Expr) : MetaM Bool :=
  otherMVars.anyM fun otherMVar => do
    if mvar == otherMVar then
      return false
    else
      let otherMVarType ← inferType otherMVar
      return (otherMVarType.findMVar? fun mvarId => mvarId == mvar.mvarId!).isSome

/-- Partitions the given mvars in to two arrays (non-deps, deps)
according to whether the given mvar depends on other mvars in the array.-/
private def partitionDependentMVars (mvars : Array Expr) : MetaM (Array MVarId × Array MVarId) :=
  mvars.foldlM (init := (#[], #[])) fun (nonDeps, deps) mvar => do
    let currMVarId := mvar.mvarId!
    if (← dependsOnOthers mvar mvars) then
      return (nonDeps, deps.push currMVarId)
    else
      return (nonDeps.push currMVarId, deps)

private def reorderGoals (mvars : Array Expr) : ApplyNewGoals → MetaM (List MVarId)
  | ApplyNewGoals.nonDependentFirst => do
      let (nonDeps, deps) ← partitionDependentMVars mvars
      return nonDeps.toList ++ deps.toList
  | ApplyNewGoals.nonDependentOnly => do
      let (nonDeps, _) ← partitionDependentMVars mvars
      return nonDeps.toList
  | ApplyNewGoals.all => return mvars.toList.map Lean.Expr.mvarId!

/-- Custom `isDefEq` for the `apply` tactic -/
private def isDefEqApply (approx : Bool) (a b : Expr) : MetaM Bool := do
  if approx then
    approxDefEq <| isDefEqGuarded a b
  else
    isDefEqGuarded a b

def _root_.Lean.MVarId.sapply (mvarId : MVarId) (e : Expr) (cfg : ApplyConfig := {})
    (term? : Option MessageData := none) : MetaM (List MVarId) :=
  mvarId.withContext do
    trace[Meta.isDefEq] m!"sapply {e}"
    mvarId.checkNotAssigned `sapply
    let targetType ← mvarId.getType
    let eType      ← inferType e
    let (numArgs, _) ← getExpectedNumArgsAux eType
    trace[Meta.isDefEq] m!"sapply 2"
    -- unless hasMVarHead do
    --   throwTacticEx `sapply mvarId m!"expected metavariable head in conclusion type {eType}"
    -- trace[Meta.isDefEq] m!"apply: {hasMVarHead}, {rangeNumArgs.toList}, {targetType}"
    let rec go : MetaM (Array Expr × Array BinderInfo) := do
      trace[Meta.isDefEq] m!"sapply 3"
      let s ← saveState
      let (newMVars, binderInfos, eType) ← forallMetaTelescopeReducing eType numArgs
      trace[Meta.isDefEq] m!"sapply 4"
      let eHead := eType.getAppFn
      let targHead := targetType.getAppFn
      let eArgs := eType.getAppArgs
      let targArgs := targetType.getAppArgs
      trace[Meta.isDefEq] m!"sapply 5"
      unless eArgs.size == targArgs.size do
        throwTacticEx `sapply mvarId "expected conclusion type and target type to have same number of arguments"
      trace[Meta.isDefEq] m!"sapply 6"
      let fail := do
        s.restore
        let conclusionType? ← if numArgs = 0 then
          pure none
        else
          let (_, _, r) ← forallMetaTelescopeReducing eType (some numArgs)
          pure (some r)
        throwApplyError mvarId eType conclusionType? targetType term?
      trace[Meta.isDefEq] m!"sapply 7"

      trace[Meta.isDefEq] m!"checking {eHead} =?= {targHead}"
      unless (← isDefEq eHead targHead) do fail
      trace[Meta.isDefEq] m!"checked {eHead} =?= {targHead}"

      for (eArg, targArg) in eArgs.zip targArgs do
        trace[Meta.isDefEq] m!"checking arg {eArg} =?= {targArg}"
        unless (← isDefEq eArg targArg) do fail
        trace[Meta.isDefEq] m!"checked arg {eArg} =?= {targArg}"

      return (newMVars, binderInfos)
    let (newMVars, binderInfos) ← go
    postprocessAppMVars `sapply mvarId newMVars binderInfos cfg.synthAssignedInstances cfg.allowSynthFailures
    let e ← instantiateMVars e
    mvarId.assign (mkAppN e newMVars)
    let newMVars ← newMVars.filterM fun mvar => not <$> mvar.mvarId!.isAssigned
    let otherMVarIds ← getMVarsNoDelayed e
    let newMVarIds ← reorderGoals newMVars cfg.newGoals
    let otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    result.forM (·.headBetaType)
    return result

def _root_.Lean.MVarId.smapply (mvarId : MVarId) (e : Expr) (cfg : ApplyConfig := {})
    (term? : Option MessageData := none) : MetaM (List MVarId) :=
  mvarId.withContext do
    trace[Meta.isDefEq] m!"smapply {e}"
    mvarId.checkNotAssigned `smapply
    let targetType ← mvarId.getType
    let eType      ← inferType e
    let (numArgs, _) ← getExpectedNumArgsAux eType
    trace[Meta.isDefEq] m!"smapply 2"
    let rec go : MetaM (Array Expr × Array BinderInfo) := do
      trace[Meta.isDefEq] m!"smapply 3"
      let s ← saveState
      let (newMVars, binderInfos, eType) ← forallMetaTelescopeReducing eType numArgs
      trace[Meta.isDefEq] m!"smapply 4"
      let newMvarId ← mvarId.assert default eType (mkAppN e newMVars)
      let (_, newMvarId) ← newMvarId.intro1 default
      return (newMVars.insertIdx 0 (Expr.mvar newMvarId), binderInfos)
    let (newMVars, binderInfos) ← go
    postprocessAppMVars `smapply mvarId newMVars binderInfos cfg.synthAssignedInstances cfg.allowSynthFailures
    let e ← instantiateMVars e
    mvarId.assign (mkAppN e newMVars)
    let newMVars ← newMVars.filterM fun mvar => not <$> mvar.mvarId!.isAssigned
    let otherMVarIds ← getMVarsNoDelayed e
    let newMVarIds ← reorderGoals newMVars cfg.newGoals
    let otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    result.forM (·.headBetaType)
    return result

end Lean.SMeta

namespace Lean.Parser.Tactic
syntax (name := sapply) "sapply " term : tactic
syntax (name := smapply) "smapply " term : tactic
end Lean.Parser.Tactic

namespace Lean.Elab.Tactic
open Meta
open Parser.Tactic

@[tactic Lean.Parser.Tactic.sapply] def evalSApply : Tactic := fun stx =>
  match stx with
  | `(tactic| sapply $t) => evalApplyLikeTactic (fun g e =>
      withConfig (fun ctx => {ctx with constApprox := true}) do
        g.sapply e (term? := some m!"`{e}`"
    )) t
  | _ => throwUnsupportedSyntax

@[tactic Lean.Parser.Tactic.smapply] def evalSMApply : Tactic := fun stx =>
  match stx with
  | `(tactic| smapply $t) => evalApplyLikeTactic (fun g e =>
      withConfig (fun ctx => {ctx with constApprox := true}) do
        g.smapply e (term? := some m!"`{e}`"
    )) t
  | _ => throwUnsupportedSyntax
