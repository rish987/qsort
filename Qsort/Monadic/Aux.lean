import Qsort.Monadic.Simp
import Std.Tactic.Do
import Init.Tactics
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Meta
import Lean.Elab.Tactic.Rewrite
import Lean.Elab.SyntheticMVars

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Tactic
open Lean.Parser.Tactic

open Std.Do

attribute [spred] SPred.and_cons SVal.curry_cons SVal.curry_nil SVal.uncurry_cons SVal.uncurry_nil SPred.and_nil

macro "mvcgen_aux" : tactic => do
  `(tactic|
    (repeat mintro ∀_ -- FIXME use better names
     try mframe
     mpure_intro
     simp only [spred] at *))

macro "omegas" : tactic => do
  `(tactic|
    (all_goals try omega))

def iteTargetTrans (id : TSyntax `ident) (tac : Syntax) : TacticM Unit := do
  Lean.Elab.Term.withSynthesize <| withMainContext do
    let mut toMvarizeDecls : Array LocalDecl := #[]
    let mut toMvarizeFVars : Array Expr := #[]
    let target ← getMainTarget
    let ctx ← getLCtx
    for decl in ← getLCtx do
      if let .cdecl .. := decl then
        if decl.userName == id.getId && (target.containsFVar decl.fvarId || ctx.containsFVar decl.toExpr) then
          toMvarizeDecls := toMvarizeDecls.push decl
          toMvarizeFVars := toMvarizeFVars.push decl.toExpr
    let mut newMvars : Array Expr := #[]
    for decl in toMvarizeDecls do
      -- FIXME dependent types?
      let newMvar ← mkFreshExprMVar decl.type 
      newMvars := newMvars.push newMvar
    let newTarget := target.replaceFVars toMvarizeFVars newMvars
    let mut newCtx := ctx
    for (fvar, newMvar) in toMvarizeFVars.zip newMvars do
      newCtx := newCtx.replaceFVarId fvar.fvarId! newMvar
    let newGoal ← withLCtx' newCtx $ mkFreshExprMVar newTarget

    pushGoal newGoal.mvarId!
    focus do
      evalTactic tac
      while (← getGoals).length > 0 do
        discard popMainGoal

    let rec makeBranches (rem : List (Expr × Expr)) (target : Expr) (allInst : Bool) (goal : MVarId) : TacticM (List MVarId) := goal.withContext do
      match rem with
      | (mvar, fvar) :: rem =>
        if not (← mvar.mvarId!.isAssigned) then
          -- ignore any mvars not assigned by the rewrite
          makeBranches rem target allInst goal
        else
          let assignment ← instantiateMVars mvar

          let T ← inferType fvar
          let α ← goal.getType
          let u ← getLevel α
          let v ← getLevel T
          let c := Lean.mkAppN (.const ``Eq [v]) #[T, assignment, fvar]
          let nc := Lean.mkApp (.const ``Not []) c
          let h ← synthInstance (Lean.mkApp (.const ``Decidable []) c)
          let (t, tGoals) ← withLocalDeclD `h c fun h => do
            let tMvar ← mkFreshExprSyntheticOpaqueMVar α
            let tGoal ← subst tMvar.mvarId! h.fvarId!
            let tGoals ← makeBranches rem (← tGoal.getType) allInst tGoal
            pure (← mkLambdaFVars #[h] (← instantiateMVars tMvar), tGoals)
          let (e, eGoals) ← withLocalDeclD `h nc fun h => do
            let eMvar ← mkFreshExprSyntheticOpaqueMVar α
            let eGoal := eMvar.mvarId!
            let eGoals ← makeBranches rem (← eGoal.getType) false eGoal
            pure (← mkLambdaFVars #[h] (← instantiateMVars eMvar), eGoals)
          let prf := Lean.mkAppN (.const ``dite [u]) #[α, c, h, t, e]
          goal.assign prf
          pure (tGoals ++ eGoals)
      | [] =>
        pure [goal]

    -- trace[Meta.debug] s!"DBG[A]: Aux.lean:106: newGoals={(← getGoals).length}"
    let newGoals ← makeBranches (newMvars.zip toMvarizeFVars).toList target true (← getMainGoal)
    replaceMainGoal newGoals
    evalTactic tac

syntax (name := iteTrans) "ite" ident tacticSeq : tactic

@[tactic iteTrans] def evalIteTrans : Tactic := fun stx => do
  let id    := stx[1]
  let tac   := stx[2]
  iteTargetTrans (.mk id) tac

syntax (name := existsMvar) "exists?" ident : tactic

def evalApplyLikeTactic (tac : MVarId → Expr → MetaM (List MVarId)) (e : Expr) : TacticM Unit := do
  withMainContext do
    let mut val ← instantiateMVars e
    if val.isMVar then
      Term.synthesizeSyntheticMVarsNoPostponing
      val ← instantiateMVars val
    let mvarIds' ← tac (← getMainGoal) val
    Term.synthesizeSyntheticMVarsNoPostponing
    replaceMainGoal mvarIds'

@[tactic existsMvar] def evalExistsMvar : Tactic := fun stx => do
  let id : Name := (TSyntax.mk stx[1]).getId
  let target ← getMainTarget
  if let (.const ``Exists [u]) := target.getAppFn then
    let type := target.getAppArgs[0]!
    let pred := target.getAppArgs[1]!
    let newMvar ← mkFreshExprMVar type (userName := id)

    let e := (mkAppN (.const ``Exists.intro [u]) #[type, pred, newMvar])
    evalApplyLikeTactic (·.apply) e
    modify fun s => { goals := s.goals.filter (· != newMvar.mvarId!)}
  else
    throwError "expected Exists application in goal, got {indentExpr target}"

syntax (name := inst) "inst" ident tacticSeq : tactic

syntax (name := inst') "inst'" ident tacticSeq : tactic

-- marker for "hole parameters"
abbrev HP : Sort u → Sort u := id

 def runInst (id : Name) (tac : TacticM Unit) (rerun : Bool): TacticM Unit := withMainContext $ Tactic.focus do
  let mctx := ← getMCtx
  let some mvar := mctx.findUserName? id | throwError "could not find '{id}' in metavariable context"
  let rec countHPs (e : Expr) (n : Nat) := do
    match e with
    | .forallE _ d b _ =>
      if d.isAppOf ``HP then
        countHPs b (n + 1)
      else
        pure n
    | _ => 
      pure n
  let type ← mvar.getType
  let numHPs ← countHPs type 0
  let lctx ← getLCtx
  let target ← getMainTarget

  let tryReplace decl := do
    let mut ret := false
    if decl.type.hasMVar then
      ret := true
    else if let some val := decl.value? then
      if val.hasMVar then
        ret := true
    pure ret

  let mut mvarApp? := none

  let getMVarApp? (e : Expr) : Option Expr := do
    e.find? fun sube =>
      if let .mvar id .. := sube.getAppFn then
        if id == mvar then
          if sube.getAppArgs.size == numHPs then
            true
          else
            false
        else
          false
      else
        false

  for decl in lctx do
    unless ← tryReplace decl do continue
    match decl with
      | .cdecl i fv n t b k =>
        if let some mvarApp := getMVarApp? t then
          mvarApp? := some mvarApp
          break
      | .ldecl i fv n t v b k =>
        if let some mvarApp := getMVarApp? t then
          mvarApp? := some mvarApp
          break
        if let some mvarApp := getMVarApp? v then
          mvarApp? := some mvarApp
          break
  if mvarApp?.isNone then
    mvarApp? := getMVarApp? target

  let some mvarApp := mvarApp? | throwError "no instance of `{Expr.mvar mvar} [{numHPs} args]` found in proof state"
  let mvarAppArgs := mvarApp.getAppArgs

  let newMvar ← mkFreshExprMVar (← inferType mvarApp)
  let newMvarLam ← forallBoundedTelescope (← mvar.getType) numHPs fun vs _ => do
    mkLambdaFVars vs newMvar
  let rep e :=
    e.replace fun e =>
      if let .mvar id .. := e then
        if id == mvar then
          newMvarLam
        else
          none
      else
        none
  let mut newCtx := (← getLCtx)
  for decl in lctx do
    unless ← tryReplace decl do continue
    let newDecl : LocalDecl := match decl with
      | .cdecl i fv n t b k =>
        .cdecl i fv n (rep t) b k
      | .ldecl i fv n t v b k =>
        .ldecl i fv n (rep t) (rep v) b k
    -- trace[Meta.debug] s!"DBG[39]: Aux.lean:185 {← ppExpr newDecl.type}"
    newCtx := newCtx.modifyLocalDecl newDecl.fvarId fun _ => newDecl
  let newTarget := rep target
  let newGoal ← withLCtx' newCtx $ mkFreshExprMVar newTarget

  let state ← saveState
  pushGoal newGoal.mvarId!
  Tactic.focus do
    tac
    while (← getGoals).length > 0 do
      discard popMainGoal

  unless (← newMvar.mvarId!.isAssigned) do throwError "failed to assign `{mvar}` through unification"
  let assignment ← instantiateMVars newMvar
  state.restore

  forallBoundedTelescope (← mvar.getType) numHPs fun vs _ => do
    let mut absAssignment := assignment
    for (arg, fvar) in mvarAppArgs.zip vs do
      absAssignment := absAssignment.replace fun e =>
        if e == arg then
          fvar
        else none
    let val ← mkLambdaFVars vs absAssignment
    try
      mvar.assign val
    catch _ =>
      throwError  "assignment `{mvar} := {← ppExpr val}` failed (from application {mvarAppArgs})"
  if rerun then
    tac

@[tactic inst] def evalInst : Tactic := fun stx => withMainContext $ Tactic.focus do
  let id : Name := (TSyntax.mk stx[1]).getId
  let tac   := stx[2]
  runInst id (evalTactic tac) true

@[tactic inst'] def evalInst' : Tactic := fun stx => withMainContext $ Tactic.focus do
  let id : Name := (TSyntax.mk stx[1]).getId
  let tac   := stx[2]
  runInst id (evalTactic tac) false

/-- Return the `n`th local declaration whose type is definitionally equal to `type`. -/
def findNthLocalDeclWithType? (type : Expr) (n : Nat) : StateRefT Nat MetaM (Option FVarId) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else
      let state ← saveState
      if (← isDefEq type localDecl.type) then
        if (← get) == n then
          trace[Meta.debug] s!"success"
          return some localDecl.fvarId
        state.restore
        modify fun n => n + 1
        return none
      return none

def _root_.Lean.MVarId.nthassumptionCore (mvarId : MVarId) (n : Nat) : MetaM Bool :=
  mvarId.withContext do
    mvarId.checkNotAssigned `nthassumption
    match (← findNthLocalDeclWithType? (← mvarId.getType) n |>.run 1).1 with
    | none => return false
    | some fvarId => mvarId.assign (mkFVar fvarId); return true

def _root_.Lean.MVarId.nthassumption (mvarId : MVarId) (n : Nat) : MetaM Unit :=
  unless (← mvarId.nthassumptionCore n) do
    throwTacticEx `nthassumption mvarId

syntax (name := nthassumption) "nthassumption" ident num : tactic

@[tactic nthassumption] def evalNthAssumption : Tactic := fun stx => do
  let id := (TSyntax.mk stx[1]).getId
  let n := (TSyntax.mk stx[2]).getNat
  let tac := liftMetaTactic fun mvarId => withAssignableSyntheticOpaque do mvarId.nthassumption n; pure []
  runInst id tac false
  liftMetaTactic fun mvarId => withAssignableSyntheticOpaque do mvarId.assumption; pure []
