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

syntax (name := existsMvar) "exists?" : tactic

def evalApplyLikeTactic (tac : MVarId → Expr → MetaM (List MVarId)) (e : Expr) : TacticM Unit := do
  withMainContext do
    let mut val ← instantiateMVars e
    if val.isMVar then
      Term.synthesizeSyntheticMVarsNoPostponing
      val ← instantiateMVars val
    let mvarIds' ← tac (← getMainGoal) val
    Term.synthesizeSyntheticMVarsNoPostponing
    replaceMainGoal mvarIds'

@[tactic existsMvar] def evalExistsMvar : Tactic := fun _ => do
  let target ← getMainTarget
  if let (.const ``Exists [u]) := target.getAppFn then
    let type := target.getAppArgs[0]!
    let pred := target.getAppArgs[1]!
    let newMvar ← mkFreshExprMVar type 

    let e := (mkAppN (.const ``Exists.intro [u]) #[type, pred, newMvar])
    evalApplyLikeTactic (·.apply) e
    modify fun s => { goals := s.goals.filter (· != newMvar.mvarId!)}
  else
    throwError "expected Exists application in goal, got {indentExpr target}"
