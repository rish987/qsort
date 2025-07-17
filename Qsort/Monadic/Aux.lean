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

def iteTargetTrans (id : TSyntax `ident) (tac : MVarId → Expr → TacticM α) (finish : α → MVarId → TacticM (List MVarId)) : TacticM Unit := do
  Lean.Elab.Term.withSynthesize <| withMainContext do
    let mut toMvarizeDecls : Array LocalDecl := #[]
    let mut toMvarizeFVars : Array Expr := #[]
    let target ← getMainTarget
    for decl in ← getLCtx do
      if let .cdecl .. := decl then
        if decl.userName == id.getId && target.containsFVar decl.fvarId then
          toMvarizeDecls := toMvarizeDecls.push decl
          toMvarizeFVars := toMvarizeFVars.push decl.toExpr
    let mut newMvars : Array Expr := #[]
    for decl in toMvarizeDecls do
      -- FIXME dependent types?
      let newMvar ← mkFreshExprMVar decl.type 
      newMvars := newMvars.push newMvar
    let newTarget := target.replaceFVars toMvarizeFVars newMvars
    let newGoal ← mkFreshExprMVar newTarget

    let r ← tac newGoal.mvarId! newTarget

    let assigned ← (newMvars.zip toMvarizeFVars).filterM fun (mvar, _) => mvar.mvarId!.isAssigned
    let unassigned ← (newMvars.zip toMvarizeFVars).filterM fun (mvar, _) => do pure <| not <| ← mvar.mvarId!.isAssigned
    for (mvar, fvar) in unassigned do
      let decl ← fvar.fvarId!.getDecl 
      mvar.mvarId!.assign fvar

    let rec makeBranches (rem : List (Expr × Expr)) (target : Expr) (allInst : Bool) (goal : MVarId) : TacticM (List MVarId) := goal.withContext do
      match rem with
      | (mvar, fvar) :: rem =>
        if not (← mvar.mvarId!.isAssigned) then
          -- ignore any mvars not assigned by the rewrite
          makeBranches rem target allInst goal
        else
          let assignment ← instantiateMVars mvar
          let targetInst := target.replaceFVar fvar assignment
          let targetNoInst := target

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
        if allInst then
          finish r goal
        else
          pure [goal]

    let newGoals ← makeBranches (newMvars.zip toMvarizeFVars).toList target true (← getMainGoal)
    -- trace[Meta.debug] s!"DBG[A]: Aux.lean:106: newGoals={newGoals.length}, {(← getGoals).length}"
    replaceMainGoal newGoals

syntax (name := iteRewriteSeq) "ite_rw" optConfig ident rwRuleSeq (location)? : tactic

def iteRewriteTarget (id : TSyntax `ident) (stx : Syntax) (symm : Bool) (config : Rewrite.Config := {}) : TacticM Unit := do
  let tac := fun newGoal newTarget => do
    let e ← elabTerm stx none true
    if e.hasSyntheticSorry then
      throwAbortTactic
    newGoal.rewrite newTarget e symm (config := config)
  let finish := fun r goal => do
    for mvarId in r.mvarIds do
      instantiateMVarDeclMVars mvarId
    let r := {r with eNew := (← instantiateMVars r.eNew), eqProof := (← instantiateMVars r.eqProof)}

    let mvarId' ← goal.replaceTargetEq (← instantiateMVars r.eNew) (← instantiateMVars r.eqProof)
    pure (mvarId' :: (r.mvarIds))
  iteTargetTrans id tac finish

@[tactic iteRewriteSeq] def evalIteRewriteSeq : Tactic := fun stx => do
  let cfg ← elabRewriteConfig stx[1]
  let id    := stx[2]
  let loc   := expandOptLocation stx[4]
  withRWRulesSeq stx[0] stx[3] fun symm term => do
    withLocation loc
      (rewriteLocalDecl term symm · cfg)
      (do
        iteRewriteTarget (.mk id) term symm cfg
      )
      (throwTacticEx `rewrite · "did not find instance of the pattern in the current goal")

syntax (name := iteAssumption) "ite_assumption" optConfig ident rwRuleSeq (location)? : tactic

@[tactic iteAssumption] def evalIteAssumption : Tactic := fun stx => do
  sorry
