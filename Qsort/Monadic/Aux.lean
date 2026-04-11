import Qsort.Monadic.Simp
import Qsort.Monadic.MVarDeps
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
open Lean.Parser.Term

open Std.Do

attribute [spred] SPred.and_cons SVal.curry_cons SVal.curry_nil SVal.uncurry_cons SVal.uncurry_nil SPred.and_nil SPred.down_pure
attribute [lists] List.length_append List.length_cons List.length_nil List.length_range'
attribute [arith] Nat.add_one_sub_one Nat.div_one Nat.zero_add Nat.add_one_sub_one Nat.le_refl Nat.Simproc.add_sub_add_ge Nat.sub_self Nat.add_zero

macro "mvcgen_aux" : tactic => do
  `(tactic|
    (repeat mintro ∀_ -- FIXME use better names
     try mframe
     mpure_intro
     simp only [spred] at *))

macro "omegas" : tactic => do
  `(tactic|
    (all_goals try omega
     all_goals try trivial
     all_goals try assumption))

macro "sorries" : tactic => do
  `(tactic|
    (all_goals try sorry))

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

/--
`ite var tac` works as follows
1. We replace `var` in the proof state with a fresh metavariable `?mvar`.
2. `tac` is run in this new proof state, and we ensure that it succeeds
   and assigns `?mvar := t`.
3. We revert to the original proof state and create a `dite` branch with
   the conditional `var = t`, creating two subgoals for the `then` and `else` cases.
4. In the `then` branch with hypothesis `h : var = t`, we call `subst h` and
   then run `tac` (again).

This leaves us with two goals, one corresponding to the result of running `tac`
where we assume `var = t` and substitute accordingly, and another where we assume `¬ var = t`.
-/
syntax (name := iteTrans) "ite" ident tacticSeq : tactic

@[tactic iteTrans] def evalIteTrans : Tactic := fun stx => do
  let id    := stx[1]
  let tac   := stx[2]
  iteTargetTrans (.mk id) tac

/--
Given an existential goal `∃ x : T, P x`, `exists? mvar` will
create a new metavariable `?mvar : T` which is provided as the existential witness,
leaving us with the goal `P ?mvar`.
`?mvar` can then be assigned via unification during the proof.

Example:
```
def f (x : Nat) : Id Nat := do
  pure x

theorem f_spec : 
    ∃ x,
   ⦃⌜True⌝⦄
   f x
   ⦃⇓ r => ⌜r = 0⌝⦄ := by
  exists? mvar1
  mintro -
  unfold f
  simp
  rfl -- assigns `?mvar1 = 0`
```
-/
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

syntax (name := mkMVar) "mvar" ident typeSpec : tactic

@[tactic mkMVar] def evalMkMvar : Tactic := fun stx => do
  let id : Name := (TSyntax.mk stx[1]).getId
  let typStx : Syntax := (stx[2][1])
  let type ← elabTerm typStx none -- | throwError "failed to elaborate mvar type: {typStx}"
  let newMvar ← mkFreshExprMVar type (userName := id)

/--
If `?mvar : HP U1 -> ... -> HP Un -> V`, `inst mvar tac` tries to intelligently assign
`?mvar` based on the unification result of running `tac`. It works as follows:

1. Any instances of `?mvar` are replaced by the constant function `fun u1 ... un => ?newMvar`, for some fresh metavar `?newMvar`.
2. The tactic `tac` is run. If `?newMvar` is assigned to some value `t`, continue, otherwise fail.
3. The proof state is reverted to what it was before (1).
4. We search for `?mvar` in the original proof state, finding an instance with `n` arguments `a1 ... an`.
5. We abstract `a1 ... an` out of `t` to construct a lambda expression `f`.
6. We assign `?mvar := f` and rerun `tac`.

Example:
```
def g (x : HP Nat → Nat) (a : Nat) : Id Nat := do
  pure (x a)

theorem g_spec (a : Nat) :
    ∃ x,
   ⦃⌜a > 0⌝⦄
   g x a
   ⦃⇓ r => ⌜r > 0⌝⦄ := by
  exists? mvar1
  mvcgen [g]
  mleave
  inst mvar1 assumption -- assigns `?mvar1 = fun a => a`
```
-/
syntax (name := inst) "inst" ident tacticSeq : tactic

syntax (name := inst') "inst'" ident tacticSeq : tactic

-- marker for "hole parameters"
abbrev HP : Sort u → Sort u := id

-- marker for "hole parameter products"
abbrev HPP : Sort u → Sort u := id

def runInst (id : Name) (tac : TacticM α) (rerun : Bool) : TacticM α := withMainContext $ Tactic.focus do
  trace[Meta.debug] m!"HERE runInst"
  let mctx := ← getMCtx
  let some mvar := mctx.findUserName? id | throwError "could not find '{id}' in metavariable context"
  unless !(← mvar.isAssigned) do 
    let ret ← tac
    return ret
  let rec countHPs (e : Expr) (n : Nat) (b : Bool) := do
    match e with
    | .forallE _ d bod _ =>
      if d.isAppOf ``HP then
        countHPs bod (n + 1) b
      else if d.isAppOf ``HPP then
        countHPs bod n true
      else
        pure (n, b)
    | _ => 
      pure (n, b)
  let type ← mvar.getType
  let mvarLCtx := (← mvar.getDecl).lctx
  let (numHPs, hasHPP) ← countHPs type 0 false
  -- trace[Meta.debug] s!"numHPs: {numHPs}, {type}"
  let lctx ← getLCtx
  let target ← instantiateMVars (← getMainTarget)

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
          if sube.getAppArgs.size == numHPs + (if hasHPP then 1 else 0) then
            true
          else
            false
        else
          false
      else
        false

  trace[Meta.debug] s!"mvar: {mvar.name}"
  for decl in lctx do
    unless ← tryReplace decl do continue
    match decl with
      | .cdecl i fv n t b k =>
        trace[Meta.debug] s!"type: {← ppExpr t}"
        trace[Meta.debug] s!"real type: {t}"
      | .ldecl i fv n t v b k =>
        pure ()
  for decl in lctx do
    unless ← tryReplace decl do continue
    match decl with
      | .cdecl i fv n t b k =>
        -- trace[Meta.debug] s!"type: {← ppExpr t}"
        -- trace[Meta.debug] s!"real type: {t}"
        if let some mvarApp := getMVarApp? t then
          -- trace[Meta.debug] s!"HERE 1"
          mvarApp? := some mvarApp
          break
        -- else
        --   -- trace[Meta.debug] s!"HERE 2"
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
  let mvarAppArgs := mvarApp.getAppArgs[0:numHPs].toArray

  let newMvar ← mkFreshExprMVar (← inferType mvarApp)
  trace[Meta.debug] m!"DBG[35]: Aux.lean:205: newMvar={newMvar}"
  let newMvarLam ← forallBoundedTelescope (← mvar.getType) numHPs fun vs _ => do
    mkLambdaFVars vs newMvar

  let repWithNewMvarLam e : Expr :=
    e.replace fun e =>
      if let .mvar id .. := e then
        if id == mvar then
          newMvarLam
        else
          none
      else
        none

  let repLCtx (ctx : LocalContext) (repFn : Expr → Expr) := do
    let mut newCtx := (ctx)
    for decl in ctx do
      unless ← tryReplace decl do continue
      let newDecl : LocalDecl ← match decl with
        | .cdecl i fv n t b k => do
          let tNew := (repFn (← instantiateMVars t))
          trace[Meta.debug] m!"new type of {n}: {tNew}"
          pure $ .cdecl i fv n tNew b k
        | .ldecl i fv n t v b k => do
          let tNew := (repFn (← instantiateMVars t))
          let vNew := (repFn (← instantiateMVars v))
          pure $ .ldecl i fv n (repFn tNew) (repFn vNew) b k
      -- trace[Meta.debug] s!"DBG[39]: Aux.lean:185 {← ppExpr newDecl.type}"
      newCtx := newCtx.modifyLocalDecl newDecl.fvarId fun _ => newDecl
    pure newCtx
  let newCtx ← repLCtx (← getLCtx) repWithNewMvarLam
  let newTarget := repWithNewMvarLam (← instantiateMVars target)
  let newGoal ← withLCtx' newCtx $ mkFreshExprMVar newTarget
  trace[Meta.debug] s!"DBG[36]: Aux.lean:229: newGoal={newGoal}"

  let state ← saveState
  pushGoal newGoal.mvarId!
  let (newMCtx, ret) ← Tactic.focus do
    evalTactic (← `(tactic| try simp only at *))
    let ret ← tac
    -- while (← getGoals).length > 0 do
    --   discard popMainGoal
    pure (← getMCtx, ret)

  -- unless (← newMvar.mvarId!.isAssigned) do throwError "failed to assign `{mvar}` through unification ({newMvar})"
  trace[Meta.debug] m!"success assigning `{mvar}` through unification ({newMvar})"
  let assignment ← instantiateMVars newMvar

  -- let assignmentMvars := assignment.collectMVars default |>.result
  trace[Meta.debug] s!"BEFORE: {assignment}"
  let assignmentMvarDeps ← assignment.myGetMVarDependencies
  -- ^ FIXME what about assigned mvars? Need to create copies of all mvars with types/assignments fully instantiated?
  trace[Meta.debug] s!"AFTER"
  
  -- trace[Meta.debug] s!"DBG[34]: Aux.lean:238: assignment={assignment}"
  state.restore

  let oldMCtx ← getMCtx
  let mut newMVars : Std.HashMap MVarId (Name × MVarId × Expr × Expr) := default
  let mut counter : Nat := 0
  for (mv, decl) in newMCtx.decls do
    if not (oldMCtx.decls.contains mv) && assignmentMvarDeps.contains mv then
      let name := id.toString ++ s!"_{counter}" |>.toName
      trace[Meta.debug] s!"name: {name}, origName: {decl.userName}"
      let newId ← mkFreshMVarId
      -- let (e, type) ← if assignmentMvarsDeps.contains mv then
      let (e, type) ← forallBoundedTelescope (← mvar.getType) numHPs fun vs _ => do
        let type ← mkForallFVars vs decl.type -- FIXME decl.type may depend on mvarAppArgs, should abstract?
        let e := mkAppN (.mvar newId) mvarAppArgs
        -- trace[Meta.debug] s!"{id.toString} numHPs: {vs.size}, {decl.type}, {type}, {e}"
        trace[Meta.debug] s!"{name} origName: {mv.name} origType: {decl.type}"
        pure (e, type)
        -- else
        --   pure (.mvar id, decl.type)
      newMVars := newMVars.insert mv (name, newId, e, type)
      counter := counter + 1

  let rep (e : Expr) : Expr :=
    e.replace fun e =>
      if let .mvar id .. := e then
        if let some (_, _, e, _) := newMVars.get? id then
          e
        else
          none
      else
        none

  for (oldId, decl) in newMCtx.decls do
    if let some (name, newId, e, type) := newMVars.get? oldId then
      let newType := rep type
      let newLctx := mvarLCtx
      trace[Meta.debug] s!"{name} type: {type}"
      trace[Meta.debug] s!"{name} newType: {newType}"
      -- let newLctx ← repLCtx decl.lctx rep -- FIXME is this necessary?
      modifyMCtx fun mctx =>
      { mctx with
        mvarCounter := mctx.mvarCounter + 1
        decls       := mctx.decls.insert newId { decl with
          depth := mctx.depth
          index := mctx.mvarCounter
          userName := name
          lctx := newLctx
          type := newType
        }
        userNames := if name.isAnonymous then mctx.userNames else mctx.userNames.insert name newId }
        -- mctx.addExprMVarDecl (mvarId : MVarId) (userName : Name) (lctx : LocalContext) (localInstances : LocalInstances) (type : Expr) (kind : MetavarKind := MetavarKind.natural) (numScopeArgs : Nat := 0) : MetavarContext :=

  let repAssignment := rep assignment
  forallBoundedTelescope (← mvar.getType) numHPs fun vs _ => do
    let mut absAssignment := repAssignment
    for (arg, fvar) in mvarAppArgs.zip vs do
      absAssignment := absAssignment.replace fun e =>
        if e == arg then
          fvar
        else none
    let mut val := default
    if hasHPP then
      let prodArg := mvarApp.getAppArgs[numHPs]!
      unless prodArg.isMVar do throwError "expected metavar for product hole argument"
      unless not (← prodArg.mvarId!.isAssigned) do throwError "expected product hole argument metavar to be unassigned"
      let prodArgType ← prodArg.mvarId!.getType
      unless prodArgType.getAppFn.isMVar do throwError "expected metavar for product hole argument type"
      unless not (← prodArgType.getAppFn.mvarId!.isAssigned) do throwError "expected product hole argument type metavar to be unassigned"
      let (_, s) ← absAssignment.collectFVars |>.run default
      let fvars ← collectForwardDeps (s.fvarIds.map (.fvar ·)) false
      let fvars := fvars.filter (fun fv => not (mvarLCtx.contains fv.fvarId!))

      -- TODO assign prodArgType to depndent Sigma type encapsulating fvars types (in order)
      -- TODO assign prodArg to tuple of fvars
      -- TODO add new fvar to context with type prodArgType
      -- TODO subst instances of fvars in absAssignment with corresponding projections of new fvar

      -- val ← mkLambdaFVars (vs ++ #[newFv])  absAssignment -- TODO
    else
      val ← mkLambdaFVars vs absAssignment

    try
      _ ← isDefEq (.mvar mvar) val
      trace[Meta.debug] s!"assigned {mvar.name} := {val}"
    catch _ =>
      throwError  "assignment `{mvar} := {← ppExpr val}` failed (from application {mvarAppArgs})"
  if rerun then
    tac
  else
    pure ret

@[tactic inst] def evalInst : Tactic := fun stx => withMainContext $ Tactic.focus do
  let id : Name := (TSyntax.mk stx[1]).getId
  let tac   := stx[2]
  runInst id (evalTactic tac) true

@[tactic inst'] def evalInst' : Tactic := fun stx => withMainContext $ Tactic.focus do
  let id : Name := (TSyntax.mk stx[1]).getId
  let tac   := stx[2]
  runInst id (evalTactic tac) false

-- syntax (name := rectx) "rectx" ident : tactic
-- @[tactic rectx] def evalRectx : Tactic := fun stx => withMainContext $ Tactic.focus do
--   let id : Name := (TSyntax.mk stx[1]).getId
--   runInst id

/-- Return the `n`th local declaration (counting backwards) whose type is definitionally equal to `type`. -/
def findNthLocalDeclWithType? (type : Expr) (n : Nat) : MetaM (Option (FVarId × Nat)) := do
  let mut curr_n := 1
  let mut idx := (← getLCtx).decls.toArray.size - 1
  for localDecl? in (← getLCtx).decls.toArray.reverse do
    if let some localDecl := localDecl? then
      if not localDecl.isImplementationDetail then
        -- if let some mvarId := (← getMCtx).findUserName? `mvar13 then
        --   trace[Meta.debug] s!"found: {mvarId.name}, {← mvarId.isAssigned}"
        let state : Meta.SavedState ← saveState
        if (← isDefEq type localDecl.type) then
          if curr_n == n then
            trace[Meta.debug] s!"success: {← ppExpr localDecl.type}, {localDecl.type}"
            -- if let some mvarId := (← getMCtx).findUserName? `mvar13 then
            --   trace[Meta.debug] s!"found: {mvarId.name}, {← mvarId.isAssigned}"
            return some (localDecl.fvarId, idx)
          else 
            trace[Meta.debug] s!"failure: {← ppExpr localDecl.type}, {localDecl.type}"
            -- if let some mvarId := (← getMCtx).findUserName? `mvar13 then
            --   trace[Meta.debug] s!"found: {mvarId.name}, {← mvarId.isAssigned}"
            state.restore
            curr_n := curr_n + 1
        else 
          state.restore
    idx := idx - 1
  pure none

def _root_.Lean.MVarId.nthassumptionCore (mvarId : MVarId) (n : Nat) : MetaM (Option Nat) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `nthassumption
    match (← findNthLocalDeclWithType? (← mvarId.getType) n) with
    | none => return none
    | some (fvarId, idx) =>
      -- trace[Meta.debug] s!"found: {← fvarId.getUserName}: {← ppExpr (← fvarId.getType)}"
      mvarId.assign (mkFVar fvarId); return idx

def _root_.Lean.MVarId.nthassumption (mvarId : MVarId) (n : Nat) : MetaM Nat := do
  let some idx := (← mvarId.nthassumptionCore n) |
    throwTacticEx `nthassumption mvarId
  pure idx

/--
`nthassumption mvar n` behaves much like `inst mvar assumption`,
except it uses the `n`th assumption that matches the current goal.

This allows for selecting which particular assumption is used, which is useful
when unification incurs a metavariable assignment.

Example:
```
def g' (x : HP Nat → HP Nat → Nat) (a b : Nat) : Id Nat := do
  pure (x a b)

theorem g'_spec (a b : Nat) :
    ∃ x,
   ⦃⌜a > 0 ∧ b > 0 ∧ 5 > a⌝⦄
   g' x a b
   ⦃⇓ r => ⌜r > 0 ∧ 5 > r⌝⦄ := by
  exists? mvar1
  mvcgen [g']
  rename_i h
  rcases h with ⟨_, _, _⟩
  mleave

  -- Goal:
  -- a b : Nat
  -- a✝² : 0 < a
  -- a✝¹ : 0 < b
  -- a✝ : a < 5
  -- ⊢ 0 < ?mvar1 a b ∧ ?mvar1 a b < 5

  and_intros
  nthassumption mvar1 2 -- assigns `?mvar1 = fun a b => a`
  assumption
```
-/
syntax (name := nthassumption) "nthassumption" ident num : tactic

@[tactic nthassumption] def evalNthAssumption : Tactic := fun stx => do
  let id := (TSyntax.mk stx[1]).getId
  let n := (TSyntax.mk stx[2]).getNat
  let tac := liftMetaTacticAux fun mvarId => do let ret ← mvarId.nthassumption n; pure (ret, [])
  let ret ← runInst id tac false
  -- trace[Meta.debug] s!"HERE 2: {ret}, {← ppExpr hyp.type}"
  --   let some hyp := (← getLCtx).decls[ret]! | unreachable!
  liftMetaTactic fun mvarId => do
    trace[Meta.debug] s!"HERE 1: {ret}, {(← getLCtx).size}"
    let some hyp := (← getLCtx).decls[ret]! | unreachable!
    trace[Meta.debug] s!"HERE 2: {ret}, {← ppExpr hyp.type}"
    mvarId.assign hyp.toExpr
    pure []

-- attribute [-spec] Std.Do.Spec.forIn_range

@[spec]
theorem Spec.forIn_range' {β : Type u} {m : Type u → Type v} {ps : PostShape}
    [Monad m] [WPMonad m ps]
    {xs : Std.Legacy.Range} {init : β} {f : Nat → β → m (ForInStep β)}
    (inv : Invariant xs.toList β ps)
    (step : ∀ pref cur suff (h1 : xs.toList = pref ++ cur :: suff) (h2 : pref.length + 1 + suff.length = (xs.stop - xs.start + xs.step - 1) / xs.step) b,
      Triple
        (f cur b)
        (inv.1 (⟨pref, cur::suff, h1.symm⟩, b))
        (fun r => match r with
          | .yield b' => inv.1 (⟨pref ++ [cur], suff, by simp [h1]⟩, b')
          | .done b' => inv.1 (⟨xs.toList, [], by simp⟩, b'), inv.2)) :
    Triple (forIn xs init f) (inv.1 (⟨[], xs.toList, rfl⟩, init)) (fun b => inv.1 (⟨xs.toList, [], by simp⟩, b), inv.2) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  apply Spec.forIn_list inv fun pref cur suff (h1 : xs.toList = pref ++ cur :: suff) =>
    step pref cur suff h1 (by
        have hrng_dec_sz : (pref ++ cur :: suff).length = (xs.stop - xs.start + xs.step - 1) / xs.step := by
          rw [← h1]
          simp only [List.length_range']
        rw [List.length_append, List.length_cons] at hrng_dec_sz
        omega
      )
