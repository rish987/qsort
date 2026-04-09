import Lean.Meta.Tactic.Util
import Lean.Meta.Diagnostics
import Lean.Meta.Tactic.Refl
import Lean.Elab.Binders
import Lean.Elab.Open
import Lean.Elab.Eval
import Lean.Elab.SetOption
import Lean.Elab.Tactic.ElabTerm
import Lean.Elab.Do

public section

open Lean.Meta
namespace Lean.SMeta

@[inline] private partial def introNImp {σ} (mvarId : MVarId) (n : Nat) (mkName : LocalContext → Name → Bool → σ → MetaM (Name × σ)) (s : σ)
    : MetaM (Array FVarId × MVarId) := mvarId.withContext do
  trace[Meta.debug] m!"HERE 1"
  mvarId.checkNotAssigned `introN
  let mvarType ← mvarId.getType
  let lctx ← getLCtx
  let rec @[specialize] loop (i : Nat) (lctx : LocalContext) (fvars : Array Expr) (j : Nat) (s : σ) (type : Expr) : MetaM (Array Expr × MVarId) := do
    match i, type with
    | 0, type =>
      let type := type.instantiateRevRange j fvars.size fvars
      withLCtx' lctx do
        withNewLocalInstances fvars j do
          let tag     ← mvarId.getTag
          -- let type := type.headBeta
          let type := mkAppN (← mkLambdaFVars fvars.reverse type.headBeta) fvars.reverse
          -- trace[Meta.debug] m!"type: {mkAppN (← mkLambdaFVars fvars.reverse type.headBeta) fvars.reverse}"
          let newMVar ← mkFreshExprSyntheticOpaqueMVar type tag
          let newVal  ← mkLambdaFVars fvars newMVar
          mvarId.assign newVal
          return (fvars, newMVar.mvarId!)
    | i+1, .forallE n type body c =>
      let type   := type.instantiateRevRange j fvars.size fvars
      let type   := type.headBeta
      let fvarId ← mkFreshFVarId
      let (n, s) ← mkName lctx n c.isExplicit s
      let lctx   := lctx.mkLocalDecl fvarId n type c
      let fvar   := mkFVar fvarId
      let fvars  := fvars.push fvar
      loop i lctx fvars j s body
    | i+1, type =>
      let type := type.instantiateRevRange j fvars.size fvars
      withLCtx' lctx do
        withNewLocalInstances fvars j do
          /- We used to use just `whnf`, but it produces counterintuitive behavior if
            - `type` is a metavariable `?m` such that `?m := let x := v; b`, or
            - `type` has `MData` or annotations such as `optParam` around a `let`-expression.

            `whnf` instantiates metavariables, and consumes `MData`, but it also expands the `let`.
          -/
          let newType := (← instantiateMVars type).cleanupAnnotations
          if newType.isForall || newType.isLet then
            loop (i+1) lctx fvars fvars.size s newType
          else
            let newType ← whnf newType
            if newType.isForall then
              loop (i+1) lctx fvars fvars.size s newType
            else
              throwTacticEx `introN mvarId <| m!"There are no additional binders or `let` bindings in the goal to introduce"
  let (fvars, mvarId) ← loop n lctx #[] 0 s mvarType
  return (fvars.map Expr.fvarId!, mvarId)

-- register_builtin_option tactic.hygienic : Bool := {
--   defValue := true
--   descr    := "make sure tactics are hygienic"
-- }
--
-- private def mkFreshBinderNameForTacticCore (lctx : LocalContext) (binderName : Name) (hygienic := true) : MetaM Name := do
--   if hygienic then
--     mkFreshUserName binderName
--   else
--     return lctx.getUnusedName binderName
--
-- /--
-- Similar to `Lean.Core.mkFreshUserName`, but takes into account the `tactic.hygienic` option value.
-- If `tactic.hygienic = true`, then fresh macro scopes are applied to `binderName`.
-- If not, then returns an (accessible) name based on `binderName` that is unused in the local context.
-- -/
-- def mkFreshBinderNameForTactic (binderName : Name) : MetaM Name := do
--   mkFreshBinderNameForTacticCore (← getLCtx) binderName (tactic.hygienic.get (← getOptions))

-- FIXME FIXME
private def mkAuxNameImp (preserveBinderNames : Bool) (hygienic : Bool) (useNamesForExplicitOnly : Bool)
    (lctx : LocalContext) (binderName : Name) (isExplicit : Bool) : List Name → MetaM (Name × List Name) --:= fun l => pure (binderName, default)
  | []         => mkAuxNameWithoutGivenName []
  | n :: rest  => do
    if useNamesForExplicitOnly && !isExplicit then
      mkAuxNameWithoutGivenName (n :: rest)
    else if n != Name.mkSimple "_" then
      return (n, rest)
    else
      mkAuxNameWithoutGivenName rest
where
  mkAuxNameWithoutGivenName (rest : List Name) : MetaM (Name × List Name) := do
    -- Use a nicer binder name than `[anonymous]`.
    -- In this case, we make sure the name is hygienic.
    let binderName ← if binderName.isAnonymous then mkFreshUserName `a else pure binderName
    -- if true then
    return (binderName, rest)
    -- else
    --   let binderName ← mkFreshBinderNameForTacticCore lctx binderName hygienic
    --   return (binderName, rest)

def introNCore (mvarId : MVarId) (n : Nat) (givenNames : List Name) (useNamesForExplicitOnly : Bool) (preserveBinderNames : Bool)
    : MetaM (Array FVarId × MVarId) := do
  let hygienic := tactic.hygienic.get (← getOptions)
  if n == 0 then
    return (#[], mvarId)
  else
    introNImp mvarId n (mkAuxNameImp preserveBinderNames hygienic useNamesForExplicitOnly) givenNames

/--
Introduce `n` binders in the goal `mvarId`.
-/
abbrev _root_.Lean.MVarId.sintroN (mvarId : MVarId) (n : Nat) (givenNames : List Name := []) (useNamesForExplicitOnly := false) : MetaM (Array FVarId × MVarId) :=
  introNCore mvarId n givenNames (useNamesForExplicitOnly := useNamesForExplicitOnly) (preserveBinderNames := false)

-- /--
-- Introduce `n` binders in the goal `mvarId`. The new hypotheses are named using the binder names.
-- The suffix `P` stands for "preserving`.
-- -/
-- abbrev _root_.Lean.MVarId.introNP (mvarId : MVarId) (n : Nat) : MetaM (Array FVarId × MVarId) :=
--   introNCore mvarId n [] (useNamesForExplicitOnly := false) (preserveBinderNames := true)

/--
Introduce one binder using `name` as the new hypothesis name.
-/
def _root_.Lean.MVarId.sintro (mvarId : MVarId) (name : Name) : MetaM (FVarId × MVarId) := do
  let (fvarIds, mvarId) ← mvarId.sintroN 1 [name]
  return (fvarIds[0]!, mvarId)

def intro1Core (mvarId : MVarId) (preserveBinderNames : Bool) : MetaM (FVarId × MVarId) := do
  let (fvarIds, mvarId) ← introNCore mvarId 1 [] (useNamesForExplicitOnly := false) preserveBinderNames
  return (fvarIds[0]!, mvarId)

/--
Given a goal `... |- β → α`, returns a goal `... ⊢ α`.
Like `intro h; clear h`, but without ever appending to the local context.
-/
def _root_.Lean.MVarId.sintro1_ (mvarId : MVarId) : MetaM MVarId := do
  mvarId.withContext do
    let target ← mvarId.getType'
    match target with
    | .forallE n β α bi =>
      if α.hasLooseBVars then
        throwError "intro1_: expected arrow type\n{mvarId}"
      let tag ← mvarId.getTag
      let newMVar ← mkFreshExprSyntheticOpaqueMVar α tag
      mvarId.assign (.lam n β newMVar bi)
      return newMVar.mvarId!
    | _ => throwError "intro1_: expected arrow type\n{mvarId}"

/--
Calculate the number of new hypotheses that would be created by `intros`,
i.e. the number of binders which can be introduced without unfolding definitions.
-/
partial def getIntrosSize : Expr → Nat
  | .forallE _ _ b _ => getIntrosSize b + 1
  | .letE _ _ _ b _  => getIntrosSize b + 1
  | .mdata _ b       => getIntrosSize b
  | _                => 0

end Lean.SMeta

namespace Lean.Parser.Tactic
/--
`intro` alternative that produces a beta-redex goal
-/
syntax (name := sintro) "sintro" ident : tactic
end Lean.Parser.Tactic

namespace Lean.Elab.Tactic
open Meta
open Parser.Tactic

@[tactic Lean.Parser.Tactic.sintro] def evalSIntro : Tactic := fun stx => do
  let id := (TSyntax.mk stx[1]).getId
  introStep stx id
where
  /--
  Performs an `intro` step.
  - `nref` is a ref for the introduced hypothesis
  - `n` is the name to use for the introduced hypothesis, `_` means to use a hygienic name
    and `rfl` means to use a hygienic name and `subst`
  - `typeStx?` is used to change the type of the introduced hypothesis
  -/
  introStep (nref : Syntax) (n : Name) (typeStx? : Option Syntax := none) : TacticM Unit := do
    let mvarIdOrig ← getMainGoal
    let subst := n == `rfl
    let n := if subst then `_ else n
    let fvarId ← liftMetaTacticAux fun mvarId => do
      let (fvarId, mvarId) ← mvarId.sintro n
      pure (fvarId, [mvarId])
    let fvar := mkFVar fvarId
    if let some typeStx := typeStx? then
      withMainContext do
        let mvarCounterSaved := (← getMCtx).mvarCounter
        let fvarType ← inferType fvar
        let type ← runTermElab do
          -- Use the original context, to prevent `type` from referring to the introduced hypothesis
          let type ← mvarIdOrig.withContext <| Term.elabType typeStx
          Term.synthesizeSyntheticMVars
          discard <| isDefEqGuarded type fvarType
          pure type
        unless (← isDefEqGuarded type fvarType) do
          throwError m!"Type mismatch: Hypothesis `{fvar}` " ++
            (← mkHasTypeButIsExpectedMsg fvarType type (trailing? := "due to the provided type annotation"))
        let type ← instantiateMVars type
        let mvars ← filterOldMVars (← getMVars type) mvarCounterSaved
        logUnassignedAndAbort mvars
        liftMetaTactic1 fun mvarId => mvarId.replaceLocalDeclDefEq fvarId type
    withMainContext do
      if subst then
        -- Note: the mdata prevents `rfl` from getting highlighted like a variable
        Term.addTermInfo' nref (.mdata {} fvar)
        liftMetaTactic1 fun mvarId => return (← substEq mvarId fvarId).2
      else
        Term.addLocalVarInfo nref fvar

