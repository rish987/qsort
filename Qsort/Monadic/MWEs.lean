import Std.Tactic.Do
import Qsort.Monadic.Aux

open Std.Do

set_option mvcgen.warning false

namespace Tactics

/--
Given an existential goal `∃ x : T, P x`, `exists? mvar` will
create a new metavariable `?mvar : T` which is provided as the existential witness,
leaving us with the goal `P ?mvar`.
`?mvar` can then be assigned via unification during the proof.
-/
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

/--
If `?mvar : HP U1 -> ... -> HP Un -> V`, `inst mvar tac` tries to intelligently assign
`?mvar` based on the unification result of running `tac`. It works as follows:

1. Any instances of `?mvar` replaced by the constant function `fun u1 ... un => ?newMvar`, for some fresh metavar `?newMvar`.
2. The tactic `tac` is run. If `?newMvar` is assigned, continue, otherwise fail.
3. The proof state is reverted to what it was before (1).
4. We search for `?mvar` in the original proof state, finding an instance with `n` arguments `a1 ... an`.
4. We abstract `a1 ... an` out of `t` to construct a lambda expression `f`.
5. We assign `?mvar := f` and rerun `tac`.
-/
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

/--
`nthassumption mvar n` behaves much like `inst mvar assumption`,
except it uses the `n`th assumption that matches the current goal.

This allows for selecting which particular assumption is used, which is useful
when unification incurs a metavariable assignment.
-/

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
axiom nil : True

end Tactics

--- --- --- ---

namespace AssumptionFail

axiom G (lt : Nat) : Id Unit

noncomputable def F : Id Unit := do
  G 1

axiom P : Prop

@[spec]
axiom G_spec (h : P) :
   ⦃⌜True⌝⦄ G 1 ⦃⇓ _ => ⌜0 < 1⌝⦄

theorem F_spec (h : P) :
   ⦃⌜True⌝⦄ F ⦃⇓ _ => ⌜0 < 1⌝⦄ := by
  unfold F
  mvcgen

end AssumptionFail

--- --- --- ---

namespace MakeGoalPure

abbrev SM := StateM Nat

axiom P : Nat → Prop
axiom P' : Nat → Prop
axiom Q : Nat → Prop
axiom R : Assertion ps

abbrev n : SVal (Nat::[]) Nat := fun s => SVal.pure s

axiom hPQ : ∀ n, P n → P' n → Q n

axiom G : StateM Nat Unit
axiom H : StateM Nat Unit

axiom b : Bool

noncomputable def F : StateM Nat Unit := do
  G
  H

@[spec]
axiom G_spec : ⦃⌜True⌝⦄ G ⦃⇓ _ => ⌜P #n⌝ ∧ ⌜P' #n⌝⦄

@[spec]
axiom H_spec : ⦃⌜Q #n⌝⦄ H ⦃⇓ _ => R⦄

noncomputable def test : StateM Nat Unit := do
  modify fun s => 0
  pure ()

theorem test_spec : ⦃⌜True⌝⦄ test ⦃⇓ _ => ⌜#n ≤ 0⌝⦄ := by
unfold test
mvcgen
simp only
mspec

theorem F_spec :
   ⦃⌜True⌝⦄
   F
   ⦃⇓ _ => R⦄ := by
  unfold F
  mvcgen

  mleave

  apply hPQ

-- in general, mvcgen should do something like this:
macro "mvcgen_aux" : tactic => do
  `(tactic|
    (repeat mintro ∀_
     try mframe
     mpure_intro
     simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at *))

theorem F_spec' :
   ⦃⌜True⌝⦄
   F
   ⦃⇓ _ => R⦄ := by
  unfold F
  mvcgen
  mleave

  apply hPQ

end MakeGoalPure

--- --- --- ---

namespace LoopStuff

abbrev gns : SVal ((Array Nat)::[]) (Array Nat) := fun s => SVal.pure s

noncomputable def setZero : StateM (Array Nat) Unit := do
  let mut i := 0
  let len := (← get).size
  for _ in [0:len] do
    let ns ← get
    modify fun _ => ns.set! i 0
    i := i + 1

def pred : Nat → Option Nat
| .succ n => .some n
| .zero => none

def addPred (n : Nat) : StateM Unit Nat := do
  if n > 0 then
    let npred? := pred n
    if h : npred?.isSome then
      let npred := pred n |>.get h
      pure (n + npred)
    else
      pure 0 -- unreachable
  else
    pure 0

theorem addPred_spec : 
   ⦃⌜n > 0⌝⦄
   addPred n
   ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold addPred
  mvcgen

  . mleave
    omega

  . mleave
    rename_i h _
    false_or_by_contra
    apply h

    -- FIXME mvcgen should leave us here
    rename_i hn _
    have := Nat.exists_eq_add_of_lt hn
    rcases this with ⟨k, rfl⟩
    simp [npred?]
    rfl

theorem addPred_spec' : 
   ⦃⌜n > 1⌝⦄
   addPred n
   ⦃⇓ r => ⌜r > n⌝⦄ := by
  unfold addPred
  mvcgen

  rename_i h _
  . mleave
    have : (pred n).get h ≥ 1 := by
      cases n with
      | zero => omega
      | succ n' =>
        cases n' with
      | zero => omega
      | succ n'' =>
        simp [pred]
    omega

  . mleave
    rename_i h _
    false_or_by_contra
    apply h

    -- FIXME mvcgen should leave us here
    rename_i hn _
    have := Nat.exists_eq_add_of_lt hn
    rcases this with ⟨k, rfl⟩
    simp [npred?]
    rfl

  . omega

theorem addPred_ok 
  ( isTrue_isTrue :
    (h1 : n > 0) → (h2 : (pred n).isSome = true) →
    P ⊢ₛ Q.fst (n + (pred n).get h2) )
  ( isFalse :
    (h1 : ¬ n > 0) →
    P ⊢ₛ Q.fst 0 )
   : 
   ⦃P⦄
   addPred n
   ⦃Q⦄ := by
  unfold addPred
  mvcgen

  . apply isTrue_isTrue
    omega

  . mleave
    rename_i h 
    false_or_by_contra
    apply h

    -- FIXME mvcgen should leave us here
    rename_i hn _ _
    have := Nat.exists_eq_add_of_lt hn
    rcases this with ⟨k, rfl⟩
    simp [npred?]
    rfl

  . apply isFalse
    omega

theorem new_addPred_spec : 
   ⦃⌜n > 0⌝⦄
   addPred n
   ⦃⇓ r => ⌜r > 0⌝⦄ := by
  mvcgen [addPred_ok]

  . rename_i h
    simp at h
    mintro ∀s -- FIXME why doesn't `mleave` do this?
    mleave
    omega

theorem new_addPred_spec' : 
   ⦃⌜n > 1⌝⦄
   addPred n
   ⦃⇓ r => ⌜r > n⌝⦄ := by
  mvcgen [addPred_ok]

  . rename_i h
    simp at h
    mintro ∀s

    mleave
    have : (pred n).get h2 ≥ 1 := by
      cases n with
      | zero => omega
      | succ n' =>
        cases n' with
      | zero => omega
      | succ n'' =>
        simp [pred]
    omega

  . rename_i h
    simp at h
    mintro ∀s
    omega

-- noncomputable def findMaxIdx : StateM Unit {n : Nat // n < ns.size} := do
--   let ns := #[1, 2, 3, 4, 5]
--   let mut i := 0
--   let mut max := 0
--   let mut maxIdx := 0
--
--   let len := ns.size
--   for _ in [0:len] do
--     if h : i < ns.size then
--       let n := ns[i]
--       if n > max then
--         maxIdx := i
--         max := n
--
--   if n > max then
--     pure ⟨maxIdx, sorry⟩
--   else
--     pure sorry

-- theorem setZero_spec :
--    ⦃⌜0 < 1⌝⦄
--    setZero
--    ⦃⇓ _ => ⌜1 < 2⌝⦄ := by
--   unfold setZero
--   mvcgen
--
--   case inv =>
--     exact ⇓ (i, sp) =>
--       ⌜(#gns).size = len⌝ ∧
--       ⌜i = sp.rpref.length⌝ ∧
--       ⌜i ≤ (#gns).size⌝
--
--   . mintro t
--     rename_i h
--     mvcgen
--     mleave
--     simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at h -- see #9363
--     grind
--
--   . mleave
--     rename_i h
--     simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at h
--     rename_i _ _ h'
--     false_or_by_contra
--     apply h'
--
--     -- `mvcgen` should leave us here
--     rename_i hsp _ _
--     have hrng_dec_sz : (rpref.reverse ++ x :: suff).length = len := by
--       rw [← hsp]
--       simp
--     rw [List.length_append, List.length_reverse, List.length_cons] at hrng_dec_sz
--     omega
--
--   . mleave
--     rename_i h
--     simp
--     rfl

structure MyException where
def F : EStateM MyException Unit Unit := do
  for _ in [0:5] do
    pure ()

theorem F_spec :
   ⦃⌜True⌝⦄
   F
   ⦃⇓ _ => ⌜1 < 2⌝⦄ := by
  mvcgen [F]

  case inv => exact ⇓ _ => ⌜1 < 2⌝

  mleave
  omega

  mleave
  omega

  -- Goal:
  -- case post.except
  -- h✝ : 0 < 1
  -- ⊢ (⇓x => ⌜1 < 2⌝).snd ⊢ₑ (⇓x => ⌜1 < 2⌝).snd
  mleave
  -- Goal:
  -- case post.except
  -- h✝ : 0 < 1
  -- ⊢ FailConds.false ⊢ₑ FailConds.false
  simp only [FailConds.false, FailConds.const, FailConds.entails.refl]

structure AssertException where

abbrev AStateT := fun σ m => ExceptT AssertException (StateT σ m)
abbrev AStateM := fun σ => AStateT σ Id

structure SNat where
  n : Nat

def foo (ns : Array Nat) : AStateM Unit SNat := do
  let ns' := ns ++ #[1, 2, 3]
  if h : ns'.size > ns.size then
    pure (.mk (ns'[ns.size]'h))
  else
    throw .mk

theorem foo_spec (ns : Array Nat) :
   ⦃⌜True⌝⦄
   foo ns
   ⦃⇓ r => ⌜r = .mk 1⌝⦄ := by
  mvcgen [foo]

  . mleave
    simp

  . mleave
    rename_i h
    false_or_by_contra
    apply h

    -- FIXME `mvcgen` should leave us here
    simp

end LoopStuff

--- --- --- ---

namespace NeedStateLVar

abbrev SM := StateM (Array Nat)

abbrev gns : SVal ((Array Nat)::[]) (Array Nat) := fun s => SVal.pure s

noncomputable def setZeroHead : StateM (Array Nat) Unit := do
  modify fun _ => #[0, 1, 2, 3, 4, 5]

-- see TODO
macro "mvcgen_aux" : tactic => do
  `(tactic|
    (repeat mintro ∀_
     try mframe
     mpure_intro
     simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at *))

theorem Spec.mymodifyGet_StateT [Monad m] [WPMonad m ps] :
  ⦃fun s => let t := f s; Q.1 t.1 t.2⦄ (MonadStateOf.modifyGet f : StateT σ m α) ⦃Q⦄ := by
    simp [Triple]

theorem setZeroHead_spec :
   ⦃⌜True⌝⦄
   setZeroHead
   ⦃⇓ _ => ⌜∃ ns', (#gns).toList = 0 :: ns'⌝⦄ := by
  unfold setZeroHead
  mstart
  mintro h ∀s
  mspec Spec.mymodifyGet_StateT
  mvcgen
  -- Goal:
  -- s✝ : Array Nat
  -- ⊢ 
  -- h✝ : ⌜True⌝ s✝
  -- ⊢ₛ ⌜∃ ns', (#gns tuple).toList = 0 :: ns'⌝ (PUnit.unit, #[0, 1, 2, 3, 4, 5]).snd

  -- FIXME (4) here, we would want mvcgen to have assigned some let variable
  -- `s := #[0, 1, 2, 3, 4, 5]` so that we can use `s.tail` below instead of
  -- having to rewrite part of the state that was set with `modify`
  mvcgen_aux
  exists [1, 2, 3, 4, 5]

end NeedStateLVar
