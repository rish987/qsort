import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

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

theorem setZero_spec :
   ⦃⌜0 < 1⌝⦄
   setZero
   ⦃⇓ _ => ⌜1 < 2⌝⦄ := by
  unfold setZero
  mvcgen

  case inv =>
    exact ⇓ (i, sp) =>
      ⌜(#gns).size = len⌝ ∧
      ⌜i = sp.rpref.length⌝ ∧
      ⌜i ≤ (#gns).size⌝

  . mintro t
    rename_i h
    mvcgen
    mleave
    simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at h -- see #9363
    grind

  . mleave
    rename_i h
    simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at h
    rename_i _ _ h'
    false_or_by_contra
    apply h'

    -- `mvcgen` should leave us here
    rename_i hsp _ _
    have hrng_dec_sz : (rpref.reverse ++ x :: suff).length = len := by
      rw [← hsp]
      simp
    rw [List.length_append, List.length_reverse, List.length_cons] at hrng_dec_sz
    omega

  . mleave
    rename_i h
    simp
    rfl

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
