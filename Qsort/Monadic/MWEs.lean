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

abbrev SM := StateM (Array Nat)

abbrev gns : SVal ((Array Nat)::[]) (Array Nat) := fun s => SVal.pure s

noncomputable def setZero : StateM (Array Nat) Unit := do
  let mut i := 0
  let len := (← get).size
  for _ in [0:len] do
    let ns ← get
    if h : i < ns.size then
      modify fun _ => ns.set i 0 h
    i := i + 1

theorem setZero_spec :
   ⦃⌜#gns = ns⌝⦄
   setZero
   -- FIXME (3.1) why parens needed around #gns?
   ⦃⇓ _ => ⌜(#gns).size = ns.size⌝ ∧ ⌜∀ i, (h : i < (#gns).size) → (#gns)[i]'h = 0⌝⦄ := by
  unfold setZero
  mvcgen

  case inv =>
    exact ⇓ (i, sp) =>
      -- FIXME (3.2) it would be very convenient to be able to name each of these
      -- components, and have mvcgen automatically call `rcases h with ...` to
      -- destruct it into separate hypotheses (using these names) in every
      -- subsequent goal. Then we wouldn't have to do it ourselves.
      ⌜(#gns).size = ns.size⌝ ∧
      ⌜ i = sp.rpref.length ⌝ ∧
      ⌜∀ j, (j < i) → (h : j < (#gns).size) → (#gns)[j]'h = 0⌝

  . mintro t
    mvcgen
    mleave
    simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at h -- FIXME `mvcgen` should have taken care of this?
    grind

  . mleave
    simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at h -- FIXME
    grind

  . mleave
    simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at h -- FIXME
    grind

  . mleave
    simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at h -- FIXME
    simp only [List.length_reverse, List.length_range']
    grind

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
