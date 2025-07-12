import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

namespace AssumptionFail

axiom G (lt : Nat) : Id Unit

noncomputable def F : Id Unit := do
  G 1

axiom P : Prop

@[spec]
axiom G_spec (h : P := by omega) :
   ⦃⌜True⌝⦄ G 1 ⦃⇓ _ => ⌜0 < 1⌝⦄

theorem qpartition_sorted (h : P) :
   ⦃⌜True⌝⦄ F ⦃⇓ _ => ⌜0 < 1⌝⦄ := by
  unfold F
  mvcgen
  -- FIXME `mvcgen` should have handled this; is the `autoParam` interfering here?
  case h => assumption

end AssumptionFail

namespace MakeGoalPure

abbrev SM := StateM Nat

abbrev ps := PostShape.arg Nat PostShape.pure

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

-- set_option pp.proofs true in
theorem F_spec :
   ⦃⌜True⌝⦄
   F
   ⦃⇓ _ => R⦄ := by
  unfold F
  mvcgen

  -- ideally, mvcgen would do these four steps automatically for us
  mintro ∀_
  mframe
  mpure_intro
  simp only [SPred.and_cons, SVal.curry_cons, SVal.curry_nil, SVal.uncurry_cons, SVal.uncurry_nil, SPred.and_nil] at *

  cases h
  apply hPQ
  assumption
  assumption

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
  mvcgen_aux

  cases h
  apply hPQ <;> assumption

end MakeGoalPure
