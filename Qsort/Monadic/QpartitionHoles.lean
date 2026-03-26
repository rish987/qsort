import Std.Tactic.Do
import Qsort.AuxLemmas
import Qsort.Monadic.Aux
import Qsort.Monadic.Theory
import Qsort.SDo.VCGen

set_option mvcgen.warning false
set_option pp.showLetValues true

open Std.Do
open List

namespace Monadic.Qpartition

@[inline] def qpartition (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : HP Nat → HP Nat → Nat)
    (lt : α → α → Bool) (lo hi : Nat) (hlo : lo < n) (hhi: hi < n) (hle : lo ≤ hi) :
    StateM (ST α n) $ {pivot : Nat // lo ≤ pivot ∧ pivot ≤ hi} := do
  qpartition_prep lt lo hi hlo hhi
  let pivot := (← get).xs.get hi hhi
  let mut i : Nat := lo
  let mut j : Nat := lo
  for _ in [x11 i j:x12 i j] do
    -- FIXME need assertions in place of `sorry`s
    let xs := (← get).xs -- FIXME
    if lt (xs.get (x1 i j) sorry) (xs.get (x2 i j) sorry) then
      mxs fun xs => xs.swap (x9 i j) (x10 i j) sorry sorry
      i := x5 i j
      j := x6 i j
    else
      i := x7 i j
      j := x8 i j
  mxs fun xs => xs.swap (x3 i j) (x4 i j) sorry sorry
  pure ⟨x13 i j, sorry, sorry⟩

variable {lt : α → α → Bool} 

namespace qpartition

-- set_option trace.Elab.Tactic.Do.vcgen true in
theorem sorted 
   (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a)
   (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
   (lo hi : Nat) (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi)
   :
   ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13,
   ⦃fun s => ⌜s.xs = xs⌝⦄
   qpartition x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 lt lo hi hlo hhi hle
   ⦃⇓ pivot s => ⌜
     (∀ (x : Nat), lo ≤ x → x < pivot.1 → (h : x < n) → ¬lt ((s.xs).get pivot.1 (by omega)) ((s.xs).get x h)) ∧
     (∀ (x : Nat), pivot.1 < x → x ≤ hi → (h : x < n) → ¬lt ((s.xs).get x h) ((s.xs).get pivot.1 (by omega))) ∧
     Stable s.xs xs lo hi hlo hhi
   ⌝⦄ := by
  exists? mvar1
  exists? mvar2
  exists? mvar3
  exists? mvar4
  exists? mvar5
  exists? mvar6
  exists? mvar7
  exists? mvar8
  exists? mvar9
  exists? mvar10
  exists? mvar11
  exists? mvar12
  exists? mvar13

  mvar mvar01 : HP Nat → HP Nat → Nat -- loop invariant mvars
  mvar mvar02 : HP Nat → HP Nat → Nat

  -- FIXME could `mvcgen` attempt to auto-unfold definitions that it doesn't have a spec for?
  unfold qpartition
  smvcgen [qpartition_prep.stable] invariants
  . ⇓ t => fun s =>
      let sp := t.1;
      let ⟨i, j⟩ := t.2;
      ⌜(∀ (x : Nat), lo ≤ x → x < i → (hx : x < n) → (hm : (?mvar01 i j) < n) → ¬ lt ((s.xs).get (?mvar01 i j) hm) ((s.xs).get x hx))
      ∧
      (∀ (x : Nat), i ≤ x → x < j → (hx : x < n) → (hm : (?mvar02 i j) < n) → ¬ lt ((s.xs).get x hx) ((s.xs).get (?mvar02 i j) hm))
      ∧
      (j = lo + sp.prefix.length)
      ∧
      (lo ≤ i ∧ j ≤ hi ∧ i ≤ j)
      ∧
      (Stable s.xs xs lo hi hlo hhi)⌝

  omegas

  case vc5.post.success.post.success =>
    rename_i r _ h

    -- FIXME FIXME these simplifications are related to the use of `Specs.forin_range`, and should be automatically applied whenever that spec is used
    simp only [List.length_range'] at h
    simp only [Nat.add_one_sub_one, Nat.div_one] at h

    rcases h with ⟨hl, hr, hj, _,  _⟩ -- FIXME
    rcases r with ⟨i, j⟩
    simp only at * -- FIXME
    
    and_intros
    intros
    inst mvar3
      rw [Vector.swap.get_left]
    rw [Vector.swap.get_other]
    inst mvar4 apply hl
    omega
    inst mvar13 omega
    omega
    rotate_left

    intros x _ _ _ -- FIXME
    rw [Vector.swap.get_left]
    ite x rw [Vector.swap.get_right]
    inst mvar02 apply hr
    omega
    rotate_left 1
    . intros
      rw [Vector.swap.get_other]
      apply hr
      omega
      -- rw [hj]
      ite j 
        apply lt_of_ne
        assumption
        apply ne_symm
        inst mvar01 assumption
        -- omega
        -- omega
      . false_or_by_contra -- FIXME write an ite_force tactic that does these steps automatically
        apply h

        apply eq_comm
        apply eq_trans
        exact hj
        inst mvar11 inst mvar12 apply add_sub
        assumption
      omega
      omega
    rotate_right
    ite j assumption
    . false_or_by_contra -- FIXME
      apply h

      omega

    . apply Vector.swap.stable
      omegas

    omega

  . rename_i pref cur suff h' _ _ h _
    simp only [length_append, length_cons, length_nil, Nat.zero_add]

    rcases h with ⟨hl, hr, hj, _,  _⟩ -- FIXME

    -- simp only [length_append, length_cons, length_nil, Nat.zero_add]

    -- FIXME FIXME both of these properties should be provided by Spec.forIn_range?
    have hrng_dec_sz : (pref ++ cur :: suff).length = hi - lo := by
      rw [← h']
      simp only [List.length_range', Nat.add_one_sub_one, Nat.div_one]
    rw [List.length_append, List.length_cons] at hrng_dec_sz

    and_intros
    omegas
    apply pred_range_extend

    intros x
    intros
    rw [Vector.swap.get_other]
    rw [Vector.swap.get_other]
    apply hl
    assumption
    assumption
    apply ne_of_lt
    nthassumption mvar9 3
    rotate_left 3 -- FIXME tactic to collectively defer all remaining goals in a .focus block not solved by `omega`

    inst mvar5 apply pred_range_single
    intros
    rw [Vector.swap.get_left]
    rw [Vector.swap.get_other]
    apply le_asymm
    omegas
    inst mvar1 inst mvar2 assumption
    rotate_left 1 -- FIXME

    apply pred_range_extend
    intros x
    intros
    . rw [Vector.swap.get_other]
      rw [Vector.swap.get_other]
      omegas
      apply hr
      rename_i hp _ _ _ _
      omegas
      rotate_right 1
      apply ne_of_lt
      nthassumption mvar10 3
      omegas
    . inst mvar6 apply pred_range_single
      intros
      rw [Vector.swap.get_right]
      rw [Vector.swap.get_other]
      omegas
      apply hr
      omegas
    omegas
    . apply Vector.swap.stable
      omegas

  . rename_i pref cur suff h' _ _ h _ 
    simp only [length_append, length_cons, length_nil, Nat.zero_add]

    rcases h with ⟨hl, hr, hj, _,  _⟩ -- FIXME

    -- FIXME FIXME both of these properties should be provided by Spec.forIn_range?
    have hrng_dec_sz : (pref ++ cur :: suff).length = hi - lo := by
      rw [← h']
      simp only [List.length_range', Nat.add_one_sub_one, Nat.div_one]
    rw [List.length_append, List.length_cons] at hrng_dec_sz
    
    and_intros
    omegas
    inst mvar7 assumption
    apply pred_range_extend
    . intros x
      intros
      apply hr
      omegas
    inst mvar8 apply pred_range_single
    intros
    omegas

  omegas

  . rename_i h
    next h' _ _ =>
    rw [h'] at h -- FIXME should have been automated

    -- FIXME automate
    dsimp

    and_intros
    omegas

-- theorem perm {lo : Fin n} {hi : Fin n} (hle : lo ≤ hi := by omega) :
--    ∃ x1 x2 x3 x4,
--    ⦃⌜#gxs = xs⌝⦄
--    qpartition x1 x2 x3 x4 lt lo hi hle
--    ⦃⇓ pivot => ⌜Perm (#gxs) xs⌝⦄ := by
--   sorry
end qpartition
