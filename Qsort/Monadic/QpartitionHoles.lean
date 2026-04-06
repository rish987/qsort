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

@[inline] def qpartition (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : HP Nat → HP Nat → Nat) (x14 : Nat) (x15 : HP Nat → Nat) 
    (lt : α → α → Bool) (lo hi : Nat) (hlo : lo < n) (hhi: hi < n) (hle : lo ≤ hi) :
    StateM (ST α n) $ {pivot : Nat // lo ≤ pivot ∧ pivot ≤ hi} := do
  qp_prep lt lo hi hlo hhi
  let mut i : Nat := x14
  let mut j : Nat := x15 i
  for _ in [x11 i j:x12 i j] do
    -- FIXME need assertions in place of `sorry`s
    let xs := (← get).xs -- FIXME
    if lt (xs.get (x1 i j) sorry) (xs.get (x2 i j) sorry) then
      swap (x9 i j) (x10 i j) sorry sorry
      i := x5 i j
      j := x6 i j
    else
      i := x7 i j
      j := x8 i j
  swap (x3 i j) (x4 i j) sorry sorry
  pure ⟨x13 i j, sorry, sorry⟩

variable {lt : α → α → Bool} 

theorem test (a b : Nat) (h : a < b) (h' : b ≤ a) : False := by omega

namespace qpartition

-- set_option trace.Elab.Tactic.Do.vcgen true in
theorem sorted 
   (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a)
   (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
   (lo hi : Nat) (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi)
   :
   ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15,
   ⦃fun s => ⌜s.xs = xs⌝⦄
   qpartition x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 lt lo hi hlo hhi hle
   ⦃⇓ pivot s => ⌜
     (RangePred lo pivot.1 fun x => (h : x < n) → ¬lt ((s.xs).get pivot.1 (by omega)) ((s.xs).get x h)) ∧
     (RangePred (pivot.1 + 1) (hi + 1) fun x => (h : x < n) → ¬lt ((s.xs).get x h) ((s.xs).get pivot.1 (by omega))) ∧
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
  exists? mvar14
  exists? mvar15

  mvar mvar01 : HP Nat → HP Nat → Nat -- loop invariant mvars
  mvar mvar02 : HP Nat → HP Nat → Nat
  mvar mvar03 : HP Nat → HP Nat → Nat
  mvar mvar04 : HP Nat → HP Nat → Nat
  mvar mvar05 : HP Nat → HP Nat → Nat

  -- FIXME could `mvcgen` attempt to auto-unfold definitions that it doesn't have a spec for?
  unfold qpartition
  smvcgen [qp_prep.stable] invariants
  . ⇓ t => fun s =>
      let sp := t.1;
      let ⟨i, j⟩ := t.2;
      ⌜(RangePred (?mvar03 i j) i fun x => (hx : x < n) → (hm : (?mvar01 i j) < n) → ¬ lt ((s.xs).get (?mvar01 i j) hm) ((s.xs).get x hx))
      -- ⌜(∀ (t : (x : Nat) ×' (?mvar03 i j) ≤ x ×' x < i ×' (hx : x < n) ×' ((?mvar01 i j) < n)), ¬ lt ((s.xs).get (?mvar01 i j) t.2.2.2.2) ((s.xs).get t.1 t.2.2.2.1))
      ∧
      (RangePred i j fun x => (hx : x < n) → (hm : (?mvar02 i j) < n) → ¬ lt ((s.xs).get x hx) ((s.xs).get (?mvar02 i j) hm))
      ∧
      (j = lo + sp.prefix.length)
      ∧
      ((?mvar04 i j) ≤ i ∧ i ≤ j)
      ∧
      (Stable s.xs xs lo hi hlo hhi)⌝

  case vc5.post.success.post.success =>
    rename_i r _ h

    simp only [lists, arith] at *

    rcases h with ⟨hl, hr, hj, _,  _⟩ -- FIXME
    rcases r with ⟨i, j⟩
    simp only at * -- FIXME
    
    and_intros
    intros x
    intros
    intros
    inst mvar3
      rw [Vector.swap.get_left]
    rw [Vector.swap.get_other]
    -- inst mvar01 refine hl (.mk x ?_)
    -- refine (.mk ?_ ?_) -- FIXME
    -- inst mvar03 omega
    -- refine (.mk ?_ ?_) -- FIXME
    -- inst mvar13 omega
    -- refine (.mk ?_ ?_) -- FIXME
    -- sorry
    -- ^ FIXME get proof from program (last arg to last swap call)?
    -- (normally this would be done automatically w/ apply)
    inst mvar01 apply hl
    inst mvar03 omega
    inst mvar13 omega
    omega
    rotate_left

    intros x _ _ _ -- FIXME
    rw [Vector.swap.get_left]
    ite x rw [Vector.swap.get_right]
    inst mvar02 apply hr
    omega
    rotate_left 1
    . rw [Vector.swap.get_other]
      apply hr
      omega
      ite j 
        apply lt_of_ne
        apply Nat.le_of_lt_succ
        assumption
        apply ne_symm
        inst mvar4 assumption
      . false_or_by_contra -- FIXME
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

    . rename_i h
      rcases h
      apply Vector.swap.stable
      omega
      inst mvar04 assumption
      omegas

    omega

  . rename_i pref cur suff h' _ _ h _
    -- FIXME
    have hrng_dec_sz : (pref ++ cur :: suff).length = hi - lo := by
      rw [← h']
      simp only [lists, arith]
    simp only [lists, arith] at *
    rcases h with ⟨hl, hr, hj, _,  _⟩

    and_intros
    apply pred_range_extend
    -- rename_i b s _ _ _
    -- rcases b with ⟨i, j⟩
    -- dsimp
    -- set_option trace.Meta.isDefEq true in
    -- refine pred_range_extend_tup' (Q := fun x => (_ : x < n) ×' hi < n) lo _ (?mvar5 i j) ?_ ?_

    intros x
    intros
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
    -- FIXME
    have hrng_dec_sz : (pref ++ cur :: suff).length = hi - lo := by
      rw [← h']
      simp only [lists, arith]
    simp only [lists, arith] at *
    rcases h with ⟨hl, hr, hj, _,  _⟩
    
    and_intros
    omegas
    inst mvar7 assumption
    apply pred_range_extend
    . intros x
      intros
      intros
      apply hr
      omegas
    inst mvar8 apply pred_range_single
    intros
    omegas

  . rename_i h' _ _ h
    rw [h'] at h
    simp only [lists, arith] at *

    and_intros

    intros _ _ hm
    intros
    have := Nat.not_le_of_lt hm
    false_or_by_contra
    apply this
    inst mvar14 assumption

    intros _ _ hm
    intros
    have := Nat.not_le_of_lt hm
    false_or_by_contra
    apply this
    inst mvar15 assumption

    omegas

-- theorem perm {lo : Fin n} {hi : Fin n} (hle : lo ≤ hi := by omega) :
--    ∃ x1 x2 x3 x4,
--    ⦃⌜#gxs = xs⌝⦄
--    qpartition x1 x2 x3 x4 lt lo hi hle
--    ⦃⇓ pivot => ⌜Perm (#gxs) xs⌝⦄ := by
--   sorry
end qpartition
