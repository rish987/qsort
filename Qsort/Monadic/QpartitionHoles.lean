import Std.Tactic.Do
import Qsort.AuxLemmas
import Qsort.Monadic.Aux
import Qsort.Monadic.Theory

set_option mvcgen.warning false

open Std.Do
open List

namespace Monadic.Qpartition

@[inline] def qpartition (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 : HP Nat → HP Nat → Nat)
    (lt : α → α → Bool) (lo hi : Nat) (hlo : lo < n) (hhi: hi < n) (hle : lo ≤ hi) :
    StateM (ST α n) $ {pivot : Nat // lo ≤ pivot ∧ pivot ≤ hi} := do
  qpartition_prep lt lo hi hlo hhi
  let pivot := (← get).xs.get hi hhi
  let mut i : Nat := lo
  let mut j : Nat := lo
  -- let mut inv : {t : Nat × Nat // lo ≤ t.1 ∧ t.1 ≤ hi ∧ t.1 ≤ t.2} := ⟨(lo, lo), by omega, by omega⟩
  for _ in [lo:x11 i j] do
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
  pure ⟨i, sorry, sorry⟩

variable {lt : α → α → Bool} 

namespace qpartition

theorem sorted 
   (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a)
   (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
   (lo hi : Nat) (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi)
   :
   ∃ x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12,
   ⦃⌜#gxs = xs⌝⦄
   qpartition x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 lt lo hi hlo hhi hle
   ⦃⇓ pivot => ⌜
     (∀ (x : Nat), lo ≤ x → x < pivot.1 → (h : x < n) → ¬lt ((#gxs).get pivot.1 (by omega)) ((#gxs).get x h)) ∧
     (∀ (x : Nat), pivot.1 < x → x ≤ hi → (h : x < n) → ¬lt ((#gxs).get x h) ((#gxs).get pivot.1 (by omega))) ∧
     Stable #gxs xs lo hi hlo hhi
   ⌝⦄ := by
  -- FIXME could `mvcgen` attempt to auto-unfold definitions that it doesn't have a spec for?
  -- apply Exists.intro y
  -- set_option pp.all true in
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
  exists default

  mvar mvar01 : HP Nat → HP Nat → HP Nat -- loop invariant mvars
  mvar mvar02 : HP Nat → HP Nat → HP Nat

  -- FIXME could `mvcgen` attempt to auto-unfold definitions that it doesn't have a spec for?
  unfold qpartition
  mvcgen [qpartition_prep.stable]

  omegas

  case inv =>
    exact PostCond.total fun t =>
      let ⟨i, j⟩ := t.1
      let sp := t.2
      SPred.and -- FIXME want to use ∧ notation instead
      ⌜(∀ (x : Nat), lo ≤ x → x < i → (hx : x < n) → ¬ lt ((#gxs).get (?mvar01 i j) sorry) ((#gxs).get x hx))⌝
      (SPred.and
      ⌜(∀ (x : Nat), i ≤ x → x < j → (hx : x < n) → ¬ lt ((#gxs).get x hx) ((#gxs).get (?mvar02 i j) sorry))⌝
      (SPred.and
      (⌜j = lo + sp.rpref.length⌝) -- FIXME can we individually label these with names for use with `mcases`?
      (SPred.and
      (⌜lo ≤ i ∧ j ≤ hi ∧ i ≤ j⌝)
      ⌜Stable #gxs xs lo hi hlo hhi⌝
      )))

  case post.success.post.success =>
    mvcgen_aux
    rename_i r _ h

    -- FIXME FIXME these simplifications are related to the use of `Specs.forin_range`, and should be automatically applied whenever that spec is used
    simp only [List.length_reverse, List.length_range'] at h
    simp only [Nat.add_one_sub_one, Nat.div_one] at h

    rcases h with ⟨hl, hr, hj, _,  _⟩ -- FIXME
    rcases r with ⟨i, j⟩
    simp only at * -- FIXME
    
    and_intros
    intros
    inst mvar3 rw [Vector.swap.get_left]
    rw [Vector.swap.get_other]
    inst mvar4
      try simp only -- FIXME
      apply hl
    omega
    omega
    omega
    rotate_left

    intros x _ _ _ -- FIXME
    rw [Vector.swap.get_left]
    ite x rw [Vector.swap.get_right]
    inst mvar02
      try simp only at hr -- FIXME
      apply hr
    omega
    rotate_left 2
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
        inst mvar11 apply add_sub
        assumption
      omega
      omega
    rotate_right
    have hj' : j = hi := by omega -- FIXME
    rw [hj']
    assumption

    . apply Vector.swap.stable
      omegas

    omega

  . mvcgen_aux -- FIXME automate
    rename_i h

    rcases h with ⟨hl, hr, hj, _,  _⟩ -- FIXME

    rw [List.length_cons]

    -- FIXME FIXME both of these properties should be provided by Spec.forIn_range?
    have hrng_dec_sz : (rpref.reverse ++ x :: suff).length = hi - lo := by
      rw [← h]
      simp only [List.length_range', Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
    rw [List.length_append, List.length_reverse, List.length_cons] at hrng_dec_sz

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
    nthassumption mvar9 2
    rotate_left 5 -- FIXME tactic to collectively defer all remaining goals in a .focus block not solved by `omega`

    inst mvar5 apply pred_range_single
    intros
    rw [Vector.swap.get_left]
    rw [Vector.swap.get_other]
    apply le_asymm
    omegas
    inst mvar1 inst mvar2
      simp only at * -- FIXME
      assumption
    rotate_left 3 -- FIXME

    apply pred_range_extend
    intros x
    intros
    . rw [Vector.swap.get_other]
      rw [Vector.swap.get_other]
      omegas
      apply hr
      omegas
      rotate_left 2
      apply ne_of_lt
      nthassumption mvar10 2
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

  . mvcgen_aux -- FIXME automate
    rename_i h

    rcases h with ⟨hl, hr, hj, _,  _⟩ -- FIXME

    rw [List.length_cons]

    -- FIXME FIXME both of these properties should be provided by Spec.forIn_range?
    have hrng_dec_sz : (rpref.reverse ++ x :: suff).length = hi - lo := by
      rw [← h]
      simp only [List.length_range', Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
    rw [List.length_append, List.length_reverse, List.length_cons] at hrng_dec_sz
    
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

  case success.pre1 =>
    rename_i h
    next h' _ _ =>
    rw [h'] at h -- FIXME should have been automated

    mvcgen_aux

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
