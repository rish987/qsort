import Std.Tactic.Do
import Qsort.AuxLemmas
import Qsort.Monadic.Theory
import Qsort.Monadic.Aux

set_option mvcgen.warning false

open Std.Do
open List

namespace Monadic.Qpartition

-- @[inline] def test : StateM (ST α n) Nat := do
--   let mut i : Nat := 0
--   let mut j : Nat := 0
--   -- let mut inv : {t : Nat × Nat // lo ≤ t.1 ∧ t.1 ≤ hi ∧ t.1 ≤ t.2} := ⟨(lo, lo), by omega, by omega⟩
--   for _ in [0:10] do
--     if i + j ≥ 0 then
--       -- FIXME need assertions in place of `sorry`s
--       i := i + 1
--       j := j + 1
--   pure i
--
-- theorem test_thm :
--    ⦃fun (s : (ST α n)) => ⌜True⌝⦄
--    test
--    ⦃⇓ r => fun s => ⌜r > 0⌝⦄ := by
--   -- FIXME could `mvcgen` attempt to auto-unfold definitions that it doesn't have a spec for?
--   unfold test
--   mvcgen
--   case inv1 =>
--     exact ⇓ (sp, ⟨i, j⟩) => fun s => ⌜i = sp.prefix.length⌝
--   sorry
--   sorry
--   sorry
--   sorry

@[inline] def qpartition
    (lt : α → α → Bool) (lo hi : Nat) (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi) :
    StateM (ST α n) $ {pivot : Nat // lo ≤ pivot ∧ pivot ≤ hi} := do
  qpartition_prep lt lo hi hlo hhi
  let pivot := (← get).xs.get hi
  let mut i : Nat := lo
  let mut j : Nat := lo
  -- let mut inv : {t : Nat × Nat // lo ≤ t.1 ∧ t.1 ≤ hi ∧ t.1 ≤ t.2} := ⟨(lo, lo), by omega, by omega⟩
  for _ in [lo:hi] do
    -- FIXME need assertions in place of `sorry`s
    let xs := (← get).xs -- FIXME
    if lt (xs.get j sorry) (xs.get hi sorry) then
      mxs fun xs => xs.swap i j sorry sorry
      i := i + 1
      j := j + 1
    else
      j := j + 1
  mxs fun xs => xs.swap i hi sorry sorry
  pure ⟨i, sorry, sorry⟩

variable {lt : α → α → Bool}

namespace qpartition
theorem sorted 
   (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a)
   (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
   (lo hi : Nat) (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi)
   :
   ⦃fun s => ⌜s.xs = xs⌝⦄
   qpartition lt lo hi hlo hhi hle
   ⦃⇓ pivot => fun s => ⌜
     Stable s.xs xs lo hi ∧
     (∀ (i : Nat) (h : i < n), i < pivot.1 → i ≥ lo → ¬lt ((s.xs).get pivot.1 (by omega)) ((s.xs).get i h)) ∧
     (∀ (i : Nat) (h : i < n), i > pivot.1 → i ≤ hi → ¬lt ((s.xs).get i h) ((s.xs).get pivot.1 (by omega)))⌝⦄ := by
  -- FIXME could `mvcgen` attempt to auto-unfold definitions that it doesn't have a spec for?
  unfold qpartition
  mvcgen [qpartition_prep.stable]

  omegas

  case inv1 =>
    exact ⇓ (sp, ⟨i, j⟩) => fun s =>
      SPred.and -- FIXME want to use ∧ notation instead
      (⌜j = lo + sp.prefix.length⌝) -- FIXME can we individually label these with names for use with `mcases`?
      (SPred.and
      (⌜lo ≤ i ∧ j ≤ hi ∧ i ≤ j⌝)
      (SPred.and
      ⌜(∀ (x : Nat), lo ≤ x → x < i → (hx : x < n) → ¬ lt ((s.xs).get hi hhi) ((s.xs).get x hx))⌝
      (SPred.and
      ⌜(∀ (x : Nat), i ≤ x → x < j → (hx : x < n) → ¬ lt ((s.xs).get x hx) ((s.xs).get hi hhi))⌝
      ⌜Stable s.xs xs lo hi ⌝
      )))

  . mvcgen_aux -- FIXME automate
    rename_i pref cur suff h' _ _ _ _ h _ _ 

    rcases h with ⟨hj, _, hl, hr, _⟩ -- FIXME

    -- simp only [length_append, length_cons, length_nil, Nat.zero_add, Nat.add_le_add_iff_right]
    simp only [length_append, length_cons, length_nil, Nat.zero_add]

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
    . rw [Vector.swap.get_other]
      rw [Vector.swap.get_other]
      apply hl
      omegas
    . apply pred_range_single
      intros
      rw [Vector.swap.get_left]
      rw [Vector.swap.get_other]
      apply le_asymm
      omegas
    apply pred_range_extend
    intros x
    intros
    . rw [Vector.swap.get_other]
      rw [Vector.swap.get_other]
      apply hr
      omegas
    . apply pred_range_single
      intros
      rw [Vector.swap.get_right]
      rw [Vector.swap.get_other]
      omegas
      apply hr
      omegas
    . apply Vector.swap.stable
      omegas

  . mvcgen_aux -- FIXME automate
    rename_i pref cur suff h' _ _ _ _ h _ _ 

    rcases h with ⟨hj, _, hl, hr, _⟩

    simp only [length_append, length_cons, length_nil, Nat.zero_add]

    -- FIXME FIXME both of these properties should be provided by Spec.forIn_range?
    have hrng_dec_sz : (pref ++ cur :: suff).length = hi - lo := by
      rw [← h']
      simp only [List.length_range', Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
    rw [List.length_append, List.length_cons] at hrng_dec_sz
    
    and_intros
    omegas
    apply pred_range_extend
    . intros x
      intros
      apply hr
      omegas
    apply pred_range_single
    intros
    omegas

  omegas

  . rename_i h
    next h' _ _ =>
    rw [h'] at h -- FIXME should have been automated

    mvcgen_aux

    -- FIXME automate
    dsimp

    and_intros
    omegas

  . rename_i h

    simp only [spred] at *
    -- FIXME FIXME these simplifications are related to the use of `Specs.forin_range`, and should be automatically applied whenever that spec is used
    simp only [List.length_range'] at h
    simp only [Nat.add_one_sub_one, Nat.div_one] at h

    rcases h with ⟨hj, _, hl, hr, _⟩ -- FIXME

    and_intros
    rotate_left
    . intros
      rw [Vector.swap.get_left]
      rw [Vector.swap.get_other]
      apply hl
      omegas
    rotate_left
    . apply Vector.swap.stable
      omegas

    intros x _ _ _ -- FIXME
    rw [Vector.swap.get_left]
    ite x rw [Vector.swap.get_right]
    apply hr
    omegas
    . intros
      . rw [Vector.swap.get_other]
        apply hr
        omegas

theorem perm {lo hi : Nat} (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi := by omega) :
   ⦃fun s => ⌜s.xs = xs⌝⦄
   qpartition lt lo hi hlo hhi hle
   ⦃⇓ pivot s => ⌜Perm (s.xs) xs⌝⦄ := by
  sorry
end qpartition
