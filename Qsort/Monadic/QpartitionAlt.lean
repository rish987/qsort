import Std.Tactic.Do
import Qsort.AuxLemmas
import Qsort.Monadic.Theory
import Qsort.Monadic.Aux
import Qsort.SDo.VCGen

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
-- set_option trace.Elab.Tactic.Do.vcgen true in
-- theorem test_thm :
--    ⦃fun (s : (ST α n)) => ⌜True⌝⦄
--    test
--    ⦃⇓ r => fun s => ⌜r > 0⌝⦄ := by
--   -- FIXME could `mvcgen` attempt to auto-unfold definitions that it doesn't have a spec for?
--   unfold test
--   -- mintro h
--   smvcgen
--   case inv1 =>
--     exact ⇓ (sp, ⟨i, j⟩) => fun s => ⌜i = sp.prefix.length⌝
--   sorry
--   sorry
--   sorry
--   sorry

@[inline] def qpartition
    (lt : α → α → Bool) (lo hi : Nat) (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi) :
    StateM (ST α n) $ {pivot : Nat // lo ≤ pivot ∧ pivot ≤ hi} := do
  qp_prep lt lo hi hlo hhi
  let mut i : Nat := lo + 1
  let mut j : Nat := lo + 1
  for _ in [lo + 1:hi + 1] do
    -- FIXME need assertions in place of `sorry`s
    let xs := (← get).xs -- FIXME
    if lt (xs.get j sorry) (xs.get lo sorry) then
      swap i j sorry sorry
      i := i + 1
      j := j + 1
    else
      j := j + 1
  swap (i - 1) lo sorry sorry
  pure ⟨i - 1, sorry, sorry⟩

variable {lt : α → α → Bool}

attribute [-simp] Nat.reduceSubDiff
namespace qpartition
set_option trace.Elab.Tactic.Do.vcgen true in
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
  -- mintro h
  -- mintro ∀s
  -- mspec_no_bind Std.Do.Spec.bind
  -- rename_i h
  -- rw [h]
  -- mspec qpartition_prep.stable
  -- omega
  -- mspec_no_bind Std.Do.Spec.bind
  -- simp only [MonadState.get]
  -- mspec
  -- mspec
  -- case post.success.post.success =>
  --   mintro ∀s
  --   mframe
  --   mleave
  --   sorry
  -- case inv =>
  --   exact ⇓ (sp, ⟨i, j⟩) => fun s =>
  --     SPred.and -- FIXME want to use ∧ notation instead
  --     (⌜j = lo + sp.prefix.length⌝) -- FIXME can we individually label these with names for use with `mcases`?
  --     (SPred.and
  --     (⌜lo ≤ i ∧ j ≤ hi ∧ i ≤ j⌝)
  --     (SPred.and
  --     ⌜(∀ (x : Nat), lo ≤ x → x < i → (hx : x < n) → ¬ lt ((s.xs).get hi hhi) ((s.xs).get x hx))⌝
  --     (SPred.and
  --     ⌜(∀ (x : Nat), i ≤ x → x < j → (hx : x < n) → ¬ lt ((s.xs).get x hx) ((s.xs).get hi hhi))⌝
  --     ⌜Stable s.xs xs lo hi ⌝
  --     )))
  -- unfold MonadState.get
  -- mspec
  smvcgen [qp_prep.stable] invariants
  . ⇓ (sp, ⟨i, j⟩) => fun s =>
      ⌜(∀ (x : Nat), lo + 1 ≤ x → x < i → (hx : x < n) → ¬ lt ((s.xs).get lo hlo) ((s.xs).get x hx))
      ∧
      (∀ (x : Nat), i ≤ x → x < j → (hx : x < n) → ¬ lt ((s.xs).get x hx) ((s.xs).get lo hlo))
      ∧
      j = lo + 1 + sp.prefix.length
      ∧
      (lo + 1 ≤ i ∧ i ≤ j)
      ∧
      Stable s.xs xs lo hi⌝

  omegas

  . rename_i pref cur suff h' _ _ h _
    rcases h with ⟨hl, hr, hj, _, _⟩
    -- FIXME should be provided by Spec.forIn_range
    have hrng_dec_sz : (pref ++ cur :: suff).length = hi - lo := by
      rw [← h']
      simp only [lists, arith] at *
    simp only [lists, arith] at *

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

  . rename_i pref cur suff h' _ _ h _
    rcases h with ⟨hl, hr, hj, _, _⟩
    -- FIXME should be provided by Spec.forIn_range
    have hrng_dec_sz : (pref ++ cur :: suff).length = hi - lo := by
      rw [← h']
      simp only [lists, arith] at *
    simp only [lists, arith] at *
    
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

  . rename_i h' _ _ h
    rw [h'] at h

    simp only [lists, arith] at *

    and_intros
    omegas

  . rename_i h'' _ _ h' _ _ h
    simp only [lists, arith] at *

    rcases h with ⟨hl, hr, hj, _, _⟩ -- FIXME

    and_intros
    rotate_left
    . intro x
      intros
      rw [Vector.swap.get_left]
      ite x rw [Vector.swap.get_right]
      apply hl
      omegas
      rw [Vector.swap.get_other]
      apply hl
      omegas
    rotate_left
    . apply Vector.swap.stable
      omegas

    intros x _ _ _ -- FIXME
    rw [Vector.swap.get_left]
    ite x rw [Vector.swap.get_right]
    omegas
    . intros
      . rw [Vector.swap.get_other]
        apply hr
        omega
        apply Nat.lt_of_le_pred
        omega
        rename_i r _ _ _ _ _ h1
        have ?m : Nat := ?mv
        have : r.snd.pred = ?m := ?mp
        rw [this]
        exact h1
        rw [hj]
        rw [Nat.pred_eq_sub_one]
        rw [Nat.succ_add_sub_one]
        omegas

theorem perm {lo hi : Nat} (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi := by omega) :
   ⦃fun s => ⌜s.xs = xs⌝⦄
   qpartition lt lo hi hlo hhi hle
   ⦃⇓ pivot s => ⌜Perm (s.xs) xs⌝⦄ := by
  sorry
end qpartition
