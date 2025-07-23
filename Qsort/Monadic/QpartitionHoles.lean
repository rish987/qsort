import Std.Tactic.Do
import Qsort.AuxLemmas
import Qsort.Monadic.Aux

set_option mvcgen.warning false

open Std.Do
open List

namespace Monadic.Qpartition

variable {α : Type} {n : Nat}

abbrev Vector (α n) := {xs : Array α // xs.size = n}

def Vector.get (xs : Vector α n) (i : Fin n) := xs.1[Fin.mk (i : Nat) (i.cast xs.2.symm).2]

def Vector.toList (xs : Vector α n) : List α := xs.1.toList

structure ST (α n) where
  xs : Vector α n

-- TODO generalize to any monad with `ST α n` in `PostShape.args`
abbrev SM := StateM (ST α n)

abbrev ps := PostShape.arg (ST α n) PostShape.pure

abbrev gxs : SVal ((ST α n)::[]) (Vector α n) := fun s => SVal.pure s.xs

def g : StateM (ST α n) (ST α n) := do pure $ (← get)

-- FIXME remove
def mxs (f : Vector α n → Vector α n) : StateM (ST α n) Unit := do modify fun s => {s with xs := f s.xs}

def Vector.swap (as : Vector α n) (i j : Nat) (h_i : i < n := by omega) (h_j : j < n := by omega) : Vector α n :=
  ⟨as.1.swap i j, (Array.size_swap ..).trans as.2⟩

def qpartition_maybeSwap (lt : α → α → Bool) (lo hi : Fin n) : StateM (ST α n) Unit := do
  if lt ((← get).xs.get hi) ((← get).xs.get lo) then
    mxs fun xs => xs.swap lo hi

def qpartition_prep
    (lt : α → α → Bool) (lo hi : Fin n) :
    StateM (ST α n) Unit := do
  let mid : Fin n := ⟨(lo.1 + hi) / 2, by omega⟩
  qpartition_maybeSwap lt lo mid
  qpartition_maybeSwap lt lo hi
  qpartition_maybeSwap lt hi mid

-- FIXME why do `xs` binders produce errors when importing MPL
/-- Partitions `xs[lo..=hi]`, returning a pivot point and the new array. -/
@[inline] def qpartition (x : Nat)
    (lt : α → α → Bool) (lo hi : Fin n) (hle : lo ≤ hi) :
    StateM (ST α n) $ {pivot : Nat // lo ≤ pivot ∧ pivot ≤ hi} := do
  qpartition_prep lt lo hi
  let pivot := (← get).xs.get hi
  -- we must keep track of i and j and their respective properties all together within a single subtype,
  -- because these dependent properties must be shown in parallel to reassigning the indices
  let mut inv : {t : Nat × Nat // lo ≤ t.1 ∧ t.1 ≤ hi ∧ t.1 ≤ t.2} := ⟨(lo, lo), by omega, by omega⟩
  for _ in [lo:hi] do
    let mut ⟨(i, j), hloi, hihi, hij⟩ := inv
    -- FIXME want to use `assert hjhi : j < hi` here, deferring its proof to the correctness proof
    if hjhi : j < hi then
      have _ : i < hi := Nat.lt_of_le_of_lt hij hjhi
      let xs := (← get).xs -- FIXME
      if lt (xs.get ⟨j, by omega⟩) (xs.get ⟨x, sorry⟩) then
        mxs fun xs => xs.swap i j
        i := i + 1
        j := j + 1
        inv := ⟨(i, j), Nat.le_succ_of_le hloi, by omega, by omega⟩
      else
        j := j + 1
        inv := ⟨(i, j), hloi, by omega, by omega⟩
  let ⟨(i, _), hloi, hihi, _⟩ := inv
  mxs fun xs => xs.swap i hi
  pure ⟨i, hloi, hihi⟩

variable {lt : α → α → Bool} (lt_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)

-- FIXME should be able to derive this triple, ideally
@[spec]
theorem mxs_triple
    :
   ⦃fun s => Q.1 () ({s with xs := f s.xs})⦄
   mxs (α := α) (n := n) f
   ⦃Q⦄ := by
  unfold mxs
  mvcgen

def Stable (as bs : Vector α n) (lo hi : Fin n) : Prop :=
     ∀ i, i < lo → as.get i = bs.get i ∧
     ∀ i, i > hi → as.get i = bs.get i

def Perm (as bs : Vector α n) : Prop :=
  as.1.Perm bs.1

namespace Vector.swap
variable (i j : Nat) 

theorem stable {as bs : Vector α n} {hi lo : Fin n} (h : Stable as bs lo hi)
   (hilo : i ≥ lo) (hihi : i ≤ hi) (hjlo : j ≥ lo) (hjhi : j ≤ hi)
   : Stable (as.swap i j) bs lo hi := by
  sorry

theorem get_left {xs : Vector α n} {i j : Nat} (hi : i < n) (hj : j < n) :
   (xs.swap i j hi hj).get ⟨i, hi⟩ = xs.get ⟨j, hj⟩ := by
  sorry

theorem get_right {xs : Vector α n} {i j : Nat} (hi : i < n) (hj : j < n) :
   (xs.swap i j hi hj).get ⟨j, hj⟩ = xs.get ⟨i, hi⟩ := by
  sorry

theorem get_other {xs : Vector α n} {i j : Nat} (k : Nat)
   (hi : i < n) (hj : j < n) (hk : k < n)
   (hi' : k ≠ i) (hj' : k ≠ j) :
   (xs.swap i j hi hj).get ⟨k, hk⟩ = xs.get ⟨k, hk⟩ := by
  sorry

end Vector.swap

-- attribute [sort] Fin.getElem_fin Array.length_toList Array.size_swap List.append_left_inj List.append_right_inj List.length_cons

theorem qpartition_maybeSwap_perm {lo : Fin n} {hi : Fin n} (hle : lo ≤ hi := by omega) :
   ⦃⌜#gxs = xs⌝⦄
   qpartition_maybeSwap lt lo hi
   ⦃⇓ pivot => ⌜Stable #gxs xs lo hi ∧ (#gxs).1.Perm xs.1⌝⦄ := by
  sorry

namespace qpartition_prep
theorem nil {lo : Fin n} {hi : Fin n} (hle : lo ≤ hi := by omega) :
   ⦃⌜True⌝⦄
   qpartition_prep lt lo hi
   ⦃⇓ _ => ⌜True⌝⦄ := by
  sorry

theorem stable {lo : Fin n} {hi : Fin n} (hle : lo ≤ hi := by omega) :
   ⦃⌜#gxs = xs⌝⦄
   qpartition_prep lt lo hi
   ⦃⇓ pivot => ⌜Stable #gxs xs lo hi⌝⦄ := by
  sorry

-- @[spec]
theorem perm {lo : Fin n} {hi : Fin n} (hle : lo ≤ hi := by omega) :
   ⦃⌜#gxs = xs⌝⦄
   qpartition_prep lt lo hi
   ⦃⇓ pivot => ⌜(#gxs).1.Perm xs.1⌝⦄ := by
  sorry
end qpartition_prep

namespace qpartition
-- theorem stable (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
--    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi)
--    :
--    ∃ x,
--    ⦃⌜#gxs = xs⌝⦄
--    qpartition x lt lo hi hle
--    ⦃⇓ _ => ⌜Stable #gxs xs lo hi⌝⦄ := by
--   let x : Nat := ?m
--   exists x
--   have : x = hi := by exact rfl
--   unfold qpartition
--   mvcgen [qpartition_prep.stable]
--   omegas
--   case inv =>
--     exact PostCond.total fun (⟨⟨i, j⟩, _⟩, sp) =>
--       SPred.and
--       ⌜j = lo + sp.rpref.length⌝
--       ⌜Stable #gxs xs lo hi ⌝
--
--   mvcgen_aux
--   rw [List.length_cons]
--   rcases h with ⟨hj, hs⟩ -- FIXME
--   and_intros
--   omegas
--   apply Vector.swap.stable
--   omegas
--
--   mvcgen_aux
--   rw [List.length_cons]
--   rcases h with ⟨hj, hs⟩ -- FIXME
--   and_intros
--   omegas
--
--   . mvcgen_aux -- FIXME
--     rcases h with ⟨hj, hs⟩ -- FIXME
--     subst hj
--
--     -- FIXME FIXME both of these properties should be provided by Spec.forIn_range?
--     have hrng_dec_sz : (rpref.reverse ++ x :: suff).length = hi - lo := by
--       rw [← h]
--       simp only [List.length_range', Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
--     rw [List.length_append, List.length_reverse, List.length_cons] at hrng_dec_sz
--
--     -- FIXME this should be a goal generated by `mvcgen`, which is used in a proof by contradiction
--     have : lo + rpref.length < hi := by omega
--     contradiction
--
--   . mvcgen_aux -- FIXME
--     next h' _ _ =>
--     rw [h'] at h -- FIXME should have been automated
--
--     dsimp
--     and_intros
--     rfl
--     omegas
--
--   . mvcgen_aux -- FIXME
--     apply Vector.swap.stable
--     rcases h
--     omegas

theorem sorted 
   (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a)
   (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
   (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi)
   :
   ∃ x,
   ⦃⌜#gxs = xs⌝⦄
   qpartition x lt lo hi hle
   ⦃⇓ pivot => ⌜
     Stable #gxs xs lo hi ∧
     (∀ (i : Nat) (h : i < n), i < pivot.1 → i ≥ lo → ¬lt ((#gxs).get ⟨pivot.1, by omega⟩) ((#gxs).get ⟨i, h⟩)) ∧
     (∀ (i : Nat) (h : i < n), i > pivot.1 → i ≤ hi → ¬lt ((#gxs).get ⟨i, h⟩) ((#gxs).get ⟨pivot.1, by omega⟩))⌝⦄ := by
  -- FIXME could `mvcgen` attempt to auto-unfold definitions that it doesn't have a spec for?
  -- let y : Nat := ?_
  -- apply Exists.intro y
  set_option pp.all true in
  exists?
  -- have : y = hi := by exact rfl
  unfold qpartition
  mvcgen [qpartition_prep.stable]

  omegas

  case inv =>
    exact PostCond.total fun (⟨⟨i, j⟩, _⟩, sp) =>
      SPred.and -- FIXME want to use ∧ notation instead
      ⌜j = lo + sp.rpref.length⌝ -- FIXME can we individually label these with names for use with `mcases`?
      (SPred.and
      ⌜(∀ (x : Nat) (hx : x < n), lo ≤ x → x < i → ¬ lt ((#gxs).get hi) ((#gxs).get ⟨x, hx⟩))⌝
      (SPred.and
      ⌜(∀ (x : Nat) (hx : x < n), i ≤ x → x < j → ¬ lt ((#gxs).get ⟨x, hx⟩) ((#gxs).get hi))⌝
      ⌜Stable #gxs xs lo hi ⌝
      )
      )

  . mvcgen_aux -- FIXME automate

    rcases h with ⟨hj, hl, hr, _⟩ -- FIXME

    rw [List.length_cons]

    and_intros
    omegas
    intros x _ _ _ -- FIXME
    -- set_option trace.Meta.debug true in
    ite x rw [Vector.swap.get_left]
    . rw [Vector.swap.get_other]
      apply le_asymm
      omegas
      assumption
    . rw [Vector.swap.get_other]
      rw [Vector.swap.get_other]
      apply hl
      omegas
    intros x _ _ _ -- FIXME
    ite x rw [Vector.swap.get_right]
    . rw [Vector.swap.get_other]
      apply hr
      omegas
    . rw [Vector.swap.get_other]
      rw [Vector.swap.get_other]
      apply hr
      omegas
    . apply Vector.swap.stable
      omegas

  . mvcgen_aux -- FIXME automate

    rcases h with ⟨hj, hl, hr, _⟩

    rw [List.length_cons]
    
    and_intros
    . omegas
    . intros
      apply hl
      omegas
    . intros x 
      intros
      omegas
      -- set_option trace.Meta.debug true in
      ite y ite x assumption
      apply hr
      omegas
      sorry
    omegas

  omegas

  case h_1.isFalse =>
    mleave
    intros s hj hl hr
    subst hj

    -- FIXME FIXME both of these properties should be provided by Spec.forIn_range?
    have hrng_dec_sz : (rpref.reverse ++ x :: suff).length = hi - lo := by
      rw [← h]
      simp only [List.length_range', Nat.sub_zero, Nat.add_one_sub_one, Nat.div_one]
    rw [List.length_append, List.length_reverse, List.length_cons] at hrng_dec_sz

    -- FIXME this should be a goal generated by `mvcgen`, which is used in a proof by contradiction
    have : lo + rpref.length < hi := by omega
    contradiction

  case success.pre1 =>
    next h' _ _ =>
    rw [h'] at h -- FIXME should have been automated

    mvcgen_aux

    -- FIXME automate
    simp only [inv]
    dsimp

    and_intros
    omegas

  case h_1 =>
    mvcgen_aux

    -- FIXME FIXME these simplifications are related to the use of `Specs.forin_range`, and should be automatically applied whenever that spec is used
    simp only [List.length_reverse, List.length_range'] at h
    simp only [Nat.add_one_sub_one, Nat.div_one] at h

    rcases h with ⟨hj, hl, hr, _⟩ -- FIXME

    and_intros
    . apply Vector.swap.stable
      omegas

    omegas
    . intros
      rw [Vector.swap.get_left]
      rw [Vector.swap.get_other]
      apply hl
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

theorem perm {lo : Fin n} {hi : Fin n} (hle : lo ≤ hi := by omega) :
   ∃ x,
   ⦃⌜#gxs = xs⌝⦄
   qpartition x lt lo hi hle
   ⦃⇓ pivot => ⌜Perm (#gxs) xs⌝⦄ := by
  sorry
end qpartition
