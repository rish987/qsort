import Std.Data.TreeMap
import Std.Tactic.Do
import Qsort.AuxLemmas
import Qsort.Monadic.Aux

set_option mvcgen.warning false

open Std.Do

namespace MPL

open List

-- def MWE (n : Nat) : (m : Nat) → n = m + 1 → Nat := by
--   let i : Nat := ?_
--   intro m h
--   -- clear n -- not allowed
--   subst h
--   have test : i = 0 := by
--     unfold i
--     -- type mismatch
--     --      rfl
--     --    has type
--     --      ?m.148 = ?m.148 : Prop
--     --    but is expected to have type
--     --      ?m.100 (m + 1) = 0 : Prop
--     exact rfl
--   exact 0


namespace Monadic

variable {α : Type} {n : Nat}

abbrev Vector (α n) := {xs : Array α // xs.size = n}

def Vector.get (xs : Vector α n) (i : Fin n) := xs.1[Fin.mk (i : Nat) (i.cast xs.2.symm).2]

def Vector.toList (xs : Vector α n) : List α := xs.1.toList

structure ST (α n) where
  xs : Vector α n

-- TODO generalize to any monad with `ST α n` in `PostShape.args`
abbrev SM := StateM (ST α n)

abbrev ps := PostShape.arg (ST α n) PostShape.pure
variable (FPre : Assertion (ps))
variable {FPre1 FPre2 : Assertion (ps)}
variable {FPost1 FPost2 : PostCond T (ps)}

variable {F : StateM (ST α n) T}

-- TODO generalize
theorem multiEntails (hF1 : ⦃FPre1⦄ F ⦃FPost1⦄) (hF2 : ⦃FPre2⦄ F ⦃FPost2⦄) (hFF1 : FPre ⊢ₛ FPre1) (hFF2 : FPre ⊢ₛ FPre2)
   : ⦃FPre⦄ F ⦃FPost1 ∧ₚ FPost2⦄ :=
   (SPred.and_intro hFF1 hFF2).trans (Triple.and F hF1 hF2)

abbrev xs : SVal ((ST α n)::[]) (Vector α n) := fun s => SVal.pure s.xs

def gxs : StateM (ST α n) (Vector α n) := do pure $ (← get).xs
def g : StateM (ST α n) (ST α n) := do pure $ (← get)

def mxs (f : Vector α n → Vector α n) : StateM (ST α n) Unit := do modify fun s => {s with xs := f s.xs}

-- @[spec]
-- theorem Specs.modifyGet_StateT' {m : Type → Type u} {ps : PostShape} {σ α : Type} {f : σ → α × σ}
--    {Q : PostCond α (PostShape.arg σ ps)} [Monad m] [WPMonad m ps] :
--    ⦃fun s => Q.1 (f s).1 (f s).2⦄ (MonadState.modifyGet f : StateT σ m α) ⦃Q⦄ := by
--   mvcgen
--
-- @[spec]
-- theorem Specs.modify_StateT  [Monad m] [WPMonad m psm] :
--   ⦃fun s => Q.1 () (f s)⦄ (modify f : StateT σ m Unit) ⦃Q⦄ := by
--     mintro _
--     unfold modify
--     mvcgen

def qpartition_maybeSwap (lt : α → α → Bool) (lo hi : Fin n) : StateM (ST α n) Unit := do
  if lt ((← get).xs.get hi) ((← get).xs.get lo) then
    mxs fun xs => ⟨xs.1.swap lo hi, (Array.size_swap ..).trans xs.2⟩

def qpartition_prep
    (lt : α → α → Bool) (lo hi : Fin n) :
    StateM (ST α n) Unit := do
  let mid : Fin n := ⟨(lo.1 + hi) / 2, by omega⟩
  qpartition_maybeSwap lt lo mid
  qpartition_maybeSwap lt lo hi
  qpartition_maybeSwap lt hi mid

-- FIXME why do `xs` binders produce errors when importing MPL
/-- Partitions `xs[lo..=hi]`, returning a pivot point and the new array. -/
@[inline] def qpartition
    (lt : α → α → Bool) (lo hi : Fin n) (hle : lo ≤ hi) :
    StateM (ST α n) $ {pivot : Nat // lo ≤ pivot ∧ pivot ≤ hi} := do
  qpartition_prep lt lo hi
  let pivot := (← get).xs.get hi
  -- we must keep track of i and j and their respective properties all together within a single subtype,
  -- because these dependent properties must be shown in parallel to reassigning the indices
  let mut inv : {t : Nat × Nat // lo ≤ t.1 ∧ t.1 ≤ hi ∧ t.1 ≤ t.2} := ⟨(lo, lo), by omega, by omega⟩
  for _ in [lo:hi] do
    let mut ⟨(i, j), hloi, hihi, hij⟩ := inv
    -- NOTE: `j < hi` is actually always the case. It would be easy to show if we could somehow bind `j`
    -- and the invariant properties in the `for` loop syntax rather than bundling it into `inv`, however this is not possible at the moment.
    -- Therefore, showing it is deferred to the correctness proof for now.
    if hjhi : j < hi then
      have _ : i < hi := Nat.lt_of_le_of_lt hij hjhi
      let xs := (← get).xs -- FIXME
      if lt (xs.get ⟨j, by omega⟩) (xs.get ⟨hi, by omega⟩) then
        mxs fun xs => ⟨(xs).1.swap i j, (Array.size_swap ..).trans xs.2⟩
        i := i + 1
        j := j + 1
        inv := ⟨(i, j), Nat.le_succ_of_le hloi, by omega, by omega⟩
      else
        j := j + 1
        inv := ⟨(i, j), hloi, by omega, by omega⟩
  let ⟨(i, _), hloi, hihi, _⟩ := inv
  mxs fun xs => ⟨xs.1.swap i hi, (Array.size_swap ..).trans xs.2⟩
  pure ⟨i, hloi, hihi⟩

def qsort_rec {n} (lt : α → α → Bool)
    (lo : Nat) (hi : Fin n) : StateM (ST α n) Unit := do
  if h : lo < hi.1 then
    let ⟨mid, (_ : lo ≤ mid), _⟩ ←
      qpartition lt ⟨lo, Nat.lt_trans h hi.2⟩ hi (Nat.le_of_lt h)
    qsort_rec lt lo ⟨mid - 1, by omega⟩
    qsort_rec lt (mid + 1) hi
termination_by hi - lo

/-- Sort the array `xs[low..=high]` using comparator `lt`. -/
@[inline] def qsort (xs : Array α) (lt : α → α → Bool) :
    Id (Array α) := do
  if h : xs.size > 0 then
    pure $ (qsort_rec lt 0 ⟨xs.size - 1, by omega⟩).run { xs := ⟨xs, rfl⟩ } |>.2.xs
  else pure xs

variable {lt : α → α → Bool} (lt_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)

-- FIXME mspec should be able to derive this triple, ideally
-- TODO try mvcgen instead wherever this is used, perhaps that's the exact use case?
@[spec]
theorem mxs_triple
    :
   ⦃fun s => Q.1 () ({s with xs := f s.xs})⦄
   mxs (α := α) (n := n) f
   ⦃Q⦄ := by
  unfold mxs
  mvcgen

theorem qpartition_maybeSwap_perm
    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi) {L M R : List α}
    (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi + 1)
    :
   ⦃⌜(#xs).toList = L ++ M ++ R⌝⦄
   qpartition_maybeSwap lt lo hi
   ⦃⇓ _ => ⌜∃ (M' : List α),
     (#xs).toList = L ++ M' ++ R ∧
     M'.Perm M⌝⦄ := by
  sorry

@[spec]
theorem qpartition_prep_perm
    {lo : Fin n} {hi : Fin n} (hle : lo ≤ hi := by omega) {L M R}
    (hlo : L.length = lo.1 := by omega) (hhi : lo.1 + M.length = hi + 1 := by omega)
    :
   ⦃⌜(#xs).toList = L ++ M ++ R⌝⦄
   qpartition_prep lt lo hi
   ⦃⇓ _ => ⌜∃ (M' : List α),
     (#xs).toList = L ++ M' ++ R ∧
     M'.Perm M⌝⦄ := by
  sorry

@[spec]
theorem Specs.get_StateT' [Monad m] [WPMonad m psm] :
  ⦃fun s => Q.1 s s⦄ (MonadState.get : StateT σ m σ) ⦃Q⦄ := by sorry

theorem qpartition_perm (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi) {L M R}
    (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi + 1)
    :
   ⦃⌜(#xs).toList = L ++ M ++ R⌝⦄
   qpartition lt lo hi hle
   ⦃⇓ pivot => ⌜∃ (M' : List α),
     (#xs).toList = L ++ M' ++ R ∧
     M'.Perm M⌝⦄ := by
  sorry

theorem swap_array_decomp {X : Array α} {A B C : List α} (hX : X.toList = A ++ B ++ C) (i j : Nat) (hi : i ≥ A.length) (hi' : i < A.length + B.length) (hj : j ≥ A.length) (hj' : j < A.length + B.length) : (X.swap (hi := sorry) (hj := sorry) i j).toList = A ++ ((Array.mk B).swap (hi := sorry) (hj := sorry) (i - A.length) (j - A.length)).toList ++ C := sorry

theorem subarray_decomp {X : Array α} {A B C : List α} (hX : X.toList = A ++ B ++ C) : X[A.length:A.length + B.length].toArray.toList = B := sorry

theorem vec_subarray (xs : Vector α n) : ∀ (a : α), a ∈ xs.1[lo:hi].toArray.toList ↔ ∃ (x : Nat) (hx : x < n), lo ≤ x ∧ x < hi ∧ xs.get ⟨x, hx⟩ = a := sorry

theorem _root_.ArrayToList.length_swap.{u} {α : Type u} {xs : Array α} {i j : Nat} {hi : i < xs.size} {hj : j < xs.size} :
  (xs.swap i j hi hj).toList.length = xs.toList.length := sorry

attribute [sort] Vector.get Fin.getElem_fin Array.length_toList Array.size_swap List.append_left_inj List.append_right_inj List.length_cons ArrayToList.length_swap
-- set_option pp.proofs true in
set_option trace.split.failure true in
set_option trace.Meta true in
theorem qpartition_sorted (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi) {L M R}
    (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi + 1)
    :
   ⦃⌜(#xs).toList = L ++ M ++ R⌝⦄
   qpartition lt lo hi hle
   ⦃⇓ pivot => ⌜∃ (l r : List α) (a : α),
     lo + l.length = pivot ∧
     (#xs).toList = L ++ l ++ a::r ++ R ∧ (∀ b ∈ l, ¬lt a b) ∧ (∀ b ∈ r, ¬lt b a)⌝⦄ := by
  -- FIXME could `mvcgen` attempt to auto-unfold definitions that it doesn't have a spec for?
  unfold qpartition
  mvcgen

  -- FIXME why?
  case hle => assumption
  case hlo => assumption
  case hhi => assumption

  case inv =>
    exact PostCond.total fun (⟨⟨i, j⟩, _⟩, sp) =>
      SPred.and -- FIXME want to use ∧ notation instead
      ⌜ j = lo + sp.rpref.length ⌝ -- FIXME can we individually label these with names for use with `mcases`?
      (SPred.and
      ⌜ ((∀ (x : Nat) (hx : x < n), lo ≤ x ∧ x < i → ¬ lt ((#xs).get hi) ((#xs).get ⟨x, hx⟩)))⌝
      (SPred.and
      ⌜ ((∀ (x : Nat) (hx : x < n), i ≤ x ∧ x < j → ¬ lt ((#xs).get ⟨x, hx⟩) ((#xs).get hi)))⌝
      ⌜ ∃ M', (#xs).val.toList = L ++ M' ++ R ∧ M'.length = M.length⌝))

  case h_1.isFalse =>
    . mvcgen_aux -- FIXME automate

      rcases h with ⟨rfl, _, _, _⟩

      -- FIXME both of these properties should be provided by Spec.forIn_range?
      have : (rpref.reverse ++ x :: suff).length = hi - lo := by sorry
      rw [List.length_append, List.length_reverse, List.length_cons] at this
      have : lo + rpref.length < hi := by omega

      -- rcases h with ⟨rfl, -, -, -⟩
      contradiction

  case success.pre1 =>
    mvcgen_aux -- FIXME automate

    -- FIXME automate
    simp only [inv]
    dsimp

    -- FIXME automate this with custom tactic?
    rcases h with ⟨_, h⟩
    rcases h with ⟨_, _⟩

    and_intros
    omega
    omega
    omega
    constructor
    and_intros
    assumption
    apply List.Perm.length_eq
    assumption
  case h_1 =>
    mvcgen_aux -- FIXME automate

    next inv' i j hloi hihi hij s => 
    simp only at hihi hloi hij -- FIXME automate
    clear inv' -- FIXME

    -- FIXME these simplifications are related to the use of `Specs.forin_range`, and should be automatically applied whenever that spec is used
    simp only [List.length_reverse, List.length_range'] at h
    simp only [Nat.add_one_sub_one, Nat.div_one] at h

    -- FIXME we should have some `s'` made available from `mvcgen` so that we don't have to do this
    let xs' : Vector α n := ⟨s.xs.val.swap i (↑hi) sorry sorry, sorry⟩

    -- FIXME want to make these mvars that are assigned later on via unification (search space is too large otherwise)
    let l_lo := lo
    let l_hi := i
    let rt_lo := i + 1
    let rt_hi := (hi : Nat) + 1

    let l := xs'.1[l_lo:l_hi].toArray.toList
    let rt := xs'.1[rt_lo:rt_hi].toArray.toList

    have : l.length = i - lo := by sorry

    let test : (Nat × Nat) := (0, 1)
    let pi : Nat := i
    have pi_prf : pi < xs'.val.size := sorry
    exists l, rt, xs'.1[pi]'pi_prf

    -- let (a, b) := test
    have ⟨hj, hl, hrt, hM⟩ := h
    have hj : j = hi := by omega
    -- have : pi = i := by
    --   unfold pi
    --   set_option pp.proofs true in
    --   exact rfl
    subst hj
    and_intros
    omega
    . rcases hM with ⟨M', hM', hM'l⟩
      rw [Vector.toList, swap_array_decomp]
      rotate_left
      exact hM'
      omega
      omega
      omega
      omega
      simp only [sort] at *
      rw [List.append_assoc]
      simp only [sort] at *

      apply Eq.trans
      apply Eq.symm
      apply subarray_decomp
      . apply swap_array_decomp
        exact hM'
        omega
        omega
        omega
        omega

      conv =>
        lhs
        simp only 
        rw [ArrayToList.length_swap] -- FIXME investigate why rewriting breaks with size_swap
        simp only [Array.size]
        rw [hlo, hM'l, hhi]
      sorry
    .
      intro b
      rw [vec_subarray]
      rintro ⟨x, hx, ⟨h1, h2, rfl⟩⟩
      rw [Array.getElem_swap_left]
      simp only [sort] at *
      rw [Array.getElem_swap_of_ne (by have := s.xs.2; omega) (by omega) (by omega)] -- FIXME
      apply hl
      and_intros
      omega
      omega
      omega
    intro b
    rw [vec_subarray]
    rintro ⟨x, _, ⟨h1, h2, rfl⟩⟩
    rw [Array.getElem_swap_left]
    if h : x = hi then
      subst h
      simp only [sort]
      rw [Array.getElem_swap_right]
      apply hrt
      omega
      and_intros
      omega
      omega
    else
      simp only [sort]
      intros
      . rw [Array.getElem_swap_of_ne]
        rotate_left -- FIXME better way to restrict to JUST those introduced by `rw` above?
        have := s.xs.2 -- FIXME why?
        omega
        omega
        omega
        apply hrt
        omega
        . and_intros
          omega
          omega

  . next i j _ _ _ _ s hhihj =>
    mvcgen_aux -- FIXME automate

    rcases h with ⟨hj, hl, hr, hM⟩

    rw [List.length_cons]

    refine ⟨by omega, fun x hx => ?_, fun x hx => ?_, ?_⟩
    simp only [sort] at *
    if h' : x = i then
      subst h'
      simp only [Nat.lt_add_one, and_true]
      intro _
      apply le_asymm
      -- FIXME pattern-matching should really be powerful enough that we don't need to do this
      rw [Array.getElem_swap_left, Array.getElem_swap_of_ne (by have := s.xs.2; omega) (by omega) (by omega)] -- FIXME
      exact hhihj
    else
      intros
      rw [Array.getElem_swap_of_ne, Array.getElem_swap_of_ne]
      apply hl _
      all_goals omega
    simp only [sort] at *
    if h' : x = j then
      subst h'
      intros
      rw [Array.getElem_swap_right]
      rw [Array.getElem_swap_of_ne (by have := s.xs.2; omega) (by omega) (by omega)] -- FIXME
      apply hr i
      omega
      and_intros
      omega
      omega
    else
      intros
      rw [Array.getElem_swap_of_ne (by have := s.xs.2; omega) (by omega) (by omega)] -- FIXME
      rw [Array.getElem_swap_of_ne (by have := s.xs.2; omega) (by omega) (by omega)] -- FIXME
      apply hr
      omega
      omega
    rcases hM with ⟨M', hM', hM'l⟩
    rw [swap_array_decomp hM' _ _ (by omega) (by omega) (by omega) (by omega)] -- FIXME
    simp only [sort] at *
    constructor
    and_intros
    exact rfl -- FIXME why can't `apply` here?
    simp only [sort] at *
    assumption

  . next i j _ _ _ _ s hhihj =>
    mvcgen_aux -- FIXME automate

    rcases h with ⟨hj, hl, hr, hM⟩
    simp only [sort] at *
    
    and_intros
    . omega
    . intros
      apply hl
      assumption
    . intros x 
      intros
      if h' : x = j then
        subst h'
        assumption
      else
        apply hr
        omega
    assumption

-- #eval #[1, 2, 3, 4][1:3].toArray
theorem qsort_rec_perm (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
    (lo : Nat) (hi : Fin n) (L M R) (hlo : L.length = lo) (hhi : M.length > 0 → lo + M.length = hi + 1)
    :
   ⦃⌜(#xs).toList = L ++ M ++ R⌝⦄
   qsort_rec lt lo hi
   ⦃⇓ _ => ⌜∃ M', (#xs).1.toList = L ++ M' ++ R ∧ M'.Perm M⌝⦄ := by
  sorry

theorem qsort_rec_sorted (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
    (lo : Nat) (hi : Fin n) (L M R) (hlo : L.length = lo) (hhi : M.length > 0 → lo + M.length = hi + 1)
    :
   ⦃⌜(#xs).toList = L ++ M ++ R⌝⦄
   qsort_rec lt lo hi
   ⦃⇓ _ => ⌜∃ M', (#xs).1.toList = L ++ M' ++ R ∧ M'.Pairwise (fun a b => ¬lt b a)⌝⦄ := by
  if hM : M.length > 0 then
    unfold qsort_rec
    mintro h
    split
    -- TODO fix bug of state not changing/no errmsg when changing angle brackets to parens
    -- let this := (qpartition_triple le_asymm le_trans ⟨lo, sorry⟩ hi _ hlo (hhi hM))
    -- FIXME why need to specify R?
    . mspec (multiEntails (FPre := ⌜(#xs).toList = L ++ M ++ R⌝) (qpartition_sorted (R := R) le_asymm le_trans ⟨lo, _⟩ hi _ hlo (hhi hM)) (qpartition_perm (R := R) le_asymm le_trans ⟨lo, _⟩ hi _ hlo (hhi hM)) sorry sorry)
      next r =>
      mintro ∀s
      mpure h
      simp at h
      rcases r with ⟨pivot, p⟩
      simp at p
      rcases h with ⟨⟨l, hM', rt, a, hdec, hl, hrt⟩, ⟨_, hdec', hperm⟩⟩
      have := hdec.symm.trans hdec'
      simp only [List.append_right_inj, List.append_left_inj, List.cons_inj_right] at this
      rw [← List.cons_append, ← List.append_assoc] at this
      simp only [List.append_right_inj, List.append_left_inj, List.cons_inj_right] at this
      subst this
      have := hperm.length_eq
      simp at this
      simp at hM'
      split
      next as' mid hmlo hmhi heq =>
      rcases heq

      have hs1 := (qsort_rec_sorted le_asymm le_trans lo ⟨pivot - 1, sorry⟩ L l (a::rt ++ R) (by assumption) (by
         simp
         omega))
      have hp1 := (qsort_rec_perm (n := n) le_asymm le_trans lo ⟨pivot - 1, sorry⟩ L l (a::rt ++ R) (by assumption) (by
         simp
         omega))
      -- have := (multiEntails hs1 hp1 sorry sorry)
      mspec (multiEntails (FPre := ⌜(#xs).toList = L ++ l ++ (a :: rt ++ R)⌝) hs1 hp1 sorry sorry)
      case refl.pre1 =>
        simpa
      mintro ∀s'
      mpure h
      simp at h
      rcases h with ⟨⟨l', hl'dec, hl'sorted⟩, ⟨_, _hl'dec, hl'perm⟩⟩
      have := hl'dec.symm.trans _hl'dec
      simp only [List.append_right_inj, List.append_left_inj] at this
      subst this

      have hs2 := (qsort_rec_sorted le_asymm le_trans (pivot + 1) hi (L ++ l' ++ [a]) rt R sorry (by simp; omega))
      have hp2 := (qsort_rec_perm le_asymm le_trans (pivot + 1) hi (L ++ l' ++ [a]) rt R sorry (by simp; omega))
      mspec (multiEntails (FPre := ⌜(#xs).toList = L ++ l' ++ (a :: rt ++ R)⌝) hs2 hp2 sorry sorry)
      case intro.intro.intro.intro.intro.pre1 =>
        simpa
      mintro ∀s''
      mpure h
      simp at h
      rcases h with ⟨⟨rt', hrt'dec, hrt'sorted⟩, ⟨_, _hrt'dec, hrt'perm⟩⟩
      have := hrt'dec.symm.trans _hrt'dec
      simp only [List.append_right_inj, List.append_left_inj, List.cons_inj_right] at this
      subst this

      clear hs1 hs2 hp1 hp2
      -- simp at hl'dec
      mpure_intro
      simp
      refine ⟨l' ++ a::rt', by simpa, ?_⟩
      simp only [List.pairwise_append]
      simp only [List.pairwise_cons]
      -- simp only [forall_mem_cons, l'.mem_iff_get, rt'.mem_iff_get]
      simp only [List.forall_mem_cons]
      -- simp at hl'sorted
      simp at le_trans
      refine ⟨hl'sorted, ⟨fun x => ?_, hrt'sorted⟩, fun x h => ⟨?_, fun y h' => ?_⟩⟩
      rw [hrt'perm.mem_iff]
      apply hrt
      rw [hl'perm.mem_iff] at h
      apply (hl _ h)
      rw [hl'perm.mem_iff] at h
      rw [hrt'perm.mem_iff] at h'
      exact le_trans (hrt y h') (hl x h)
      -- simp_all
      -- assumption
      -- simpa
      -- simp only [pairwise_append, pairwise_cons, forall_mem_cons, rr.mem_iff, ll.mem_iff]
    have : lo = hi := sorry
    have : M.length = 1 := by omega
    mintro ∀s
    mpure h
    simp at h
    mpure_intro -- TODO should automatically remove `spred`
    simp [Bool.not_eq_true, SPred.and_nil, SPred.exists_nil]
    refine ⟨M, by rw [← h]; rfl, ?_⟩
    have : ∃ x, M = [x] := by sorry
    rw [this.choose_spec]
    simp
  else
    simp at hM
    subst hM
    sorry
termination_by hi - lo

-- FIXME
axiom _root_.Std.Do.StateM.by_wp' {σ : Type u} {s : σ} {α : Type u} {x : α × σ} {prog : StateM σ α}
  (h : StateT.run prog s = x) (P : α × σ → Prop) : (wp⟦prog⟧ (⇓a s' => ⌜P (a, s')⌝) s).down → P x

theorem qsort_spec (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c) (xs : Array α) :
   ⦃⌜True⌝⦄
   qsort xs lt
   ⦃⇓ xs' => ⌜xs'.toList.Pairwise (fun a b => ¬lt b a)⌝ ∧ ⌜xs'.Perm xs⌝⦄
   := by
  unfold qsort
  split
  . next h =>
    mintro -
    -- FIXME why can't I inline the proof as an argument to mspec, with holes for the args corresponding to those of the call to qsort'? Is the pattern matching that it does not powerful enough?
    have hs :=
     (qsort_rec_sorted le_asymm le_trans 0 ⟨xs.size - 1, by omega⟩ [] xs.toList [] rfl (by simp; omega) ) ⟨xs, rfl⟩ (by simp; rfl)
    have hp :=
     (qsort_rec_perm le_asymm le_trans 0 ⟨xs.size - 1, by omega⟩ [] xs.toList [] rfl (by simp; omega) ) ⟨xs, rfl⟩ (by simp; rfl)
    simp at hs
    simp at hp
    generalize h : (StateT.run (qsort_rec lt 0 ⟨xs.size - 1, _⟩) { xs := ⟨xs, _⟩ }) = x
    have hs := StateM.by_wp' h (fun (_, s) => List.Pairwise (fun a b => lt b a = false) s.xs.val.toList) hs
    have hp := StateM.by_wp' h (fun (_, s) => s.xs.val.toList.Perm xs.toList) hp
    simp at hs
    simp at hp
    mspec
    simp_all
    and_intros
    exact hs
    simp [Array.perm_iff_toList_perm]
    exact hp
  . next h =>
    simp at h
    subst h
    mintro -
    simp

theorem sorted (xs : Array α) {lt : α → α → Bool} (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c) :
    (qsort xs lt).run.toList.Pairwise (fun a b => ¬lt b a) ∧ (qsort xs lt).run.Perm xs := by
  exact qsort_spec le_asymm le_trans (α := α) xs True.intro
