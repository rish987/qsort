import MPL
import Batteries.Data.List.Perm
import Batteries.Data.List.Lemmas
import Qsort.AuxLemmas

open MPL

namespace MPL
variable (T S : Type)
abbrev ps := (PostShape.arg S PostShape.pure)

variable (FPre FPre1 FPre2 : Assertion (ps S))
variable (FPost1 FPost2 : PostCond T (ps S))

variable (F : StateM S T)
variable (hF1 : ⦃FPre1⦄ F ⦃FPost1⦄)
variable (hF2 : ⦃FPre2⦄ F ⦃FPost2⦄)
variable (test : ⦃FPre⦄ F ⦃FPost1.and FPost2⦄)
variable (hFF1 : FPre ⊢ₛ FPre1)
variable (hFF1 : FPre ⊢ₛ FPre2)


theorem multiEntails 
(hF1 : ⦃FPre1⦄ F ⦃FPost1⦄) (hF2 : ⦃FPre2⦄ F ⦃FPost2⦄) (hFF1 : FPre ⊢ₛ FPre1) (hFF1 : FPre ⊢ₛ FPre2)
 : ⦃FPre⦄ F ⦃FPost1.and FPost2⦄ := by
  sorry

open List

namespace Monadic

abbrev Vector (α n) := {xs : Array α // xs.size = n}

def Vector.get (xs : Vector α n) (i : Fin n) := xs.1.get i (i.cast xs.2.symm).2

def Vector.toList (xs : Vector α n) : List α := xs.1.toList

def qpartition_maybeSwap (xs : Vector α n) (lt : α → α → Bool) (lo hi : Fin n) : Idd $ Vector α n :=
    let hi := hi.cast xs.2.symm
    let lo := lo.cast xs.2.symm
    if lt (xs.1[hi]) (xs.1[lo]) then
      pure ⟨xs.1.swap lo hi, (Array.size_swap ..).trans xs.2⟩
    else pure xs

theorem qpartition_maybeSwap_triple (xs : Vector α n)
    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi) {L M R}
    (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi + 1)
    (hxs : xs.1.toList = L ++ M ++ R)
    :
   ⦃⌜True⌝⦄
   qpartition_maybeSwap xs lt lo hi
   ⦃⇓ (xs') => ∃ (M' : List α),
     M'.length = M.length ∧
     xs'.1.toList = L ++ M' ++ R ∧
     M'.Perm M⦄ := by
  sorry

def qpartition_prep (xs : Vector α n)
    (lt : α → α → Bool) (lo hi : Fin n) :
    Idd $ Vector α n := do
  let mid : Fin n := ⟨(lo.1 + hi) / 2, by omega⟩
  let mut xs := xs
  xs ← qpartition_maybeSwap xs lt lo mid
  xs ← qpartition_maybeSwap xs lt lo hi
  xs ← qpartition_maybeSwap xs lt hi mid
  pure xs

theorem qpartition_prep_triple (xs : Vector α n)
    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi) {L M R}
    (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi + 1)
    (hxs : xs.1.toList = L ++ M ++ R)
    :
   ⦃⌜True⌝⦄
   qpartition_prep xs lt lo hi
   ⦃⇓ (xs') => ∃ (M' : List α),
     M'.length = M.length ∧
     xs'.1.toList = L ++ M' ++ R ∧
     M'.Perm M⦄ := by
  sorry

-- FIXME why do `xs` binders produce errors when importing MPL
/-- Partitions `xs[lo..=hi]`, returning a pivot point and the new array. -/
@[inline] def qpartition (xs : Vector α n)
    (lt : α → α → Bool) (lo hi : Fin n) (hle : lo ≤ hi) :
    Idd $ Vector α n × {pivot : Nat // lo ≤ pivot ∧ pivot ≤ hi} := do
  let mut xs ← qpartition_prep xs lt lo hi
  let pivot := xs.1[hi.cast xs.2.symm]
  -- we must keep track of i and j and their respective properties all together within a single subtype,
  -- because these dependent properties must be shown in parallel to reassigning the indices
  let mut inv : {t : Nat × Nat // lo ≤ t.1 ∧ t.1 ≤ hi ∧ t.1 ≤ t.2} := ⟨(lo, lo), by omega, by omega⟩
  -- let mut i : Nat := lo
  -- let mut ihs : lo ≤ i ∧ i ≤ hi := sorry
  for _ in [lo:hi] do
    let mut ⟨(i, j), hloi, hihi, hij⟩ := inv
    -- NOTE: `j < hi` is actually always the case. It would be easy to show if we could somehow bind `j`
    -- and the invariant properties in the `for` loop syntax rather than bundling it into `inv`, however this is not possible at the moment.
    -- Therefore, showing it is deferred to the correctness proof for now.
    if hjhi : j < hi then
      have _ : i < hi := Nat.lt_of_le_of_lt hij hjhi
      if lt (xs.1[j]) pivot then
        xs := ⟨xs.1.swap i j, (Array.size_swap ..).trans xs.2⟩
        i := i + 1
        j := j + 1
        inv := ⟨(i, j), Nat.le_succ_of_le hloi, by omega, by omega⟩
      else
        j := j + 1
        inv := ⟨(i, j), hloi, by omega, by omega⟩
  let ⟨(i, _), hloi, hihi, _⟩ := inv
  xs ← pure ⟨xs.1.swap i hi, (Array.size_swap ..).trans xs.2⟩
  pure ⟨xs, ⟨i, hloi, hihi⟩⟩
  -- loop xs lo lo ⟨Nat.le_refl _, Nat.le_refl _, hle⟩

-- hi - lo > hi - mid - 1
-- - lo > - mid - 1
-- lo < mid + 1
-- hi > mid - 1
def qsort' {n} (lt : α → α → Bool) (xs : Vector α n)
    (lo : Nat) (hi : Fin n) : Idd (Vector α n) := do
  if h : lo < hi.1 then
    let ⟨as', mid, (_ : lo ≤ mid), _⟩ ←
      qpartition xs lt ⟨lo, Nat.lt_trans h hi.2⟩ hi (Nat.le_of_lt h)
    let mut xs := as'
    xs ← qsort' lt xs lo ⟨mid - 1, by omega⟩
    xs ← qsort' lt xs (mid + 1) hi
    pure xs
  else pure xs
termination_by hi - lo
-- decreasing_by
--   unfold newHi at *
--   simp_all
--   omega
--   unfold newHi at *
--   simp_all
--   omega
-- #print qsort'._unary
-- #print qsort'.eq_def

/-- Sort the array `xs[low..=high]` using comparator `lt`. -/
@[inline] def qsort (xs : Array α) (lt : α → α → Bool) :
    Idd (Array α) := do
  if h : xs.size > 0 then
    pure (← qsort' lt ⟨xs, rfl⟩ 0 ⟨xs.size - 1, by omega⟩).1
  else pure xs

theorem qpartition_triple (xs : Vector α n)
    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi) {L M R}
    (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi + 1)
    (hxs : xs.1.toList = L ++ M ++ R)
    :
   ⦃⌜True⌝⦄
   qpartition xs lt lo hi hle
   ⦃⇓ (xs', pivot) => ∃ (l r : List α) (a : α),
     M.length = l.length + 1 + r.length ∧
     lo + l.length = pivot ∧
     xs'.1.toList = L ++ l ++ a::r ++ R ∧ (∀ b ∈ l, ¬lt a b) ∧ (∀ b ∈ r, ¬lt b a) ∧
     (l ++ a::r).Perm M⦄ := by
  unfold qpartition
  mintro -
  mwp
  let this :
    ⦃⌜True⌝⦄
      qpartition_prep xs lt lo hi
    ⦃⇓xs' => ∃ M', M'.length = M.length ∧ xs'.val.toList = L ++ M' ++ R ∧ M'.Perm M⦄ := (qpartition_prep_triple (lt := lt) xs lo hi hle hlo hhi hxs)
  mspec this
  mspec Specs.forIn_list ?inv ?step
  case inv => exact PostCond.total fun (⟨⟨(i, j), _⟩, xs'⟩, sp) =>
    j = lo + sp.rpref.length ∧
    ((∀ (n : Fin n), lo ≤ n ∧ n < i → ¬ lt (xs'.get hi) (xs'.get n))) ∧
    ((∀ (n : Fin n), i ≤ n ∧ n < j → ¬ lt (xs'.get n) (xs'.get hi))) ∧
    ∃ M', M'.length = M.length ∧ xs'.val.toList = L ++ M' ++ R ∧ M'.Perm M
  case pre => sorry
  case step => sorry
  rcases r with ⟨⟨⟨i, j⟩, _⟩, xs'⟩
  mpure h
  simp at h
  rcases h with ⟨hj, hl, hrt, hM⟩
  have hj : j = hi := by omega
  rcases hj
  mwp
  split
  next heq =>
  rcases heq
  -- let r := xs'.val.swap i hi _ _
  mspec
  have hin : i < n := by get_elem_tactic
  let r : Vector α n := ⟨xs'.1.swap i hi, (Array.size_swap ..).trans xs'.2⟩
  let a := r.1[i]
  have : a = xs'.get hi := sorry
  have hrt' : ∀ (x : Fin n), i < x → x ≤ hi → lt (r.get x) a = false := sorry
  have hl' : ∀ (x : Fin n), lo ≤ x → x < i → lt a (r.get x) = false := sorry
  mwp
  let M' := r.1[lo:hi + 1].toArray.toList
  let l := r.1[lo:i].toArray.toList
  let rt := r.1[i + 1:hi + 1].toArray.toList
  mpure_intro
  simp
  have : l.length = i - lo := by sorry
  have : rt.length = (hi + 1) - (i + 1) := by sorry
  have : M.length = hi + 1 - lo := by omega
  refine ⟨l, rt, by omega, by omega, a, sorry, sorry, sorry, sorry⟩

#eval #[1, 2, 3, 4][1:3].toArray

variable (lt : α → α → Bool) (lt_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)

theorem sorted_triple' {lt : α → α → Bool} (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c) (xs : Vector α n)
    (lo : Nat) (hi : Fin n) (L M R) (hlo : L.length = lo) (hhi : M.length > 0 → lo + M.length = hi + 1)
    (hxs : xs.1.toList = L ++ M ++ R)
    :
   ⦃⌜True⌝⦄
   qsort' lt xs lo hi
   ⦃⇓ xs' => ∃ M', M'.length = M.length ∧ xs'.1.toList = L ++ M' ++ R ∧ M'.Pairwise (fun a b => ¬lt b a) ∧ M'.Perm M⦄ := by
  if hM : M.length > 0 then
    unfold qsort'
    mintro -
    mwp
    split
    -- TODO fix bug of state not changing/no errmsg when changing angle brackets to parens
    . mspec (qpartition_triple _ _ _ _ hlo (hhi hM) hxs)
      mpure h
      rcases r with ⟨xs', pivot⟩
      rcases h with ⟨l, rt, a, hMlrt, hM', hxs', hl, hrt, hlrP⟩
      split
      next as' mid hmlo hmhi heq =>
      simp at heq
      rcases heq.1
      rcases heq.2
      simp at hM'
      simp at hxs'
      -- cases
      -- mwp
      have :
       ⦃⌜True⌝⦄
       qsort' lt xs' lo ⟨mid - 1, by omega⟩
       ⦃⇓ ret => ∃ l', l'.length = l.length ∧ ret.1.toList = L ++ l' ++ (a::rt ++ R) ∧ l'.Pairwise (fun a b => ¬lt b a) ∧ l'.Perm l⦄ :=
       (sorted_triple' le_trans xs' lo ⟨mid - 1, by omega⟩ L l (a::rt ++ R) (by assumption) (by
         simp
         omega) (by simp_all))
      mspec this
      mpure h
      rcases h with ⟨l', hl'eq, hl'dec, hl'sorted, hpl'⟩
      simp at hl'dec
      have :
       ⦃⌜True⌝⦄
       qsort' lt r (mid + 1) hi
       ⦃⇓ ret => ∃ rt', rt'.length = rt.length ∧ ret.1.toList = (L ++ l' ++ [a]) ++ rt' ++ R ∧ rt'.Pairwise (fun a b => ¬lt b a) ∧ rt'.Perm rt⦄ :=
       (sorted_triple' le_trans r (mid + 1) hi (L ++ l' ++ [a]) rt R (by simp; subst hlo; rw [hl'eq]; omega) (by simp; omega) (by simpa))
      mspec this
      mwp
      mpure h
      mpure_intro
      simp
      simp at h
      rcases h with ⟨rt', hrt'eq, hrt'dec, hrt'sorted, hprt'⟩
      refine ⟨l' ++ a::rt', sorry, by simpa, ?_⟩
      simp only [List.pairwise_append]
      simp only [List.pairwise_cons]
      -- simp only [forall_mem_cons, l'.mem_iff_get, rt'.mem_iff_get]
      simp only [List.forall_mem_cons]
      simp at hl'sorted
      simp at hl
      simp at hrt
      simp at le_trans
      refine ⟨⟨hl'sorted, ⟨fun x => ?_, hrt'sorted⟩, fun x h => ⟨?_, fun y h' => ?_⟩⟩, ?_⟩
      rw [hprt'.mem_iff]
      apply hrt
      rw [hpl'.mem_iff] at h
      apply (hl _ h)
      rw [hpl'.mem_iff] at h
      rw [hprt'.mem_iff] at h'
      exact le_trans (hrt y h') (hl x h)
      sorry
      -- simp only [pairwise_append, pairwise_cons, forall_mem_cons, rr.mem_iff, ll.mem_iff]
    have : lo = hi := sorry
    have : M.length = 1 := by omega
    mpure_intro -- TODO should automatically remove `spred`
    simp only [Bool.not_eq_true, SPred.and_nil, SPred.exists_nil]
    refine ⟨M, rfl, hxs, ?_⟩
    have : ∃ x, M = [x] := by sorry
    rw [this.choose_spec]
    simp
  else
    simp at hM
    sorry
termination_by hi - lo

theorem sorted_triple {lt : α → α → Bool} (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c) (xs : Array α) :
   ⦃⌜True⌝⦄
   qsort xs lt
   ⦃⇓ xs' => xs'.toList.Pairwise (fun a b => ¬lt b a)⦄
   := by
  unfold qsort
  split
  . next h =>
    mintro -
    mwp
    -- FIXME why can't I inline the proof as an argument to mspec, with holes for the args corresponding to those of the call to qsort'? Is the pattern matching that it does not powerful enough?
    have :
     ⦃⌜True⌝⦄
     qsort' lt ⟨xs, rfl⟩ 0 ⟨xs.size - 1, by omega⟩
     ⦃⇓ xs' => ∃ M', M'.length = xs.toList.length ∧ xs'.1.toList = [] ++ M' ++ [] ∧ M'.Pairwise (fun a b => ¬lt b a) ∧ M'.Perm xs.toList⦄ :=
     (sorted_triple' le_trans ⟨xs, rfl⟩ 0 ⟨xs.size - 1, by omega⟩ [] xs.toList [] rfl (by simp; omega) (by simp))
    mspec this
    mpure h
    simp_all
    rcases h with ⟨_, _, h, r, _⟩
    simpa [h]
  . next h =>
    simp at h
    subst h
    mintro -
    mwp
    simp

theorem sorted (xs : Array α) {lt : α → α → Bool} (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c) :
    (qsort xs lt).run.toList.Pairwise (fun a b => ¬lt b a) := by
  exact sorted_triple le_trans (α := α) xs True.intro
