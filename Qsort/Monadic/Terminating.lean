import Batteries.Data.List.Perm
import Batteries.Data.List.Lemmas
import Qsort.AuxLemmas

namespace Monadic

/-- Partitions `as[lo..=hi]`, returning a pivot point and the new array. -/
@[inline] def qpartition' (as : {as : Array α // as.size = n})
    (lt : α → α → Bool) (lo hi : Fin n) (hle : lo ≤ hi) :
    Id $ {as : Array α // as.size = n} × {pivot : Nat // lo ≤ pivot ∧ pivot ≤ hi} := do
  let mid : Fin n := ⟨(lo.1 + hi) / 2, by omega⟩
  let rec
  /-- Swaps `lo` and `hi` if needed to ensure `as[lo] ≤ as[hi]`. -/
  @[inline] maybeSwap
      (as : {as : Array α // as.size = n}) (lo hi : Fin n) : {as : Array α // as.size = n} :=
    let hi := hi.cast as.2.symm
    let lo := lo.cast as.2.symm
    if lt (as.1[hi]) (as.1[lo]) then
      ⟨as.1.swap lo hi, (Array.size_swap ..).trans as.2⟩
    else as
  let mut as := as
  as := maybeSwap as lo mid
  as := maybeSwap as lo hi
  as := maybeSwap as hi mid
  let pivot := as.1[hi.cast as.2.symm]
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
      if lt (as.1[j]) pivot then
        as := ⟨as.1.swap i j, (Array.size_swap ..).trans as.2⟩
        i := i + 1
        j := j + 1
        inv := ⟨(i, j), Nat.le_succ_of_le hloi, by omega, by omega⟩
      else
        j := j + 1
        inv := ⟨(i, j), hloi, by omega, by omega⟩
  let ⟨(i, _), hloi, hihi, _⟩ := inv
  as := ⟨as.1.swap i hi, (Array.size_swap ..).trans as.2⟩
  pure ⟨as, ⟨i, hloi, hihi⟩⟩
  -- loop as lo lo ⟨Nat.le_refl _, Nat.le_refl _, hle⟩

-- hi - lo > hi - mid - 1
-- - lo > - mid - 1
-- lo < mid + 1
-- hi > mid - 1
def qsort' {n} (lt : α → α → Bool) (as : {as : Array α // as.size = n})
    (lo : Nat) (hi : Fin n) : Id {as : Array α // as.size = n} := do
  if h : lo < hi.1 then
    let ⟨as', mid, (_ : lo ≤ mid), _⟩ :=
      qpartition' as lt ⟨lo, Nat.lt_trans h hi.2⟩ hi (Nat.le_of_lt h)
    let mut as := as'
    as := qsort' lt as lo ⟨mid - 1, by omega⟩
    as := qsort' lt as (mid + 1) hi
    pure as
  else as
termination_by hi - lo

/-- Sort the array `as[low..=high]` using comparator `lt`. -/
@[inline] def qsort (as : Array α) (lt : α → α → Bool) :
    Id (Array α) :=
  if h : as.size > 0 then
    (qsort' lt ⟨as, rfl⟩ 0 ⟨as.size - 1, by omega⟩).1
  else as
