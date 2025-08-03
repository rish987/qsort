import Std.Tactic.Do
import Qsort.AuxLemmas
import Qsort.Monadic.Aux

set_option mvcgen.warning false

open Std.Do
open List

namespace Monadic.Qpartition

variable {α : Type} {n : Nat}

abbrev Vector (α n) := {xs : Array α // xs.size = n}

def Vector.get (xs : Vector α n) (i : Nat) (hi : i < n) := xs.1[i]'(by omega)

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

-- FIXME should be able to derive this triple, ideally
@[spec]
theorem mxs_triple
    :
   ⦃fun s => Q.1 () ({s with xs := f s.xs})⦄
   mxs (α := α) (n := n) f
   ⦃Q⦄ := by
  unfold mxs
  mvcgen

def Stable (as bs : Vector α n) (lo hi : Nat) (hlo : lo < n := by omega) (hhi : hi < n := by omega) : Prop :=
     ∀ i, i < lo → as.get i = bs.get i ∧
     ∀ i, i > hi → as.get i = bs.get i

def Perm (as bs : Vector α n) : Prop :=
  as.1.Perm bs.1

theorem pred_range_single {P : Nat → Prop} (i : Nat) (h : P i)
   : ∀ j, i ≤ j → j < i + 1 → P j := by
  intros j
  intros
  have : i = j := by omega
  subst this
  assumption

theorem pred_range_extend {P : Nat → Prop} (lo mid hi : Nat)
   (h1 : ∀ j, lo ≤ j → j < mid → j < hi → P j)
   (h2 : ∀ j, mid ≤ j → j < hi → lo ≤ j → P j) : ∀ j, lo ≤ j → j < hi → P j := by
  intro j _ _
  if _ : j < mid then
    apply h1
    omegas
  else
    apply h2
    omegas

theorem ne_of_lt (i j : Nat) (h : i < j) : ¬ i = j := by sorry

theorem lt_of_ne (i j : Nat) (h1 : i ≤ j) (h2 : ¬ i = j) : i < j := by sorry
theorem ne_symm (i j : Nat) (h : ¬ i = j) : ¬ j = i := by sorry
theorem eq_trans (i j k : Nat) (h1 : i = j) (h2 : j = k) : i = k := by sorry
theorem eq_comm (i j : Nat) (h : i = j) : j = i := by sorry
theorem add_sub (i j : Nat) (h : i ≤ j) : i + (j - i) = j := by sorry

namespace Vector

namespace swap
variable (i j : Nat) 

theorem stable {as bs : Vector α n} {lo hi : Nat} (hlo : lo < n) (hhi : hi < n) (h : Stable as bs lo hi)
   (hilo : i ≥ lo) (hihi : i ≤ hi) (hjlo : j ≥ lo) (hjhi : j ≤ hi)
   : Stable (as.swap i j) bs lo hi := by
  sorry

theorem get_left {xs : Vector α n} {i j : Nat} (hi : i < n) (hj : j < n) :
   (xs.swap i j hi hj).get i hi = xs.get j hj := by
  sorry

theorem get_right {xs : Vector α n} {i j : Nat} (hi : i < n) (hj : j < n) :
   (xs.swap i j hi hj).get j hj = xs.get i hi := by
  sorry

theorem get_other {xs : Vector α n} {i j : Nat} (k : Nat)
   (hi : i < n) (hj : j < n) (hk : k < n)
   (hi' : k ≠ i) (hj' : k ≠ j) :
   (xs.swap i j hi hj).get k hk = xs.get k hk := by
  sorry

end swap
end Vector

def qpartition_maybeSwap (lt : α → α → Bool) (lo hi : Nat) (hlo : lo < n) (hhi: hi < n) : StateM (ST α n) Unit := do
  if lt ((← get).xs.get hi hhi) ((← get).xs.get lo hlo) then
    mxs fun xs => xs.swap lo hi

def qpartition_prep
    (lt : α → α → Bool) (lo hi : Nat) (hlo : lo < n) (hhi: hi < n):
    StateM (ST α n) Unit := do
  let mid : Fin n := ⟨(lo + hi) / 2, by omega⟩
  qpartition_maybeSwap lt lo mid hlo mid.2
  qpartition_maybeSwap lt lo hi hlo hhi
  qpartition_maybeSwap lt hi mid hhi mid.2

theorem qpartition_maybeSwap_perm {lo hi : Nat} (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi := by omega) :
   ⦃⌜#gxs = xs⌝⦄
   qpartition_maybeSwap lt lo hi hlo hhi
   ⦃⇓ pivot => ⌜Stable #gxs xs lo hi hlo hhi ∧ (#gxs).1.Perm xs.1⌝⦄ := by
  sorry

namespace qpartition_prep
theorem nil {lo hi : Nat} (hlo : lo < n := by omega) (hhi : hi < n := by omega)(hle : lo ≤ hi := by omega) :
   ⦃⌜True⌝⦄
   qpartition_prep lt lo hi hlo hhi
   ⦃⇓ _ => ⌜True⌝⦄ := by
  sorry

theorem stable {lo hi : Nat} (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi := by omega) :
   ⦃⌜#gxs = xs⌝⦄
   qpartition_prep lt lo hi hlo hhi
   ⦃⇓ pivot => ⌜Stable #gxs xs lo hi hlo hhi⌝⦄ := by
  sorry

-- @[spec]
theorem perm {lo hi : Nat} (hlo : lo < n := by omega) (hhi : hi < n := by omega) (hle : lo ≤ hi := by omega) :
   ⦃⌜#gxs = xs⌝⦄
   qpartition_prep lt lo hi hlo hhi
   ⦃⇓ pivot => ⌜(#gxs).1.Perm xs.1⌝⦄ := by
  sorry
end qpartition_prep

-- attribute [sort] Fin.getElem_fin Array.length_toList Array.size_swap List.append_left_inj List.append_right_inj List.length_cons
