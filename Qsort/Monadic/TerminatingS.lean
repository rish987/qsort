import MPL
import Batteries.Data.List.Perm
import Batteries.Data.List.Lemmas
import Qsort.AuxLemmas

open MPL

namespace MPL

open List

namespace Monadic

variable {α : Type} {n : Nat}

abbrev Vector (α n) := {xs : Array α // xs.size = n}

def Vector.get (xs : Vector α n) (i : Fin n) := xs.1[Fin.mk (i : Nat) (i.cast xs.2.symm).2]

def Vector.toList (xs : Vector α n) : List α := xs.1.toList

structure ST (α n) where
  xs : Vector α n

abbrev SM := StateM (ST α n)

abbrev ps := PostShape.arg (ST α n) PostShape.pure
variable (FPre : Assertion (ps))
variable {FPre1 FPre2 : Assertion (ps)}
variable {FPost1 FPost2 : PostCond T (ps)}

variable {F : StateM (ST α n) T}

theorem multiEntails (hF1 : ⦃FPre1⦄ F ⦃FPost1⦄) (hF2 : ⦃FPre2⦄ F ⦃FPost2⦄) (hFF1 : FPre ⊢ₛ FPre1) (hFF1 : FPre ⊢ₛ FPre2)
   : ⦃FPre⦄ F ⦃FPost1.and FPost2⦄ := by
  sorry

private abbrev gxs : SVal ((ST α n)::[]) (Vector α n) := fun s => SVal.pure s.xs

def xs : StateM (ST α n) (Vector α n) := do pure $ (← get).xs

def mxs (f : Vector α n → Vector α n) : StateM (ST α n) Unit := do modify fun s => {s with xs := f s.xs}

@[spec]
theorem xs_triple
    :
   ⦃P⦄
   xs (α := α) (n := n)
   ⦃⇓ r => P ∧ ⌜r = (#gxs)⌝⦄ := by
  unfold xs
  mvcgen

@[spec]
theorem mxs_triple
    :
   ⦃⌜#gxs = r⌝⦄
   mxs (α := α) (n := n) f
   ⦃⇓ _ => ⌜#gxs = f r⌝⦄ := by
  unfold mxs
  mintro h ∀s
  mpure h
  simp at h
  mvcgen
  simp
  congr

def qpartition_maybeSwap (lt : α → α → Bool) (lo hi : Fin n) : StateM (ST α n) Unit := do
  if lt ((← xs).get hi) ((← xs).get lo) then
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
  let pivot := (← xs).get hi
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
      let xs := (← xs) -- FIXME
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

def qsort' {n} (lt : α → α → Bool)
    (lo : Nat) (hi : Fin n) : StateM (ST α n) Unit := do
  if h : lo < hi.1 then
    let ⟨mid, (_ : lo ≤ mid), _⟩ ←
      qpartition lt ⟨lo, Nat.lt_trans h hi.2⟩ hi (Nat.le_of_lt h)
    qsort' lt lo ⟨mid - 1, by omega⟩
    qsort' lt (mid + 1) hi
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
    pure $ (qsort' lt 0 ⟨xs.size - 1, by omega⟩).run { xs := ⟨xs, rfl⟩ } |>.2.xs
  else pure xs

variable {lt : α → α → Bool} (lt_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)

theorem qpartition_maybeSwap_triple
    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi) {L M R : List α}
    (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi + 1)
    :
   ⦃⌜(#gxs).toList = L ++ M ++ R⌝⦄
   qpartition_maybeSwap lt lo hi
   ⦃⇓ _ => ⌜∃ (M' : List α),
     (#gxs).toList = L ++ M' ++ R ∧
     M'.Perm M⌝⦄ := by
  sorry

theorem qpartition_prep_triple
    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi) {L M R}
    (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi + 1)
    :
   ⦃⌜(#gxs).toList = L ++ M ++ R⌝⦄
   qpartition_prep lt lo hi
   ⦃⇓ _ => ⌜∃ (M' : List α),
     (#gxs).toList = L ++ M' ++ R ∧
     M'.Perm M⌝⦄ := by
  sorry

-- set_option pp.all true in
theorem qpartition_triple (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
    (lo : Fin n) (hi : Fin n) (hle : lo ≤ hi) {L M R}
    (hlo : L.length = lo.1) (hhi : lo.1 + M.length = hi + 1)
    :
   ⦃⌜(#gxs).toList = L ++ M ++ R⌝⦄
   qpartition lt lo hi hle
   ⦃⇓ pivot => ⌜∃ (l r : List α) (a : α),
     lo + l.length = pivot ∧
     (#gxs).toList = L ++ l ++ a::r ++ R ∧ (∀ b ∈ l, ¬lt a b) ∧ (∀ b ∈ r, ¬lt b a) ∧
     (l ++ a::r).Perm M⌝⦄ := by
  unfold qpartition
  mintro h
  mspec (qpartition_prep_triple (lt := lt) lo hi hle hlo hhi)
  mspec (xs_triple (P := ⌜∃ M', (#gxs).toList = L ++ M' ++ R ∧ M'.Perm M⌝))
  mspec 
  case inv => exact PostCond.total fun (⟨⟨i, j⟩, _⟩, sp) =>
    ⌜ j = lo + sp.rpref.length ∧
    ((∀ (n : Fin n), lo ≤ n ∧ n < i → ¬ lt ((#gxs).get hi) ((#gxs).get n))) ∧
    ((∀ (n : Fin n), i ≤ n ∧ n < j → ¬ lt ((#gxs).get n) ((#gxs).get hi))) ∧
    ∃ M', (#gxs).val.toList = L ++ M' ++ R ∧ M'.Perm M⌝
  case pre1 =>
    mintro ∀s
    mpure h
    simp at h
    -- rcases h with ⟨M, h, h'⟩
    simp
    refine ⟨by omega, by omega, h.1⟩
  case step =>
    intro iv rpref a rsuff _
    rcases iv with ⟨⟨i, j⟩, _⟩
    mintro h
    simp only
    -- mpure h
    -- simp at h
    -- rcases h with ⟨hj, hl, hr, hM⟩
    simp
    mintro ∀s
    mpure h
    simp at h
    rcases h with ⟨hj, hl, hr, hM⟩
    split
    next heq =>
    rcases heq
    split
    mspec (xs_triple (P := fun s' => s = s'))
    mintro ∀s'
    mpure h
    have : s = s' ∧ r = s'.xs := h
    rcases h with ⟨rfl, rfl⟩
    split
    . next hhihj =>
      mspec
      mpure_intro
      refine ⟨by omega, fun x => ?_, fun x => ?_, ?_⟩
      if h' : x = i then
        subst h'
        simp at le_asymm
        simp
        refine fun _ => le_asymm ?_
        simp only [Vector.get, Fin.getElem_fin]
        rw [Array.getElem_swap_left, Array.getElem_swap_of_ne (by have := s.xs.2; omega) (by omega) (by omega)]
        exact hhihj
      else
        simp
        refine fun _ _ => ?_
        rw [Vector.get, Fin.getElem_fin]
        simp only [Vector.get, Fin.getElem_fin]
        rw [Array.getElem_swap_of_ne, Array.getElem_swap_of_ne]
        apply hl _
        all_goals omega
      if h' : x = j then
        simp -- FIXME
        subst h'
        rintro _ _
        simp [Vector.get, Fin.getElem_fin]
        rw [Array.getElem_swap_of_ne (by have := s.xs.2; omega) (by omega) (by omega)]
        apply hr ⟨i, by omega⟩
        simp only [Nat.le_refl]
        simp only
        omega
      else
        -- refine fun _ => ?_
        -- have : x < i := by omega
        -- have : (x : Nat) ≠ i := by omega
        -- have : (x : Nat) ≠ j := by omega
        -- have hhixs : r'.1[x] = xs'.1[x] := Array.getElem_swap_of_ne xs'.1 (i := i) (j := j) (k := x) (hi := by get_elem_tactic) (hj := by get_elem_tactic) (by omega) (by omega) (by omega)
        -- rw [← hrdef, Vector.get, Fin.getElem_fin]
        -- unfold Vector.get
        -- simp only [Fin.getElem_fin] at hhixs
        -- simp only [Fin.getElem_fin]
        -- rw [hhixs]
        -- simp
        -- apply hl _
        -- all_goals omega
        sorry
      sorry
    sorry
    -- have : j < hi := by omega
    have : (rpref.reverse ++ a :: rsuff).length = hi - lo := by sorry
    simp at this
    have : rpref.length + lo < hi := by omega
    subst hj
    rw [Nat.add_comm] at this
    contradiction
  rcases r with ⟨⟨i, j⟩, _⟩
  mintro ∀s
  mpure h
  simp at h
  rcases h with ⟨hj, hl, hrt, hM⟩
  have hj : j = hi := by omega
  rcases hj
  split
  next heq =>
  rcases heq
  -- let r := xs'.val.swap i hi _ _
  mspec
  mintro ∀s'
  mpure h
  simp at h
  let r := s'.xs
  have hr : r = s'.xs := rfl
  let l := s'.xs.1[lo:i].toArray.toList
  let rt := s'.xs.1[i + 1:hi + 1].toArray.toList
  have : l.length = i - lo := by sorry
  have : rt.length = (hi + 1) - (i + 1) := by sorry
  -- have : M.length = hi + 1 - lo := by omega
  have hrt' : ∀ (b : α), b ∈ rt ↔ ∃ (x : Fin n), i < x ∧ x ≤ hi ∧ s'.xs.get x = b := sorry
  mpure_intro
  simp
  rw [h]
  rw [h] at hr
  refine ⟨l, by omega, rt, r.1[i]'(by have := r.2; sorry /- FIXME omega here breaks pattern-matching -/ ), sorry, ?_, ?_, sorry⟩
  .
    rw [hr]
    have hl' : ∀ (b : α), b ∈ l ↔ ∃ (x : Fin n), lo ≤ x ∧ x < i ∧ r.get x = b := sorry
    rw [hr] at hl'
    intro b
    rw [hl']
    rintro ⟨x, ⟨h1, h2, rfl⟩⟩
    rw [Array.getElem_swap_left]
    intros
    simp [Vector.get]
    rw [Array.getElem_swap_of_ne (by have := s.xs.2; omega) (by omega) (by omega)]
    exact (hl ⟨x, by omega⟩ (by simp; omega) (by simp; omega))
  intro b
  rw [hrt']
  rintro ⟨x, ⟨h1, h2, rfl⟩⟩
  unfold r
  rw [h]
  if h : x = hi then
    simp [Vector.get]
    intros
    rw [h, Array.getElem_swap_right]
    exact (hrt ⟨i, by omega⟩ (by simp) (by simp; omega))
  else
    simp [Vector.get]
    intros
    -- have hr : r.val[(x : Nat)] = xs'.val[(x : Nat)] := Array.getElem_swap_of_ne (by omega) (by omega) (by omega)
    rw [Array.getElem_swap_of_ne (by have := s.xs.2; omega) (by omega) (by omega)]
    exact (hrt ⟨x, by omega⟩ (by simp; omega) (by simp; omega))

-- #eval #[1, 2, 3, 4][1:3].toArray
theorem perm_triple' (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
    (lo : Nat) (hi : Fin n) (L M R) (hlo : L.length = lo) (hhi : M.length > 0 → lo + M.length = hi + 1)
    :
   ⦃⌜(#gxs).toList = L ++ M ++ R⌝⦄
   qsort' lt lo hi
   ⦃⇓ _ => ⌜∃ M', (#gxs).1.toList = L ++ M' ++ R ∧ M'.Perm M⌝⦄ := by
  sorry

theorem sorted_triple' (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c)
    (lo : Nat) (hi : Fin n) (L M R) (hlo : L.length = lo) (hhi : M.length > 0 → lo + M.length = hi + 1)
    :
   ⦃⌜(#gxs).toList = L ++ M ++ R⌝⦄
   qsort' lt lo hi
   ⦃⇓ _ => ⌜∃ M', (#gxs).1.toList = L ++ M' ++ R ∧ M'.Pairwise (fun a b => ¬lt b a)⌝⦄ := by
  if hM : M.length > 0 then
    unfold qsort'
    mintro h
    split
    -- TODO fix bug of state not changing/no errmsg when changing angle brackets to parens
    -- let this := (qpartition_triple le_asymm le_trans ⟨lo, sorry⟩ hi _ hlo (hhi hM))
    . mspec (qpartition_triple le_asymm le_trans ⟨lo, _⟩ hi _ hlo (hhi hM))
      mintro ∀s
      mpure h
      simp at h
      rcases r with ⟨pivot, p⟩
      simp at p
      rcases h with ⟨l, hM', rt, a, _, hl, hrt, hperm⟩
      have := hperm.length_eq
      simp at this
      simp at hM'
      split
      next as' mid hmlo hmhi heq =>
      rcases heq

      have hs1 := (sorted_triple' le_asymm le_trans lo ⟨pivot - 1, sorry⟩ L l (a::rt ++ R) (by assumption) (by
         simp
         omega))
      have hp1 := (perm_triple' (n := n) le_asymm le_trans lo ⟨pivot - 1, sorry⟩ L l (a::rt ++ R) (by assumption) (by
         simp
         omega))
      -- have := (multiEntails hs1 hp1 sorry sorry)
      mspec (multiEntails (FPre := ⌜(#gxs).toList = L ++ l ++ (a :: rt ++ R)⌝) hs1 hp1 sorry sorry)
      case refl.pre1 =>
        simpa
      mintro ∀s'
      mpure h
      simp at h
      rcases h with ⟨⟨l', hl'dec, hl'sorted⟩, ⟨_, _hl'dec, hl'perm⟩⟩
      have := hl'dec.symm.trans _hl'dec
      simp only [List.append_right_inj, List.append_left_inj] at this
      subst this

      have hs2 := (sorted_triple' le_asymm le_trans (pivot + 1) hi (L ++ l' ++ [a]) rt R sorry (by simp; omega))
      have hp2 := (perm_triple' le_asymm le_trans (pivot + 1) hi (L ++ l' ++ [a]) rt R sorry (by simp; omega))
      mspec (multiEntails (FPre := ⌜(#gxs).toList = L ++ l' ++ (a :: rt ++ R)⌝) hs2 hp2 sorry sorry)
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

theorem sorted_triple (le_asymm : ∀ {{a b}}, lt a b → ¬lt b a) (le_trans : ∀ {{a b c}}, ¬lt a b → ¬lt b c → ¬lt a c) (xs : Array α) :
   ⦃⌜True⌝⦄
   qsort xs lt
   ⦃⇓ xs' => xs'.toList.Pairwise (fun a b => ¬lt b a) ∧ xs'.Perm xs⦄
   := by
  unfold qsort
  split
  . next h =>
    mintro -
    -- FIXME why can't I inline the proof as an argument to mspec, with holes for the args corresponding to those of the call to qsort'? Is the pattern matching that it does not powerful enough?
    have hs :=
     (sorted_triple' le_asymm le_trans 0 ⟨xs.size - 1, by omega⟩ [] xs.toList [] rfl (by simp; omega) ) ⟨xs, rfl⟩ (by simp; rfl)
    have hp :=
     (perm_triple' le_asymm le_trans 0 ⟨xs.size - 1, by omega⟩ [] xs.toList [] rfl (by simp; omega) ) ⟨xs, rfl⟩ (by simp; rfl)
    simp at hs
    simp at hp
    generalize h : (StateT.run (qsort' lt 0 ⟨xs.size - 1, _⟩) { xs := ⟨xs, _⟩ }) = x
    have hs := StateM.by_wp h (fun (_, s) => List.Pairwise (fun a b => lt b a = false) s.xs.val.toList) hs
    have hp := StateM.by_wp h (fun (_, s) => s.xs.val.toList.Perm xs.toList) hp
    simp at hs
    simp at hp
    mspec
    simp_all
    split_ands
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
  exact sorted_triple le_asymm le_trans (α := α) xs True.intro
