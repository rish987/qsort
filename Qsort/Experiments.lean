import MPL

open MPL

theorem EStateM.by_wp' {α} {x : EStateM.Result ε σ α} {prog : EStateM ε σ α} (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop) :
  ((wp prog).apply (post⟨fun a s' => P (EStateM.Result.ok a s'), fun e s' => P (EStateM.Result.error e s')⟩) s) → P x := by
  intro hspec
  simp [wp, PredTrans.pure] at hspec
  split at hspec <;> case _ _ _ heq => rw[← heq] at hspec; exact h ▸ hspec

partial def List.findIndex! (xs : List α) (p : α → Bool) : EStateM Unit Unit Nat := do
  match xs with
  | [] => throw ()
  | x::ys => do
    if p x then
      pure 0
    else
      let r ← List.findIndex! ys p
      pure (r + 1)
-- partial_fixpoint

def List.findIndex!_fmap
  (f : (xs : List α) → (p : α → Bool) → EStateM Unit Unit Nat)
  (xs : List α) (p : α → Bool) : EStateM Unit Unit Nat := do
  match xs with
  | [] => throw ()
  | x::ys =>
    if p x then
      pure 0
    else
      let r ← f ys p
      pure (r + 1)

def List.findIndex!_fmap.partial_correctness (motive : List α → (α → Bool) → Unit → _ → Prop)
  (f : List α → (α → Bool) → EStateM Unit Unit Nat)
  (hf : List.findIndex!_fmap f = f)
  (h :
    ∀ (f : List α → (α → Bool) → EStateM Unit Unit Nat),
      (∀ (xs : List α) (p : α → Bool) (s : Unit) (r : _), (f xs p).run s = r → motive xs p s r) →
        ∀ (xs : List α) (p : α → Bool) (s : Unit) (r : _),
          (List.findIndex!_fmap f xs p).run s = r →
            motive xs p s r)
  (xs : List α) (p : α → Bool) (s : Unit) (r : _) : (f xs p).run s = r → motive xs p s r := sorry

-- set_option trace.mpl.tactics.spec true in
theorem List.findIndex!_fmap_implies_pred_triple
  (xs : List α) (p : α → Bool)
  (f : List α → (α → Bool) → EStateM Unit Unit Nat)
  (ih : ∀ (xs : List α) (p : α → Bool),
    ⦃⌜True⌝⦄
    f xs p
    ⦃post⟨fun i _ => ∃x, xs[i]? = some x ∧ p x,
          fun _ _ => ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)⟩⦄)
  :
    ⦃⌜True⌝⦄
    List.findIndex!_fmap f xs p
    ⦃post⟨fun i _ => ∃x, xs[i]? = some x ∧ p x,
          fun _ _ => ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)⟩⦄ := by
  -- induction xs <;> mintro - ∀_; unfold findIndex!_fmap ; mwp
  -- simp
  -- unfold findIndex!_fmap
  -- split
  -- contradiction
  -- next ys _ =>
  -- split
  -- mwp
  -- mspec ih ys p
  -- sorry
  simp_all only [Bool.not_eq_true]
  unfold findIndex!_fmap
  mintro - ∀s
  split 
  simp
  sorry
  next y ys =>
  split
  . simpa
  next hn =>
  simp at hn
  mspec ih ys p
  mintro ∀_
  mpure h
  mpure_intro
  intros i x
  cases i with
  | zero =>
    simp
    rintro rfl
    assumption
  | succ n =>
    simp
    have := h n x
    assumption
  massumption

theorem List.findIndex!_fmap_implies_pred
  (f : List α → (α → Bool) → EStateM Unit Unit Nat)
  (hf : List.findIndex!_fmap f = f)
  (xs : List α) (p : α → Bool) :
  (f xs p).run () = r →
  if let (.ok i _) := r then
    ∃x, xs[i]? = some x ∧ p x
  else
    ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
  := by
    refine List.findIndex!_fmap.partial_correctness (fun xs p s r => 
      if let (.ok i _) := r then
        ∃x, xs[i]? = some x ∧ p x
      else
        ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
      ) f hf (fun f ih => ?_) xs p () r
    intros xs p s r h
    apply EStateM.by_wp' h
    refine List.findIndex!_fmap_implies_pred_triple xs p f (fun xs p s => ?_) s True.intro
    refine fun _ => ?_
    simp only [wp] ; split <;> next h => exact ih xs p _ _ h

-- #print List.findIndex
-- #print List.findIndex.partial_correctness
--
#eval (List.findIndex! ["a", "b", "c"] fun s => s == "b").run ()

-- terminating version of findIndex! (by structural recursion)
def List.findIndexT! (xs : List α) (p : α → Bool) : EStateM Unit Unit Nat := do
  match xs with
  | [] => throw ()
  | x::ys => do
    if p x then
      pure 0
    else
      let r ← List.findIndexT! ys p
      pure (r + 1)

theorem List.findIndexT!_eq_fmap : List.findIndex!_fmap (α := α) List.findIndexT! = List.findIndexT! := by
  ext xs p
  refine match xs with
  | [] => by rfl
  | x::ys =>
    if h : p x then
      by
        unfold findIndex!_fmap
        simp [h]
        unfold findIndexT!
        simp [h]
    else
      by
        unfold findIndex!_fmap
        simp [h]
        conv =>
          rhs
          unfold findIndexT!
          simp [h]

theorem List.findIndexT!_implies_pred
  (xs : List α) (p : α → Bool) :
  (findIndexT! xs p).run () = r →
  if let (.ok i _) := r then
    ∃x, xs[i]? = some x ∧ p x
  else
    ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
  := List.findIndex!_fmap_implies_pred List.findIndexT! List.findIndexT!_eq_fmap xs p

theorem List.findIndexT!_implies_pred_triple
  (xs : List α) (p : α → Bool)
  : ⦃⌜True⌝⦄
    List.findIndexT! xs p
    ⦃post⟨fun i _ => ∃x, xs[i]? = some x ∧ p x,
          fun _ _ => ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)⟩⦄ := by
  induction xs <;> mintro - ∀_; unfold findIndexT! ;
  simp
  sorry
  next tail ih _ =>
  unfold findIndexT!
  split
  . simpa
  next hn =>
  simp at hn
  mspec ih
  mintro ∀_
  mpure h
  mpure_intro
  intros i x
  cases i with
  | zero =>
    simp
    rintro rfl
    assumption
  | succ n =>
    simp
    have := h n x
    simp at this
    assumption
  massumption
  -- mspec ih _ b -- FIXME why is there an error only when both args are holes? (also, there should be an error here since `b` is not a valid binder)

theorem List.findIndexT!_implies_pred'
  (xs : List α) (p : α → Bool) :
  (findIndexT! xs p).run () = r →
  if let (.ok i _) := r then
    ∃x, xs[i]? = some x ∧ p x
  else
    ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
  := by
    intro h
    apply EStateM.by_wp' h
    exact List.findIndexT!_implies_pred_triple xs p () True.intro
    -- unfold findIndex?
    -- induction xs <;> mwp
    -- refine List.findIndex!_fmap_implies_pred_triple xs p f (fun xs p s => ?_) s True.intro
    -- refine fun _ => ?_
    -- simp only [wp] ; split <;> next h => exact ih xs p _ _ h

#eval (List.findIndexT! ["a", "b", "c"] fun s => s == "b").run ()
-- some 1

partial def List.findIndex? (xs : List α) (p : α → Bool) : Option Nat := do
  match xs with
  | [] => none
  | x::ys => do
    if p x then
      pure 0
    else
      let r ← List.findIndex? ys p
      pure (r + 1)
-- partial_fixpoint

def List.findIndex'? (xs : List α) (p : α → Bool) : Option Nat := do
  match xs with
  | [] => none
  | x::ys => do
    if p x then
      pure 0
    else
      let r ← List.findIndex'? ys p
      pure (r + 1)
partial_fixpoint

-- #print List.findIndex'?.partial_correctness
#print List.findIndex'?.fixpoint_induct
#print Lean.Order.fix_induct

axiom fixpoint_rec (F : α → α) (f : α) (hf : F f = f) (motive : α → Prop)
  (ih : ∀ (g : α), motive g → motive (F g)) : motive f
example : False := by
  refine fixpoint_rec (fun x => x) 0 rfl (fun _ => False) fun _ h => h

#eval List.findIndex? ["a", "b", "c"] fun s => s == "b"
-- some 1

def List.findIndex?_fmap (f : (xs : List α) → (p : α → Bool) → Option Nat) (xs : List α) (p : α → Bool) : Option Nat := do
  match xs with
  | [] => none
  | x::ys =>
    if p x then
      pure 0
    else
      let r ← f ys p
      pure (r + 1)

def List.findIndex?_fmap.partial_correctness (motive : List α → (α → Bool) → Option Nat → Prop)
  (f : List α → (α → Bool) → Option Nat)
  (hf : List.findIndex?_fmap f = f)
  (h :
    ∀ (f : List α → (α → Bool) → Option Nat),
      (∀ (xs : List α) (p : α → Bool) (r : Option Nat), f xs p = r → motive xs p r) →
        ∀ (xs : List α) (p : α → Bool) (s : Unit) (r : Option Nat),
          List.findIndex?_fmap f xs p = r →
            motive xs p r)
  (xs : List α) (p : α → Bool) (r : Option Nat) : f xs p = r → motive xs p r := sorry

def List.findIndexT? (xs : List α) (p : α → Bool) : Option Nat := do
  match xs with
  | [] => none
  | x::ys => do
    if p x then
      pure 0
    else
      let r ← List.findIndexT? ys p
      pure (r + 1)

theorem List.findIndexT?_eq_fmap : List.findIndex?_fmap (α := α) List.findIndexT? = List.findIndexT? := by
  ext xs p
  refine match xs with
  | [] => by rfl
  | x::ys =>
    if h : p x then
      by
        unfold findIndex?_fmap
        simp [h]
        unfold findIndexT?
        simp [h]
    else
      by
        unfold findIndex?_fmap
        simp [h]
        conv =>
          rhs
          unfold findIndexT?
          simp [h]

-- main proof
def List.findIndex?_prf
  (f : List α → (α → Bool) → Option Nat)
  (xs : List α) (p : α → Bool) (r : Option Nat)
  (ih : ∀ (xs : List α) (p : α → Bool) (r : Option Nat),
    f xs p = r →
    match r with
    | some i => ∃ x, xs[i]? = some x ∧ p x = true
    | x => ∀ (i : Nat) (x : α), xs[i]? = some x → ¬p x = true)
        
  :
    if let some i := List.findIndex?_fmap f xs p then
      ∃x, xs[i]? = some x ∧ p x
    else
      ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x) := by
  sorry

theorem List.findIndex?_fmap_implies_pred
  (f : List α → (α → Bool) → Option Nat)
  (hf : List.findIndex?_fmap f = f)
  (xs : List α) (p : α → Bool) :
  f xs p = r →
  if let some i := r then
    ∃x, xs[i]? = some x ∧ p x
  else
    ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
  := by
    refine List.findIndex?_fmap.partial_correctness (fun xs p r => 
      if let some i := r then
        ∃x, xs[i]? = some x ∧ p x
      else
        ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
      ) f hf (fun f ih => ?_) xs p r
    intros xs p s r h
    subst r
    exact List.findIndex?_prf f xs p r ih


theorem List.findIndexT?_implies_pred
  (xs : List α) (p : α → Bool) :
  (findIndexT? xs p) = r →
  if let some i := r then
    ∃x, xs[i]? = some x ∧ p x
  else
    ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
  := List.findIndex?_fmap_implies_pred List.findIndexT? List.findIndexT?_eq_fmap xs p
