import MPL

open MPL

theorem EStateM.by_wp' {α} {x : EStateM.Result ε σ α} {prog : EStateM ε σ α} (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop) :
  ((wp prog).apply (post⟨fun a s' => P (EStateM.Result.ok a s'), fun e s' => P (EStateM.Result.error e s')⟩) s) → P x := by
  sorry
    -- intro hspec
    -- simp [wp, PredTrans.pure] at hspec
    -- split at hspec
    -- case h_1 a s' heq => rw[← heq] at hspec; exact h ▸ hspec
    -- case h_2 => contradiction

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

def List.__findIndex! (f : (xs : List α) → (p : α → Bool) → EStateM Unit Unit Nat) (xs : List α) (p : α → Bool) : EStateM Unit Unit Nat := do
  match xs with
  | [] => throw ()
  | x::ys =>
    if p x then
      pure 0
    else
      let r ← f ys p
      pure (r + 1)

def List.__findIndex!.partial_correctness (motive : List α → (α → Bool) → Unit → _ → Prop)
  (hf : ∃ f, List.__findIndex! f = f)
  (h :
    ∀ (f : List α → (α → Bool) → EStateM Unit Unit Nat),
      (∀ (xs : List α) (p : α → Bool) (s : Unit) (r : _), (f xs p).run s = r → motive xs p s r) →
        ∀ (xs : List α) (p : α → Bool) (s : Unit) (r : _),
          (List.__findIndex! f xs p).run s = r →
            motive xs p s r)
  (xs : List α) (p : α → Bool) (s : Unit) (r : _) : (hf.choose xs p).run s = r → motive xs p s r := sorry

-- set_option trace.mpl.tactics.spec true in
theorem List.__findIndex!_implies_pred_triple
  (xs : List α) (p : α → Bool)
  (f : List α → (α → Bool) → EStateM Unit Unit Nat)
  (ih : ∀ (xs : List α) (p : α → Bool),
    ⦃⌜True⌝⦄
    f xs p
    ⦃post⟨fun i _ => ∃x, xs[i]? = some x ∧ p x,
          fun e s => ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)⟩⦄)
  :
    ⦃⌜True⌝⦄
    List.__findIndex! f xs p
    ⦃post⟨fun i _ => ∃x, xs[i]? = some x ∧ p x,
          fun e s => ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)⟩⦄ := by
  simp_all only [Bool.not_eq_true]
  unfold __findIndex!
  mintro - ∀s
  split
  . mwp
    simp
  next y ys =>
  mwp
  split
  . simpa
  next hn =>
  simp only [Bool.not_eq_true] at hn
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

theorem List.__findIndex!_implies_pred
  (hf : ∃ f, List.__findIndex! f = f)
  (xs : List α) (p : α → Bool) :
  (hf.choose xs p).run () = r →
  if let (.ok i _) := r then
    ∃x, xs[i]? = some x ∧ p x
  else
    ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
  := by
    refine List.__findIndex!.partial_correctness (fun xs p s r => 
      if let (.ok i _) := r then
        ∃x, xs[i]? = some x ∧ p x
      else
        ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
      ) hf (fun f ih => ?_) xs p () r
    intros xs p s r h
    apply EStateM.by_wp' h
    refine List.__findIndex!_implies_pred_triple xs p f (fun xs p s => ?_) s True.intro
    refine fun _ => ?_
    simp only [wp] ; split <;> next h => exact ih xs p _ _ h

-- #print List.findIndex
-- #print List.findIndex.partial_correctness
--
#eval (List.findIndex! ["a", "b", "c"] fun s => s == "b").run ()
