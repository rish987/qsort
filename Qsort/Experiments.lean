import MPL

open MPL

partial def List.findIndex (xs : List α) (p : α → Bool) : EStateM Unit Unit Nat := do
  match xs with
  | [] => throw ()
  | x::ys => do
    if p x then
      pure 0
    else
      let r ← List.findIndex ys p
      pure (r + 1)
-- partial_fixpoint
def List.__findIndex (f : (xs : List α) → (p : α → Bool) → EStateM Unit Unit Nat) (xs : List α) (p : α → Bool) : EStateM Unit Unit Nat := do
  match xs with
  | [] => throw ()
  | x::ys =>
    if p x then
      pure 0
    else
      let r ← f ys p
      pure (r + 1)

def List.findIndex.partial_correctness (motive : List α → (α → Bool) → _ → Prop)
  (hf : ∃ f, List.__findIndex f = f)
  (h :
    ∀ (f : List α → (α → Bool) → EStateM Unit Unit Nat),
      (∀ (xs : List α) (p : α → Bool) (r : _), (f xs p).run () = r → motive xs p r) →
        ∀ (xs : List α) (p : α → Bool) (r : _),
          (List.__findIndex f xs p).run () = r →
            motive xs p r)
  (xs : List α) (p : α → Bool) (r : _) : (hf.choose xs p).run () = r → motive xs p r := sorry

theorem List.findIndex_implies_pred
    (hf : ∃ f, List.__findIndex f = f)
    (xs : List α) (p : α → Bool) :
    (hf.choose xs p).run () = r →
    if let (.ok i _) := r then
      ∃x, xs[i]? = some x ∧ p x
    else
      ∀ (i : Nat) x, xs[i]? = some x → ¬ (p x)
    := by
      refine List.findIndex.partial_correctness (fun xs p r => _) hf (fun f ih => ?_) xs p r
      intros xs p r h
      apply EStateM.by_wp h
      sorry

-- #print List.findIndex
-- #print List.findIndex.partial_correctness
--
#eval (List.findIndex ["a", "b", "c"] fun s => s == "b").run ()
