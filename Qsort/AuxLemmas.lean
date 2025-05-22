namespace List
theorem exists_of_length_le {n} {l : List α} (h : n ≤ l.length) :
    ∃ l₁ l₂, l = l₁ ++ l₂ ∧ l₁.length = n :=
  ⟨_, _, (take_append_drop n l).symm, length_take_of_le h⟩

theorem exists_of_length_lt {n} {l : List α} (h : n < l.length) :
    ∃ l₁ a l₂, l = l₁ ++ a :: l₂ ∧ l₁.length = n :=
  match exists_of_length_le (Nat.le_of_lt h) with
  | ⟨l₁, [], _, _⟩ => by subst l; simp at h; omega
  | ⟨l₁, a::l₂, H⟩ => ⟨l₁, a, l₂, H⟩

theorem exists_three_of_le (l : List α) (h1 : i ≤ j) (h2 : j ≤ l.length) :
    ∃ l₁ l₂ l₃, l₁.length = i ∧ i + l₂.length = j ∧ l = l₁ ++ l₂ ++ l₃ := by
  obtain ⟨l', l₃, rfl, rfl⟩ := exists_of_length_le h2
  let ⟨l₁, l₂, eq, hl₁⟩ := exists_of_length_le h1
  exact ⟨l₁, l₂, l₃, hl₁, by simp [eq, hl₁]⟩

theorem exists_three_of_lt (l : List α) (h1 : i < j) (h2 : j < l.length) :
    ∃ l₁ a l₂ b l₃, l₁.length = i ∧ i + l₂.length + 1 = j ∧ l = l₁ ++ a :: l₂ ++ b :: l₃ := by
  obtain ⟨l', b, l₃, rfl, rfl⟩ := exists_of_length_lt h2
  let ⟨l₁, a, l₂, eq, hl₁⟩ := exists_of_length_lt h1
  -- exact ⟨l₁, a, l₂, b, l₃, hl₁, by simp [eq, hl₁, Nat.add_succ]⟩
  exact ⟨l₁, a, l₂, b, l₃, hl₁, sorry⟩
