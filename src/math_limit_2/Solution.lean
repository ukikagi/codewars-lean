import .Preloaded

theorem exercise_1p3 (x y : ℕ → ℝ) (l : ℝ)
  (h₁ : ∀ n, abs (x n - l) ≤ y n) (h₂ : lim_to_inf y 0) :
  lim_to_inf x l :=
begin
  unfold lim_to_inf at *,
  intros ε hep,
  specialize h₂ ε hep, simp at h₂,
  cases h₂ with N H,
  use N,
  intros n hn,
  specialize H n hn,
  apply lt_of_le_of_lt,
    exact h₁ n,
  apply lt_of_le_of_lt,
    exact le_abs_self (y n),
  exact H,
end
