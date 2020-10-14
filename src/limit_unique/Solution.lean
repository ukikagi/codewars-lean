import .Preloaded

theorem limit_unique {X : Type*} [metric_space X] {s : ℕ → X}
  (x₀ x₁ : X) (h₀ : s ⟶ x₀) (h₁ : s ⟶ x₁) :
x₀ = x₁ :=  
begin
  unfold converges_to at *,
  apply eq_of_forall_dist_le,
  intros ε hεp,
  specialize h₀ (ε/3) (by linarith),
    cases h₀ with N₀ hN₀,
  specialize h₁ (ε/3) (by linarith),
    cases h₁ with N₁ hN₁,
  set N := max N₀ N₁ with hN,
    specialize hN₀ N (le_max_left _ _),
    specialize hN₁ N (le_max_right _ _),
  transitivity,
    apply dist_triangle_right _ _ (s N),
  linarith,
end
