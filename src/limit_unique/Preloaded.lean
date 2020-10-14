import topology.metric_space.basic

def converges_to {X : Type*} [metric_space X] (s : ℕ → X) (x : X) :=
∀ (ε : ℝ) (hε : 0 < ε), ∃ N : ℕ, ∀ (n : ℕ) (hn : N ≤ n), dist x (s n) < ε

notation s ` ⟶ ` x := converges_to s x

def SUBMISSION := ∀ {X : Type*} [h : metric_space X] {s : ℕ → X} (x₀ x₁ : X),
  by letI := h; exact
  ∀ (h₀ : s ⟶ x₀) (h₁ : s ⟶ x₁), x₀ = x₁