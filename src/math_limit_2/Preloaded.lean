import data.real.basic
open classical
attribute [instance] prop_decidable

/-
  Rigorous definition of a limit
  For a sequence x_n, we say that \lim_{n \to \infty} x_n = l if
    ∀ ε > 0, ∃ N, n ≥ N → |x_n - l| < ε
-/

def lim_to_inf (x : ℕ → ℝ) (l : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (x n - l) < ε

-- Suppose |x_n - l| \leq y_n and \lim_{n\to\infty} y_n = 0.
-- Then \lim_{n\to\infty} x_n = l.
def SUBMISSION := ∀ (x y : ℕ → ℝ) l,
  (∀ n, abs (x n - l) ≤ y n) →
  lim_to_inf y 0 →
  lim_to_inf x l
notation `SUBMISSION` := SUBMISSION
