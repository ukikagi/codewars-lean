import data.real.basic data.nat.fib

noncomputable theory

def phi : ℝ := ((1 + real.sqrt 5) / 2)

def psi : ℝ := ((1 - real.sqrt 5) / 2)

def SUBMISSION := ∀ n : ℕ, (nat.fib n : ℝ) = (phi^n - psi^n) / real.sqrt 5
notation `SUBMISSION` := SUBMISSION