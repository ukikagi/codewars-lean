import data.real.basic data.nat.fib
import tactic

noncomputable theory

def phi : ℝ := ((1 + real.sqrt 5) / 2)

def psi : ℝ := ((1 - real.sqrt 5) / 2)

def SUBMISSION := ∀ n : ℕ, (nat.fib n : ℝ) = (phi^n - psi^n) / real.sqrt 5
notation `SUBMISSION` := SUBMISSION

lemma lt_wrap {n m: nat} {h: n < m}: n.lt m
:= by assumption

lemma ind2 {C: ℕ → Prop} {n: ℕ}:
  C 0 → C 1 → (∀ k: ℕ, C k → C (k + 1) → C (k + 2)) → C n
:=
begin
  intros h0 h1 hstep,
  apply nat.lt_wf.induction,
  intros n ih,
  rcases n with _ | _ | n,
    assumption',
  apply hstep,
  apply ih n (by apply lt_wrap; omega),
  apply ih (n + 1) (by apply lt_wrap; omega),
end

theorem binet (n : ℕ) : (nat.fib n : ℝ) = (phi^n - psi^n) / real.sqrt 5 :=
begin
  induction n using ind2 with n ihn1 ihn2,
    simp,
    sorry,
  rw nat.fib_succ_succ,
    simp,
    rw [ihn1, ihn2],
    

end
