import .Preloaded data.nat.fib
import tactic

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

lemma lem_phi2: phi^2 = phi + 1
:=
begin
  unfold phi,
  unfold pow monoid.pow,
  field_simp,
  ring_exp,
  rw [real.sqr_sqrt _],
  ring,
  linarith,
end

#check pow

lemma lem_psi2: psi^2 = psi + 1
:=
begin
  unfold psi,
  unfold pow monoid.pow,
  field_simp,
  ring_exp,
  rw [real.sqr_sqrt _],
  ring,
  linarith,
end

theorem binet (n : ℕ) : (nat.fib n : ℝ) = (phi^n - psi^n) / real.sqrt 5 :=
begin
  induction n using ind2 with n ihn1 ihn2,
  {
    simp,
  }, {
    simp,
    unfold phi psi,
    ring,
    symmetry,
    apply @inv_mul_cancel _ _ (real.sqrt 5) _,
    intro h,
    let h2 := (real.sqrt_eq_zero _).1 h,
    linarith,
    linarith,
  }, {
    rw nat.fib_succ_succ,
    simp,
    rw [ihn1, ihn2], clear ihn1 ihn2,
    conv {
      to_rhs,
      congr,
      rw [pow_add phi n 2, lem_phi2],
      rw [pow_add psi n 2, lem_psi2],
    },
    ring_exp,
  }
end
