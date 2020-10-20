import .Preloaded
import tactic

theorem expand : ∀ n : ℕ, (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 :=
begin
  intro n,
  ring 
end
