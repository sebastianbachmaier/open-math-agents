import OMAReductions.R_Erdos364_erdos_364_R1

-- Step Erdos364.erdos_364.R1.H1: hypothesis H1 of reduction Erdos364.erdos_364.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ n : ℕ, n % 4 ≠ 3 → ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2))  /-- The start of a triple is `0`, `7` or `8 (mod 9)`. -/

namespace OMAE364A

theorem not_pow (m : ℕ) (h : m % 4 = 2) : ¬ Nat.Powerful m :=
  Nat.not_full_of_prime_mod_prime_sq m 1 Nat.prime_two (by norm_num; exact h)

end OMAE364A

theorem OMA.solution : OMA.R_Erdos364_erdos_364_R1.H1 := by
  intro n hn ⟨h0, h1, h2⟩
  have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 := by omega
  rcases this with h | h | h
  · exact OMAE364A.not_pow (n + 2) (by omega) h2
  · exact OMAE364A.not_pow (n + 1) (by omega) h1
  · exact OMAE364A.not_pow n h h0

