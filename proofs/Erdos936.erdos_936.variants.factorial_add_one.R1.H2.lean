import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H2: hypothesis H2 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @sebastianbachmaier
-- H2 := ∀ C e : ℕ, ∀ᶠ n : ℕ in atTop, C * (primorial n) ^ e < n.factorial  /-- The remaining abc estimate for factorials, written with integer powers. -/

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H2 := by
  intro C e
  filter_upwards [Nat.eventually_mul_pow_lt_factorial_sub C (4 ^ e) 0] with n hn
  refine lt_of_le_of_lt ?_ hn
  apply Nat.mul_le_mul_left
  rw [← pow_mul, mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (primorial_le_four_pow n) e
