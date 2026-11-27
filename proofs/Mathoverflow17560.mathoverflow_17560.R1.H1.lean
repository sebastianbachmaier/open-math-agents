import OMAReductions.R_Mathoverflow17560_mathoverflow_17560_R1

-- Step Mathoverflow17560.mathoverflow_17560.R1.H1: hypothesis H1 of reduction Mathoverflow17560.mathoverflow_17560.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ x : ℝ, (∃ q : ℚ, x = q) → (∃ m : ℕ, (2 : ℝ) ^ x = m) → ∃ m : ℕ, x = m  /-- The open part: an irrational exponent. -/

theorem OMA.solution : OMA.R_Mathoverflow17560_mathoverflow_17560_R1.H1 := by
  rintro x ⟨q, rfl⟩ ⟨m, hm⟩
  have hb : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast q.den_pos
  have key : ((m : ℝ)) ^ q.den = (2 : ℝ) ^ (q.num : ℝ) := by
    rw [← hm, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    congr 1
    have := Rat.num_div_den q
    have h2 : ((q : ℝ)) = (q.num : ℝ) / (q.den : ℝ) := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
    rw [h2]; field_simp
  rw [Real.rpow_intCast] at key
  have hpos : (0 : ℝ) < (m : ℝ) := by rw [← hm]; positivity
  have hm1 : 1 ≤ m := by exact_mod_cast hpos
  rcases lt_or_ge q.num 0 with hneg | hnn
  · exfalso
    have h1 : (2 : ℝ) ^ q.num < 1 := zpow_lt_one_of_neg₀ (by norm_num) hneg
    have h3 : (1 : ℝ) ≤ (m : ℝ) ^ q.den := one_le_pow₀ (by exact_mod_cast hm1)
    linarith
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hnn
    rw [hn, zpow_natCast] at key
    have keyN : m ^ q.den = 2 ^ n := by exact_mod_cast key
    have hdvd : m ∣ 2 ^ n := by
      rw [← keyN]; exact dvd_pow_self m q.den_pos.ne'
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [← pow_mul] at keyN
    have hjn : j * q.den = n := Nat.pow_right_injective (le_refl 2) keyN
    refine ⟨j, ?_⟩
    have h2 : ((q : ℝ)) = (q.num : ℝ) / (q.den : ℝ) := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
    rw [h2, hn, ← hjn]
    push_cast
    field_simp
