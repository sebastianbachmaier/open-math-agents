import OMAReductions.R_Erdos317_erdos_317_variants_claim2_R1

-- Step Erdos317.erdos_317.variants.claim2.R1.H1: hypothesis H1 of reduction Erdos317.erdos_317.variants.claim2.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ n : ℕ, 1 ≤ n → ∃ u : ℕ, n < u ∧ IsPrimePow u ∧     (Icc 1 n).lcm id = (Icc 1 (u - 1)).lcm id  /-- At large prime-power predecessors, signed reciprocal sums avoid the critical magnitude. -/

namespace OMAErdos317H1

theorem dvd_lcm_of_not_ppow (m : ℕ) (hm : 1 ≤ m) (hpp : ¬ IsPrimePow (m + 1)) :
    m + 1 ∣ (Finset.Icc 1 m).lcm id := by
  have hn0 : m + 1 ≠ 0 := by omega
  set p := (m + 1).minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  set a := p ^ (m + 1).factorization p with ha
  set b := (m + 1) / a with hb
  have hab : a * b = m + 1 := Nat.ordProj_mul_ordCompl_eq_self (m + 1) p
  have hcop : Nat.Coprime a b := Nat.Coprime.pow_left _ (Nat.coprime_ordCompl hp hn0)
  have hk : 0 < (m + 1).factorization p :=
    hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd _)
  have ha2 : 2 ≤ a := by
    have := Nat.one_lt_pow (Nat.pos_iff_ne_zero.mp hk) hp.one_lt
    omega
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, mul_zero] at hab; omega
    · exact h
  have hbne : b ≠ 1 := by
    intro h1
    apply hpp
    rw [isPrimePow_nat_iff]
    exact ⟨p, _, hp, hk, by rw [← ha]; rw [h1, mul_one] at hab; exact hab⟩
  have h1 : a * 2 ≤ a * b := Nat.mul_le_mul_left a (by omega)
  have h2 : 2 * b ≤ a * b := Nat.mul_le_mul_right b ha2
  have hamem : a ∈ Finset.Icc 1 m := by
    rw [Finset.mem_Icc]; constructor <;> omega
  have hbmem : b ∈ Finset.Icc 1 m := by
    rw [Finset.mem_Icc]; constructor <;> omega
  rw [← hab]
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
    (by simpa using Finset.dvd_lcm (f := id) hamem)
    (by simpa using Finset.dvd_lcm (f := id) hbmem)

theorem lcm_step (m : ℕ) (hm : 1 ≤ m) (hpp : ¬ IsPrimePow (m + 1)) :
    (Finset.Icc 1 (m + 1)).lcm id = (Finset.Icc 1 m).lcm id := by
  have hI : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hI, Finset.lcm_insert]
  exact lcm_eq_right_iff _ _ (by simp) |>.mpr (dvd_lcm_of_not_ppow m hm hpp)

end OMAErdos317H1

open OMAErdos317H1 in
theorem OMA.solution : OMA.R_Erdos317_erdos_317_variants_claim2_R1.H1 := by
  classical
  intro n hn
  have hex : ∃ u, n < u ∧ IsPrimePow u := by
    obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (n + 1)
    exact ⟨q, by omega, hqp.isPrimePow⟩
  set u := Nat.find hex with hu
  have hspec := Nat.find_spec hex
  have hmin : ∀ v, n < v → v < u → ¬ IsPrimePow v := fun v h1 h2 h3 =>
    Nat.find_min hex h2 ⟨h1, h3⟩
  refine ⟨u, hspec.1, hspec.2, ?_⟩
  have key : ∀ t, n + t < u →
      (Finset.Icc 1 (n + t)).lcm id = (Finset.Icc 1 n).lcm id := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      rw [← add_assoc, lcm_step (n + t) (by omega) (hmin _ (by omega) ht)]
      exact ih (by omega)
  have := key (u - 1 - n) (by have := hspec.1; omega)
  rw [show n + (u - 1 - n) = u - 1 by have := hspec.1; omega] at this
  exact this.symm
