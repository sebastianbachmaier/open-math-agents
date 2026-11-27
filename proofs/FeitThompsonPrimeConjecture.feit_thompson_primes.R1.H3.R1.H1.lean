import OMAReductions.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1

-- Step FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H3.R1.H1: hypothesis H1 of reduction FeitThompsonPrimeConjecture.feit_thompson_primes.R1.H3.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → ¬ (p % 4 = 3 ∧ q % 4 = 1) →     (∃ r : ℕ, r.Prime ∧ r ∣ (q ^ p - 1) / (q - 1) ∧ ¬ q ∣ r - 1) →     ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1)  /-- The rest: every prime factor r of N has q | r - 1. -/

namespace OMAStepFT

open Finset

lemma geom_cast (p q : ℕ) (n : ℕ) (hq : q % p = 1) :
    ((∑ k ∈ range n, q ^ k : ℕ) : ZMod p) = n := by
  have h1 : (q : ZMod p) = 1 := by
    rw [← ZMod.natCast_mod, hq, Nat.cast_one]
  push_cast
  simp [h1]

lemma geom_mod_base (p n : ℕ) :
    ((∑ k ∈ range (n + 1), p ^ k : ℕ) : ZMod p) = 1 := by
  rw [Finset.sum_range_succ']
  push_cast
  simp [pow_succ]

theorem H31 : ∀ (p q : ℕ), p.Prime → q.Prime → p < q → q % p ≠ 1 → ¬ (p % 4 = 3 ∧ q % 4 = 1) →
    (∃ r : ℕ, r.Prime ∧ r ∣ (q ^ p - 1) / (q - 1) ∧ ¬ q ∣ r - 1) →
    ¬ (q ^ p - 1) / (q - 1) ∣ (p ^ q - 1) / (p - 1) := by
  rintro p q hp hq hpq - - ⟨r, hr, hrN, hqr⟩ hdvd
  rw [← Nat.geomSum_eq hq.two_le, ← Nat.geomSum_eq hp.two_le] at hdvd
  rw [← Nat.geomSum_eq hq.two_le] at hrN
  have : Fact r.Prime := ⟨hr⟩
  have hrM := hrN.trans hdvd
  have hM0 : ((∑ k ∈ range q, p ^ k : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hrM
  have hpow : (p : ZMod r) ^ q = 1 := by
    have hg := geom_sum_mul (p : ZMod r) q
    push_cast at hM0
    rw [hM0, zero_mul] at hg
    exact (sub_eq_zero.mp hg.symm)
  have hord : orderOf (p : ZMod r) ∣ q := orderOf_dvd_of_pow_eq_one hpow
  rcases (Nat.dvd_prime hq).mp hord with h1 | hq'
  · rw [orderOf_eq_one_iff] at h1
    have hq0 : ((q : ℕ) : ZMod r) = 0 := by
      have := hM0
      push_cast at this
      simpa [h1] using this
    rw [ZMod.natCast_eq_zero_iff] at hq0
    have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hq0
    subst hrq
    obtain ⟨s, hs⟩ : ∃ s, p = s + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
    rw [hs, ← ZMod.natCast_eq_zero_iff, geom_mod_base] at hrN
    exact one_ne_zero hrN
  · have hp0 : (p : ZMod r) ≠ 0 := by
      intro h
      rw [h, zero_pow hq.ne_zero] at hpow
      exact zero_ne_one hpow
    have := ZMod.orderOf_dvd_card_sub_one hp0
    rw [hq'] at this
    exact hqr this

end OMAStepFT

theorem OMA.solution : OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1.H1 := by
  unfold OMA.R_FeitThompsonPrimeConjecture_feit_thompson_primes_R1_H3_R1.H1
  exact OMAStepFT.H31
