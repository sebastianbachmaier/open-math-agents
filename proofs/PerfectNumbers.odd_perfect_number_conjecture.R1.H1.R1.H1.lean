import OMAReductions.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1

-- Step PerfectNumbers.odd_perfect_number_conjecture.R1.H1.R1.H1: hypothesis H1 of reduction PerfectNumbers.odd_perfect_number_conjecture.R1.H1.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ n : ℕ, Nat.Perfect n → Odd n → n.primeFactors.card ≤ 2 → Nat.minFac n ≠ 3  /-- The open part: more than `2` distinct prime factors. -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

namespace OMAPerfA

theorem key (n : ℕ) (hn : n ≠ 0) :
    σ 1 n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p := by
  have h1 : σ 1 n = ∏ p ∈ n.primeFactors, σ 1 (p ^ n.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization (σ 1) hn, Finsupp.prod,
      Nat.support_factorization]
  have h2 : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
  rw [h1, ← Finset.prod_mul_distrib]
  calc _ ≤ ∏ p ∈ n.primeFactors, p ^ n.factorization p * p := ?_
    _ = n * ∏ p ∈ n.primeFactors, p := by rw [Finset.prod_mul_distrib, ← h2]
  apply Finset.prod_le_prod'
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [sigma_one_apply_prime_pow hpp, geom_sum_mul_of_one_le hpp.one_lt.le, pow_succ]
  exact Nat.sub_le _ _

theorem odd_of_mem {n p : ℕ} (hodd : Odd n) (hp : p ∈ n.primeFactors) : ∃ a, p = 2 * a + 1 ∧ 1 ≤ a := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpo : Odd p := Odd.of_dvd_nat hodd (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨a, ha⟩ := hpo
  refine ⟨a, ha, ?_⟩
  have := hpp.two_le
  omega

end OMAPerfA

theorem OMA.solution : OMA.R_PerfectNumbers_odd_perfect_number_conjecture_R1_H1_R1.H1 := by
  intro n hperf hodd hcard _
  have hn0 : 0 < n := hperf.2
  have hs : σ 1 n = 2 * n := by
    rw [sigma_one_apply]; exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn0).1 hperf
  have hk := OMAPerfA.key n hn0.ne'
  rw [hs] at hk
  have hk' : 2 * ∏ p ∈ n.primeFactors, (p - 1) ≤ ∏ p ∈ n.primeFactors, p := by
    apply Nat.le_of_mul_le_mul_left _ hn0
    calc n * (2 * ∏ p ∈ n.primeFactors, (p - 1)) = 2 * n * ∏ p ∈ n.primeFactors, (p - 1) := by ring
      _ ≤ _ := hk
  interval_cases h : n.primeFactors.card
  · rw [Finset.card_eq_zero, Nat.primeFactors_eq_empty] at h
    rcases h with h | h
    · omega
    · subst h; simp at hs
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h
    have hmem : p ∈ n.primeFactors := by rw [hp]; simp
    obtain ⟨a, rfl, ha⟩ := OMAPerfA.odd_of_mem hodd hmem
    rw [hp] at hk'
    simp at hk'
    omega
  · obtain ⟨p, q, hpq, hpq'⟩ := Finset.card_eq_two.1 h
    have hmp : p ∈ n.primeFactors := by rw [hpq']; simp
    have hmq : q ∈ n.primeFactors := by rw [hpq']; simp
    obtain ⟨a, rfl, ha⟩ := OMAPerfA.odd_of_mem hodd hmp
    obtain ⟨b, rfl, hb⟩ := OMAPerfA.odd_of_mem hodd hmq
    rw [hpq', Finset.prod_pair hpq, Finset.prod_pair hpq] at hk'
    simp only [Nat.add_sub_cancel] at hk'
    have hab : a ≠ b := by omega
    rcases Nat.lt_or_gt_of_ne hab with h' | h'
    · nlinarith
    · nlinarith
