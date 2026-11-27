import OMAReductions.R_Erdos779_erdos_779_R1

-- Step Erdos779.erdos_779.R1.H1: hypothesis H1 of reduction Erdos779.erdos_779.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ n : ℕ, 3 ≤ n →     let P := ∏ i ∈ range (n + 1), nth Nat.Prime i     ∀ q : ℕ, q.Prime → P + 1 < q → q - P < (nth Nat.Prime (n + 1)) ^ 2 →       ∃ p : ℕ, p.Prime ∧ (P + p).Prime ∧ nth Nat.Prime n < p ∧ p < P  /-- Verify the prime pair at the first ten indices of the formal statement. -/

open Finset Nat

namespace OMAErdos779H1

theorem nth_succ_le (n r : ℕ) (hr : r.Prime) (h : nth Nat.Prime n < r) :
    nth Nat.Prime (n + 1) ≤ r := by
  have e := nth_count hr
  rw [← e] at h ⊢
  have h2 := (nth_lt_nth infinite_setOfPred_prime).mp h
  exact (nth_le_nth infinite_setOfPred_prime).mpr h2

theorem exists_idx (n r : ℕ) (hr : r.Prime) (h : r ≤ nth Nat.Prime n) :
    ∃ i, i ≤ n ∧ nth Nat.Prime i = r := by
  have e := nth_count hr
  refine ⟨count Nat.Prime r, ?_, e⟩
  rw [← e] at h
  exact (nth_le_nth infinite_setOfPred_prime).mp h

theorem bertrand (n : ℕ) : nth Nat.Prime (n + 1) ≤ 2 * nth Nat.Prime n := by
  obtain ⟨p, hp, h1, h2⟩ :=
    exists_prime_lt_and_le_two_mul (nth Nat.Prime n) (prime_nth_prime n).ne_zero
  exact le_trans (nth_succ_le n p hp h1) h2

theorem four_le (n : ℕ) (hn : 2 ≤ n) : 4 ≤ nth Nat.Prime n := by
  have : nth Nat.Prime 2 ≤ nth Nat.Prime n := (nth_le_nth infinite_setOfPred_prime).mpr hn
  rw [nth_prime_two_eq_five] at this
  omega

theorem sq_le_prod (n : ℕ) (hn : 3 ≤ n) :
    nth Nat.Prime (n + 1) ^ 2 ≤ ∏ i ∈ range (n + 1), nth Nat.Prime i := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [prod_range_succ, prod_range_zero, nth_prime_zero_eq_two, nth_prime_one_eq_three,
      nth_prime_two_eq_five, nth_prime_three_eq_seven]
    norm_num
  | succ m hm ih =>
    rw [prod_range_succ]
    have hb := bertrand (m + 1)
    have h4 := four_le (m + 1) (by omega)
    set a := nth Nat.Prime (m + 1)
    set b := nth Nat.Prime (m + 1 + 1)
    have : b ^ 2 ≤ a ^ 2 * a := by
      have : b ^ 2 ≤ (2 * a) ^ 2 := Nat.pow_le_pow_left hb 2
      nlinarith
    calc b ^ 2 ≤ a ^ 2 * a := this
      _ ≤ _ := Nat.mul_le_mul_right a ih

end OMAErdos779H1

open OMAErdos779H1 in
theorem OMA.solution : OMA.R_Erdos779_erdos_779_R1.H1 := by
  intro n hn P q hq hPq hlt
  have hdvd : ∀ i, i ≤ n → nth Nat.Prime i ∣ P := fun i hi =>
    dvd_prod_of_mem _ (mem_range.mpr (by omega))
  set p := q - P with hp
  have hp2 : 2 ≤ p := by omega
  -- every prime factor of p is at least the next prime
  have hmin : nth Nat.Prime (n + 1) ≤ p.minFac := by
    have hm : p.minFac.Prime := minFac_prime (by omega)
    apply nth_succ_le n _ hm
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi, he⟩ := exists_idx n _ hm hcon
    have h1 : p.minFac ∣ P := he ▸ hdvd i hi
    have h2 : p.minFac ∣ p := minFac_dvd p
    have h3 : p.minFac ∣ q := by
      have : q = P + p := by omega
      rw [this]; exact Nat.dvd_add h1 h2
    have := (Nat.prime_dvd_prime_iff_eq hm hq).mp h3
    have hle : p.minFac ≤ P := Nat.le_of_dvd (Finset.prod_pos (fun i _ => (prime_nth_prime i).pos)) h1
    omega
  have hpp : p.Prime := by
    by_contra hnp
    have := minFac_sq_le_self (by omega) hnp
    have : nth Nat.Prime (n + 1) ^ 2 ≤ p.minFac ^ 2 := Nat.pow_le_pow_left hmin 2
    omega
  refine ⟨p, hpp, ?_, ?_, ?_⟩
  · have : P + p = q := by omega
    rw [this]; exact hq
  · have h1 : nth Nat.Prime n < nth Nat.Prime (n + 1) :=
      (nth_lt_nth infinite_setOfPred_prime).mpr (by omega)
    have h2 : p.minFac ≤ p := minFac_le (by omega)
    omega
  · have := sq_le_prod n hn
    omega
