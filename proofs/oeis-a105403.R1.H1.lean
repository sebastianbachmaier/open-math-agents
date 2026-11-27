import OMAReductions.R_oeis_a105403_R1

-- Step oeis-a105403.R1.H1: hypothesis H1 of reduction oeis-a105403.R1
-- Credit: @sebastianbachmaier
-- H1 := ({2, 30, 53, 217} : Set ℕ) ⊆ {n : ℕ | 1 ≤ n ∧ gpf (prime n - 1) = gpf (prime (n + 1) - 1)}

open OMA.S_oeis_a105403

namespace OMAA105403

def P (k : ℕ) : Prop := 2 ≤ k ∧ ∀ m < 38, 2 ≤ m → m * m ≤ k → k % m ≠ 0

instance : DecidablePred P := fun k => by unfold P; infer_instance

theorem P_iff (k : ℕ) (hk : k < 1444) : Nat.Prime k ↔ P k := by
  constructor
  · intro hp
    refine ⟨hp.two_le, fun m _ hm2 hmm hmod => ?_⟩
    rcases (Nat.dvd_prime hp).1 (Nat.dvd_of_mod_eq_zero hmod) with h | h
    · omega
    · subst h; have := hp.two_le; nlinarith
  · rintro ⟨h2, h⟩
    by_contra hr
    have hq := Nat.minFac_prime (show k ≠ 1 by omega)
    have hsq := Nat.minFac_sq_le_self (show 0 < k by omega) hr
    have hq2 := hq.two_le
    have hmm : k.minFac * k.minFac ≤ k := by rw [← pow_two]; exact hsq
    have hlt' : k.minFac < 38 := by nlinarith
    exact h _ hlt' hq2 hmm (Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd k))

theorem count_eq (n : ℕ) (hn : n ≤ 1444) : Nat.count Nat.Prime n = Nat.count P n := by
  simp only [Nat.count_eq_card_filter_range]
  congr 1
  apply Finset.filter_congr
  intro x hx
  rw [Finset.mem_range] at hx
  exact P_iff x (by omega)

theorem nth_of (k p : ℕ) (hp : p.Prime) (hle : p ≤ 1444) (hc : Nat.count P p = k) :
    Nat.nth Nat.Prime k = p := by
  rw [← hc, ← count_eq p hle]; exact Nat.nth_count hp

theorem gpf_eq (m : ℕ) (l : List ℕ) (h : m.primeFactorsList = l) : gpf m = l.toFinset.sup id := by
  rw [gpf, ← Nat.toFinset_factors, h]

end OMAA105403

theorem OMA.solution : OMA.R_oeis_a105403_R1.H1 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  refine ⟨by omega, ?_⟩
  unfold prime
  rcases hn with rfl | rfl | rfl | rfl
  · show gpf (Nat.nth Nat.Prime 1 - 1) = gpf (Nat.nth Nat.Prime 2 - 1)
    rw [OMAA105403.nth_of 1 3 (by norm_num) (by norm_num) (by decide +kernel),
      OMAA105403.nth_of 2 5 (by norm_num) (by norm_num) (by decide +kernel)]
    rw [OMAA105403.gpf_eq _ _ (by simp [Nat.primeFactorsList_ofNat] : Nat.primeFactorsList (3 - 1) = [2]),
      OMAA105403.gpf_eq _ _ (by simp [Nat.primeFactorsList_ofNat] : Nat.primeFactorsList (5 - 1) = [2, 2])]
    decide
  · show gpf (Nat.nth Nat.Prime 29 - 1) = gpf (Nat.nth Nat.Prime 30 - 1)
    rw [OMAA105403.nth_of 29 113 (by norm_num) (by norm_num) (by decide +kernel),
      OMAA105403.nth_of 30 127 (by norm_num) (by norm_num) (by decide +kernel)]
    rw [OMAA105403.gpf_eq _ _ (by simp [Nat.primeFactorsList_ofNat] : Nat.primeFactorsList (113 - 1) = [2, 2, 2, 2, 7]),
      OMAA105403.gpf_eq _ _ (by simp [Nat.primeFactorsList_ofNat] : Nat.primeFactorsList (127 - 1) = [2, 3, 3, 7])]
    decide
  · show gpf (Nat.nth Nat.Prime 52 - 1) = gpf (Nat.nth Nat.Prime 53 - 1)
    rw [OMAA105403.nth_of 52 241 (by norm_num) (by norm_num) (by decide +kernel),
      OMAA105403.nth_of 53 251 (by norm_num) (by norm_num) (by decide +kernel)]
    rw [OMAA105403.gpf_eq _ _ (by simp [Nat.primeFactorsList_ofNat] : Nat.primeFactorsList (241 - 1) = [2, 2, 2, 2, 3, 5]),
      OMAA105403.gpf_eq _ _ (by simp [Nat.primeFactorsList_ofNat] : Nat.primeFactorsList (251 - 1) = [2, 5, 5, 5])]
    decide
  · show gpf (Nat.nth Nat.Prime 216 - 1) = gpf (Nat.nth Nat.Prime 217 - 1)
    rw [OMAA105403.nth_of 216 1327 (by norm_num) (by norm_num) (by decide +kernel),
      OMAA105403.nth_of 217 1361 (by norm_num) (by norm_num) (by decide +kernel)]
    rw [OMAA105403.gpf_eq _ _ (by simp [Nat.primeFactorsList_ofNat] : Nat.primeFactorsList (1327 - 1) = [2, 3, 13, 17]),
      OMAA105403.gpf_eq _ _ (by simp [Nat.primeFactorsList_ofNat] : Nat.primeFactorsList (1361 - 1) = [2, 2, 2, 2, 5, 17])]
    decide
