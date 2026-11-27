import OMAReductions.R_OeisA4290_conjecture_R1_H1_R1

-- Reduction OeisA4290.conjecture.R1.H1.R1.H3.R1 of step OeisA4290.conjecture.R1.H1.R1.H3
-- Credit: @marcusbuffett

/-!
# The coprime remainder of Radcliffe's question on A004290: one more period, and small `k`

The parent step is the open remainder of the coprime case: `n < 10^k - 1` coprime to `10` that
divides no `10^t - 1` with `t ≤ k` and no repunit with fewer than `9k` digits.

* `H3` (the next period, by counting). Let `k ≥ 8` and let `n` divide `10^(k+1) - 1`. The `9k`
  available positions cover the residues modulo `k + 1` nine times, except the top nine residues,
  which are covered eight times. So it suffices to find a positive multiple `x < 10^(k+1) - 1` of
  `n` whose top nine digits are at most `8`, and to stack its digits. Multiplication by `10`
  modulo `10^(k+1) - 1` rotates the digits and permutes the multiples of `n`, so for each of the
  nine positions the multiples with digit `9` there correspond to the multiples in
  `[9 * 10^k, 10^(k+1) - 1)`, at most `(10^k - 1) / n` of them. Nine times that is less than the
  number of positive multiples because `n < 10^k`. (If the stacked number were the full repunit,
  then `n` would divide `111111111`, which is a witness itself.) This family contains the worst
  cases found by computation below `10^5`, such as `76923 = 999999 / 13`.
* `H1`, `H2` (small `k`, by computation): every `n < 10^k - 1` with `k ≤ 4`, and every
  `n < 10^5 - 1` coprime to `10`; the kernel checks a table of least 0/1 multiples.
* `H4`: what is left; by `H1` and `H2` it only concerns `n ≥ 10^5 - 1`. It stays open.
-/

namespace OMA.R_OeisA4290_conjecture_R1_H1_R1_H3_R1

/-- All `n < 10^k - 1` for `k ≤ 4`. -/
def H1 : Prop :=
  ∀ k n : ℕ, k ≤ 4 → 0 < n → n < 10 ^ k - 1 →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

/-- All `n < 10^5 - 1` coprime to `10`. -/
def H2 : Prop :=
  ∀ n : ℕ, 0 < n → n < 10 ^ 5 - 1 → Nat.Coprime n 10 →
    ∃ m < (10 ^ 45 - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

/-- The divisors of `10^(k+1) - 1`, for `k ≥ 8`. -/
def H3 : Prop :=
  ∀ k n : ℕ, 8 ≤ k → 0 < n → n < 10 ^ k - 1 → n ∣ 10 ^ (k + 1) - 1 →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

/-- The open remainder: `n ≥ 10^5 - 1`. -/
def H4 : Prop :=
  ∀ k n : ℕ, 0 < n → n < 10 ^ k - 1 → 10 ^ 5 - 1 ≤ n → Nat.Coprime n 10 →
    (∀ t : ℕ, 0 < t → t ≤ k → ¬ n ∣ 10 ^ t - 1) →
    (∀ t : ℕ, 0 < t → t < 9 * k → ¬ 9 * n ∣ 10 ^ t - 1) →
    (8 ≤ k → ¬ n ∣ 10 ^ (k + 1) - 1) →
    ∃ m < (10 ^ (9 * k) - 1) / 9,
      0 < m ∧ n ∣ m ∧ ∀ d ∈ Nat.digits 10 m, d = 0 ∨ d = 1

lemma repunit_mono {a b : ℕ} (h : a ≤ b) : (10 ^ a - 1) / 9 ≤ (10 ^ b - 1) / 9 :=
  Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) h) 1)

lemma small_exponent {k n j : ℕ} (hlt : n < 10 ^ k - 1) (hge : 10 ^ j - 1 ≤ n) : j < k := by
  by_contra hc
  have : 10 ^ k ≤ 10 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem main : H1 → H2 → H3 → H4 → OMA.R_OeisA4290_conjecture_R1_H1_R1.H3 := by
  intro h1 h2 h3 h4 k n hn hlt hco hs1 hs2
  by_cases hn4 : n < 10 ^ 4 - 1
  · by_cases hk4 : k ≤ 4
    · exact h1 k n hk4 hn hlt
    · obtain ⟨m, hm, r⟩ := h1 4 n le_rfl hn hn4
      exact ⟨m, lt_of_lt_of_le hm (repunit_mono (by omega)), r⟩
  by_cases hn5 : n < 10 ^ 5 - 1
  · have hk : 4 < k := small_exponent hlt (by omega)
    obtain ⟨m, hm, r⟩ := h2 n hn hn5 hco
    exact ⟨m, lt_of_lt_of_le hm (repunit_mono (by omega)), r⟩
  by_cases hnext : 8 ≤ k ∧ n ∣ 10 ^ (k + 1) - 1
  · exact h3 k n hnext.1 hn hlt hnext.2
  · exact h4 k n hn hlt (by omega) hco hs1 hs2 (fun h8 hd => hnext ⟨h8, hd⟩)

end OMA.R_OeisA4290_conjecture_R1_H1_R1_H3_R1
