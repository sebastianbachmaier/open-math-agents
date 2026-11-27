import OMAReductions.R_Erdos398_erdos_398_R1

-- Reduction Erdos398.erdos_398.R1.H3.R1 of step Erdos398.erdos_398.R1.H3
-- Credit: @marcusbuffett

/-!
# Brocard's problem: a verified range, and the open tail

The parent step says that `n! / 4` is never a product of two consecutive integers for `n ≥ 128`,
which is Brocard's problem (`n! + 1 = m^2` only for `n = 4, 5, 7`) beyond the range its sibling
step checks directly.

* `H1` (a range, by computation): no solution for `128 ≤ n < 10000`. For each such `n` there is a
  prime `p > n` such that `n! + 1` is not a square modulo `p`, which Euler's criterion detects by
  one modular power. This is the classical method (Berndt and Galway, The Brocard-Ramanujan
  diophantine equation n! + 1 = m^2, Ramanujan J. 4 (2000), checked `n` up to `10^9` with it).
* `H2`: no solution for `n ≥ 10000`. This is the open problem and stays open.
-/

namespace OMA.R_Erdos398_erdos_398_R1_H3_R1

/-- No solution for `128 ≤ n < 10000`. -/
def H1 : Prop :=
  ∀ n : ℕ, 128 ≤ n → n < 10000 → ∀ x : ℕ, n.factorial / 4 ≠ x * (x + 1)

/-- The open tail: no solution for `n ≥ 10000`. -/
def H2 : Prop :=
  ∀ n : ℕ, 10000 ≤ n → ∀ x : ℕ, n.factorial / 4 ≠ x * (x + 1)

theorem main : H1 → H2 → OMA.R_Erdos398_erdos_398_R1.H3 := by
  intro h1 h2 n hn x
  by_cases hlt : n < 10000
  · exact h1 n hn hlt x
  · exact h2 n (by omega) x

end OMA.R_Erdos398_erdos_398_R1_H3_R1
