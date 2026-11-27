import FormalConjectures.ErdosProblems.«364»

-- Reduction Erdos364.erdos_364.R1 of Erdős problem 364 (no three consecutive powerful numbers)
-- Credit: @marcusbuffett

/-!
# Three consecutive powerful numbers: the congruence conditions, and the open rest

A powerful number is one in which every prime factor occurs at least squared. A number that is
`2 (mod 4)` or `3, 6 (mod 9)` is not powerful. Among three consecutive numbers this pins down the
first one modulo `36`, which is the classical remark that a triple `n, n + 1, n + 2` of powerful
numbers needs `n ≡ 7, 27` or `35 (mod 36)`.

* `H1`: no triple starts at an `n` that is not `3 (mod 4)` (one of the three is `2 (mod 4)`).
* `H2`: no triple starts at an `n` whose residue modulo `9` is not `0`, `7` or `8` (the multiple
  of `3` among the three is not a multiple of `9`).
* `H3`: no triple starts at `n ≡ 7, 27, 35 (mod 36)`. This is the open problem and stays open.
-/

namespace OMA.R_Erdos364_erdos_364_R1

/-- The start of a triple is `3 (mod 4)`. -/
def H1 : Prop :=
  ∀ n : ℕ, n % 4 ≠ 3 → ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2))

/-- The start of a triple is `0`, `7` or `8 (mod 9)`. -/
def H2 : Prop :=
  ∀ n : ℕ, n % 9 ≠ 0 → n % 9 ≠ 7 → n % 9 ≠ 8 →
    ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2))

/-- The open part: the three remaining classes modulo `36`. -/
def H3 : Prop :=
  ∀ n : ℕ, (n % 36 = 7 ∨ n % 36 = 27 ∨ n % 36 = 35) →
    ¬ (Nat.Powerful n ∧ Nat.Powerful (n + 1) ∧ Nat.Powerful (n + 2))

theorem main : H1 → H2 → H3 → type_of% @Erdos364.erdos_364 := by
  intro h1 h2 h3
  rintro ⟨n, hn⟩
  by_cases c4 : n % 4 = 3
  · by_cases c9 : n % 9 = 0 ∨ n % 9 = 7 ∨ n % 9 = 8
    · exact h3 n (by omega) hn
    · exact h2 n (fun h => c9 (Or.inl h)) (fun h => c9 (Or.inr (Or.inl h)))
        (fun h => c9 (Or.inr (Or.inr h))) hn
  · exact h1 n c4 hn

end OMA.R_Erdos364_erdos_364_R1
