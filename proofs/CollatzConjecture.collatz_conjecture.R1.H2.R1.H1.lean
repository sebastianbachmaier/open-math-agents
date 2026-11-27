import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1

-- Step CollatzConjecture.collatz_conjecture.R1.H2.R1.H1: hypothesis H1 of reduction CollatzConjecture.collatz_conjecture.R1.H2.R1

namespace CollatzFiniteCheck

open CollatzConjecture

def reach : ℕ → ℕ → Bool
  | 0, n => n == 1
  | f + 1, n => n == 1 || reach f (collatzStep n)

lemma reach_sound : ∀ f n, reach f n = true → ∃ m, collatzStep^[m] n = 1
  | 0, n, h => ⟨0, by simpa [reach] using h⟩
  | f + 1, n, h => by
    simp only [reach, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨m, hm⟩ := reach_sound f _ h
      exact ⟨m + 1, by rw [Function.iterate_succ_apply]; exact hm⟩

def checkAll : ℕ → Bool
  | 0 => true
  | N + 1 => checkAll N && (N == 0 || reach 200 N)

lemma checkAll_sound : ∀ N, checkAll N = true → ∀ n, 0 < n → n < N → reach 200 n = true
  | 0, _, n, _, h => absurd h (Nat.not_lt_zero n)
  | N + 1, h, n, hn, hlt => by
    simp only [checkAll, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hl | rfl
    · exact checkAll_sound N h.1 n hn hl
    · rcases h.2 with h0 | h2
      · omega
      · exact h2

lemma checkAll_1000 : checkAll 1000 = true := by decide +kernel

end CollatzFiniteCheck

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H1 := fun n hn hlt =>
  CollatzFiniteCheck.reach_sound 200 n
    (CollatzFiniteCheck.checkAll_sound 1000 CollatzFiniteCheck.checkAll_1000 n hn hlt)
