import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1

-- Reduction CollatzConjecture.collatz_conjecture.R1.H2.R1 of step H2 (no nontrivial Collatz cycles)

/-!
# No nontrivial cycles: finite check + minimum residue + open core

Take any cycle of positive integers and let `m` be its minimum. Then `m` is a minimum of
its own trajectory.

* `H1` (finite check, true): every `0 < n < 1000` reaches `1`. If `m < 1000` then `1` lies
  on the cycle, so the cycle is `1 → 4 → 2 → 1`.
* `H2` (elementary, true): a trajectory minimum `m > 1` has `m % 4 = 3`.
* `H3` (genuinely open): a periodic point `m ≥ 1000` with `m % 4 = 3` is not the minimum
  of its cycle, i.e. there is no nontrivial cycle whose minimum is at least `1000`.

`main` combines the three: the cycle minimum either lies below `1000` (handled by `H1`) or
contradicts `H3` via `H2`.
-/

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1


open CollatzConjecture

/-- Finite check: every positive integer below 1000 reaches 1. -/
def H1 : Prop :=
  ∀ n : ℕ, 0 < n → n < 1000 → ∃ m : ℕ, collatzStep^[m] n = 1

/-- Elementary: a value `n > 1` that is a minimum of its own trajectory satisfies `n % 4 = 3`
(even values halve; `n % 4 = 1` gives `(3n+1)/4 < n` after three steps). -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → (∀ i : ℕ, n ≤ collatzStep^[i] n) → n % 4 = 3

/-- The open core: no periodic point `n ≥ 1000` with `n % 4 = 3` is the minimum of its cycle. -/
def H3 : Prop :=
  ∀ n k : ℕ, 1000 ≤ n → n % 4 = 3 → 0 < k → collatzStep^[k] n = n →
    ∃ i : ℕ, collatzStep^[i] n < n

lemma iter_mod {n k : ℕ} (hk : collatzStep^[k] n = n) (i : ℕ) :
    collatzStep^[i] n = collatzStep^[i % k] n := by
  conv_lhs => rw [← Nat.mod_add_div i k]
  rw [Function.iterate_add_apply]
  congr 1
  induction i / k with
  | zero => simp
  | succ t ih => rw [Nat.mul_succ, Function.iterate_add_apply, hk, ih]

lemma step_pos {n : ℕ} (hn : 0 < n) : 0 < collatzStep n := by
  unfold collatzStep
  split_ifs with h
  · obtain ⟨r, hr⟩ := h
    omega
  · omega

lemma iterate_pos {n : ℕ} (hn : 0 < n) (m : ℕ) : 0 < collatzStep^[m] n := by
  induction m generalizing n with
  | zero => simpa using hn
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih (step_pos hn)

lemma orbit_one (t : ℕ) : collatzStep^[t] 1 = 1 ∨ collatzStep^[t] 1 = 2 ∨
    collatzStep^[t] 1 = 4 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;> decide

theorem main : H1 → H2 → H3 → OMA.R_CollatzConjecture_collatz_conjecture_R1.H2 := by
  intro h1 h2 h3 n k hn hk hcyc
  -- the minimum of the cycle
  have hne : (Finset.range k).Nonempty := ⟨0, Finset.mem_range.mpr hk⟩
  obtain ⟨i0, hi0, hmin⟩ := Finset.exists_min_image (Finset.range k)
    (fun i => collatzStep^[i] n) hne
  set m := collatzStep^[i0] n with hm
  have hmin' : ∀ j : ℕ, m ≤ collatzStep^[j] n := by
    intro j
    rw [iter_mod hcyc j]
    exact hmin _ (Finset.mem_range.mpr (Nat.mod_lt _ hk))
  have hmcyc : collatzStep^[k] m = m := by
    rw [hm, ← Function.iterate_add_apply, Nat.add_comm, Function.iterate_add_apply, hcyc]
  have hmall : ∀ j : ℕ, m ≤ collatzStep^[j] m := by
    intro j
    rw [hm, ← Function.iterate_add_apply]
    exact hmin' _
  have hmpos : 0 < m := iterate_pos hn i0
  -- n is in the orbit of m
  have hn_of_m : ∃ j, collatzStep^[j] m = n := by
    refine ⟨k - i0 % k, ?_⟩
    have hi0k : i0 < k := Finset.mem_range.mp hi0
    rw [hm, ← Function.iterate_add_apply, iter_mod hcyc]
    have : (k - i0 % k + i0) % k = 0 := by
      rw [Nat.mod_eq_of_lt hi0k]
      rw [Nat.sub_add_cancel hi0k.le, Nat.mod_self]
    rw [this]
    rfl
  by_cases hsmall : m < 1000
  · obtain ⟨j, hj⟩ := h1 m hmpos hsmall
    obtain ⟨t, ht⟩ := hn_of_m
    -- 1 is in the orbit of m; m is in the orbit of 1
    have hm1 : ∃ s, collatzStep^[s] 1 = m := by
      refine ⟨k - j % k, ?_⟩
      rw [← hj, ← Function.iterate_add_apply, iter_mod hmcyc]
      have hjk : j % k < k := Nat.mod_lt _ hk
      have e : k - j % k + j = k * (j / k + 1) := by
        have h := Nat.mod_add_div j k
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have : (k - j % k + j) % k = 0 := by
        rw [e, Nat.mul_mod_right]
      rw [this]
      rfl
    obtain ⟨s, hs⟩ := hm1
    have := orbit_one (t + s)
    rw [Function.iterate_add_apply, hs, ht] at this
    exact this
  · exfalso
    have hm3 : m % 4 = 3 := h2 m (by omega) hmall
    obtain ⟨i, hi⟩ := h3 m k (by omega) hm3 hk hmcyc
    exact absurd (hmall i) (not_le.mpr hi)

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1
