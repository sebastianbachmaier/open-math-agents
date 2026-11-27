import OMAReductions.R_Erdos398_erdos_398_R1_H3_R1

-- Step Erdos398.erdos_398.R1.H3.R1.H1: hypothesis H1 of reduction Erdos398.erdos_398.R1.H3.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ n : ℕ, 128 ≤ n → n < 10000 → ∀ x : ℕ, n.factorial / 4 ≠ x * (x + 1)  /-- The open tail: no solution for `n ≥ 10000`. -/

namespace OMAE398

def Q : List ℕ := [11321, 10709, 10141, 11329, 10289, 11119, 10957, 11833, 10061, 10037]

theorem Q_prime : ∀ q ∈ Q, q.Prime := by
  simp only [Q, List.mem_cons, List.not_mem_nil, or_false]
  rintro q (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> norm_num

def good (st : List (ℕ × ℕ)) : Bool :=
  st.any (fun p => ((p.2 + 1) % p.1) ^ ((p.1 - 1) / 2) % p.1 == p.1 - 1)

def step (n : ℕ) (st : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  st.map (fun p => (p.1, p.2 * (n + 1) % p.1))

def run : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | 0, _, _ => true
  | k + 1, n, st => (decide (n < 128) || good st) && run k (n + 1) (step n st)

def stF (n : ℕ) : List (ℕ × ℕ) := Q.map (fun q => (q, n.factorial % q))

theorem step_stF (n : ℕ) : step n (stF n) = stF (n + 1) := by
  simp only [step, stF, List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp, Nat.factorial_succ]
  congr 1
  rw [Nat.mod_mul_mod, Nat.mul_comm]

theorem run_spec : ∀ k n, run k n (stF n) = true → ∀ m, n ≤ m → m < n + k → 128 ≤ m →
    good (stF m) = true := by
  intro k
  induction k with
  | zero => intro n _ m h1 h2; omega
  | succ k ih =>
    intro n h m h1 h2 h3
    simp only [run, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rcases h.1 with h' | h'
      · omega
      · exact h'
    · rw [step_stF] at h
      exact ih (n + 1) h.2 m (by omega) (by omega) h3

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem run_ok : run 10000 0 (stF 0) = true := by decide +kernel

theorem not_sq (q a e y : ℕ) (hq : q.Prime) (hq2 : 2 < q) (he : e = (q - 1) / 2)
    (ha : a % q = y ^ 2 % q) (h : a ^ e % q = q - 1) : False := by
  have := Fact.mk hq
  have h1 : ((a ^ e % q : ℕ) : ZMod q) = ((q - 1 : ℕ) : ZMod q) := by rw [h]
  have hc : ((q - 1 : ℕ) : ZMod q) = -1 := by
    rw [Nat.cast_sub hq.one_le, ZMod.natCast_self]; simp
  rw [hc, ZMod.natCast_mod, Nat.cast_pow] at h1
  have ha' : (a : ZMod q) = (y : ZMod q) ^ 2 := by
    rw [← ZMod.natCast_mod, ha, ZMod.natCast_mod, Nat.cast_pow]
  rw [ha', ← pow_mul, he] at h1
  have hodd : 2 * ((q - 1) / 2) = q - 1 := by
    have := hq.eq_one_or_self_of_dvd 2
    rcases hq.eq_two_or_odd with h2 | h2
    · omega
    · omega
  rw [hodd] at h1
  by_cases hy : (y : ZMod q) = 0
  · rw [hy, zero_pow (by omega)] at h1
    exact one_ne_zero (neg_eq_zero.1 h1.symm)
  · rw [ZMod.pow_card_sub_one_eq_one hy] at h1
    have h2 : ((2 : ℕ) : ZMod q) = 0 := by
      have e : ((2 : ℕ) : ZMod q) = 1 - (-1) := by push_cast; ring
      rw [e, ← h1, sub_self]
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd (by norm_num) h2
    omega

end OMAE398

theorem OMA.solution : OMA.R_Erdos398_erdos_398_R1_H3_R1.H1 := by
  intro n h1 h2 x hx
  have hg := OMAE398.run_spec 10000 0 OMAE398.run_ok n (by omega) (by omega) h1
  simp only [OMAE398.good, OMAE398.stF, List.any_map, List.any_eq_true, Function.comp,
    beq_iff_eq] at hg
  obtain ⟨q, hqQ, hq⟩ := hg
  have hqp := OMAE398.Q_prime q hqQ
  have hq2 : 2 < q := by
    simp only [OMAE398.Q, List.mem_cons, List.not_mem_nil, or_false] at hqQ
    rcases hqQ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  have h4 : 4 ∣ n.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  have hf : n.factorial = 4 * (x * (x + 1)) := by
    rw [← hx, Nat.mul_div_cancel' h4]
  have hsq : n.factorial + 1 = (2 * x + 1) ^ 2 := by rw [hf]; ring
  refine OMAE398.not_sq q ((n.factorial % q + 1) % q) ((q - 1) / 2) (2 * x + 1) hqp hq2 rfl ?_ hq
  rw [Nat.mod_mod, ← hsq, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
