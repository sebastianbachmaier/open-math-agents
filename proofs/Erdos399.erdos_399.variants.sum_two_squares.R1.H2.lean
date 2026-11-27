import OMAReductions.R_Erdos399_erdos_399_variants_sum_two_squares_R1

-- Step Erdos399.erdos_399.variants.sum_two_squares.R1.H2: hypothesis H2 of reduction Erdos399.erdos_399.variants.sum_two_squares.R1
-- Credit: @sebastianbachmaier
-- H2 := ∀ n : ℕ, 100 < n →   ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n  /-- A prime q with q ≤ n < 2q has padicValNat q n! = 1. -/

open Finset
open scoped Nat

namespace E399

def R (r z : ℕ) : ℕ := ∏ m ∈ (range z).filter (fun m => (m + 1) % 4 = r), (m + 1)

lemma R_zero (r : ℕ) : R r 0 = 1 := by simp [R]

lemma R_succ (r z : ℕ) : R r (z + 1) = R r z * (if (z + 1) % 4 = r then z + 1 else 1) := by
  unfold R
  rw [range_add_one, filter_insert]
  by_cases h : (z + 1) % 4 = r
  · rw [if_pos h, if_pos h, prod_insert (by simp)]
    ring
  · rw [if_neg h, if_neg h, mul_one]

lemma R_pos (r z : ℕ) : 0 < R r z := prod_pos (fun _ _ => Nat.succ_pos _)

lemma R_cross (z : ℕ) : R 1 z ≤ R 3 (z + 2) ∧ R 3 z ≤ R 1 (z + 2) := by
  induction z with
  | zero => decide
  | succ z ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [R_succ 1 z, R_succ 3 z, show z + 1 + 2 = (z + 2) + 1 by ring, R_succ 3 (z + 2),
      R_succ 1 (z + 2)]
    constructor
    · by_cases h : (z + 1) % 4 = 1
      · rw [if_pos h, if_pos (by omega)]
        exact Nat.mul_le_mul h1 (by omega)
      · rw [if_neg h, if_neg (by omega)]
        simpa using h1
    · by_cases h : (z + 1) % 4 = 3
      · rw [if_pos h, if_pos (by omega)]
        exact Nat.mul_le_mul h2 (by omega)
      · rw [if_neg h, if_neg (by omega)]
        simpa using h2

lemma R_add_two (r z : ℕ) : R r (z + 2) ≤ (z + 2) * R r z := by
  rw [show z + 2 = (z + 1) + 1 by ring, R_succ, R_succ]
  have hp := R_pos r z
  by_cases h1 : (z + 1) % 4 = r <;> by_cases h2 : (z + 1 + 1) % 4 = r
  · omega
  · rw [if_pos h1, if_neg h2]; nlinarith
  · rw [if_neg h1, if_pos h2]; nlinarith
  · rw [if_neg h1, if_neg h2]; nlinarith

/-- valuation of a product of successors -/
lemma fac_prod (S : Finset ℕ) {p b : ℕ} (hp : p.Prime) (hS : ∀ m ∈ S, m + 1 < p ^ b) :
    (∏ m ∈ S, (m + 1)).factorization p = ∑ i ∈ Ico 1 b, #{m ∈ S | p ^ i ∣ m + 1} := by
  rw [Nat.factorization_prod (fun m _ => Nat.succ_ne_zero m), Finset.sum_apply']
  rw [sum_congr rfl (fun m hm => Nat.factorization_eq_card_pow_dvd_of_lt hp (Nat.succ_pos m)
    (hS m hm))]
  simp only [card_filter]
  exact sum_comm

def cnt (r z q : ℕ) : ℕ := #{m ∈ range z | (m + 1) % 4 = r ∧ q ∣ m + 1}

lemma R_fac (r z : ℕ) {p b : ℕ} (hp : p.Prime) (hb : Nat.log p z < b) :
    (R r z).factorization p = ∑ i ∈ Ico 1 b, cnt r z (p ^ i) := by
  unfold R
  rw [fac_prod _ hp]
  · apply sum_congr rfl
    intro i _
    unfold cnt
    rw [filter_filter]
  · intro m hm
    have hmz : m < z := mem_range.1 (mem_filter.1 hm).1
    have := Nat.lt_pow_succ_log_self hp.one_lt z
    calc m + 1 ≤ z := hmz
      _ < p ^ (Nat.log p z).succ := this
      _ ≤ p ^ b := Nat.pow_le_pow_right hp.pos hb

def h1 (t s : ℕ) : ℕ := if s = 1 then (t + 3) / 4 else if s = 3 then (t + 1) / 4 else 0
def h3 (t s : ℕ) : ℕ := if s = 1 then (t + 1) / 4 else if s = 3 then (t + 3) / 4 else 0

lemma cnt_succ (r z q : ℕ) : cnt r (z + 1) q = cnt r z q +
    (if (z + 1) % 4 = r ∧ q ∣ z + 1 then 1 else 0) := by
  unfold cnt
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

lemma step_arith (s t z : ℕ) (hs : s < 4) (key : (z + 1) % 4 = (s * ((t + 1) % 4)) % 4) :
    h1 t s + (if (z + 1) % 4 = 1 then 1 else 0) = h1 (t + 1) s ∧
    h3 t s + (if (z + 1) % 4 = 3 then 1 else 0) = h3 (t + 1) s := by
  obtain ⟨a, j, hj, rfl⟩ : ∃ a j, j < 4 ∧ t = 4 * a + j :=
    ⟨t / 4, t % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod t 4).symm⟩
  have e1 : (4 * a + j + 1) % 4 = (j + 1) % 4 := by omega
  rw [e1] at key
  interval_cases j <;> interval_cases s <;> norm_num at key <;> simp only [h1, h3] <;>
    constructor <;> split_ifs <;> first | omega | simp_all

lemma cnt_closed (z q : ℕ) (_hq : 0 < q) :
    cnt 1 z q = h1 (z / q) (q % 4) ∧ cnt 3 z q = h3 (z / q) (q % 4) := by
  induction z with
  | zero => simp [cnt, h1, h3]
  | succ z ih =>
    obtain ⟨i1, i3⟩ := ih
    rw [cnt_succ, cnt_succ, i1, i3, Nat.succ_div]
    by_cases hd : q ∣ z + 1
    · have key : (z + 1) % 4 = (q % 4 * ((z / q + 1) % 4)) % 4 := by
        have : z + 1 = q * (z / q + 1) := by
          rw [← Nat.succ_div_of_dvd hd, Nat.mul_div_cancel' hd]
        rw [this, Nat.mul_mod]
      simp only [hd, and_true, if_true]
      exact step_arith _ _ _ (Nat.mod_lt _ (by norm_num)) key
    · simp [hd]

def A (t s : ℕ) : ℕ := t + t / 4 + 2 * (t / 6) + t / 12 + h3 t s + h1 (t / 2) s
def B (t s : ℕ) : ℕ := 2 * (t / 2) + 2 * (t / 3) + h1 t s + h3 (t / 2) s

lemma levelA (t s : ℕ) : A t s ≤ B t s + 2 := by
  obtain ⟨a, j, hj, rfl⟩ : ∃ a j, j < 24 ∧ t = 24 * a + j :=
    ⟨t / 24, t % 24, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod t 24).symm⟩
  unfold A B h1 h3
  interval_cases j <;> split_ifs <;> omega

lemma levelB : ∀ t < 25, ∀ s < 4, (s = 1 ∨ s = 3) →
    (t = 1 ∧ s = 3) ∨ A t s ≤ B t s + (if 12 ≤ t then 1 else 0) := by
  decide

lemma prim_fac {p : ℕ} (hp : p.Prime) (z : ℕ) :
    (primorial z).factorization p = if p ≤ z then 1 else 0 := by
  unfold primorial
  rw [Nat.factorization_prod (fun q hq => (mem_filter.1 hq).2.ne_zero), Finset.sum_apply']
  rw [sum_congr rfl (fun q hq => by rw [(mem_filter.1 hq).2.factorization, Finsupp.single_apply])]
  rw [sum_ite_eq']
  simp [mem_filter, hp, Nat.lt_succ_iff]

def Kp (N : ℕ) : ℕ := ∏ q ∈ (range (Nat.sqrt N + 1)).filter Nat.Prime, q ^ (2 * Nat.log q N)

lemma Kp_pos (N : ℕ) : 0 < Kp N :=
  prod_pos (fun q hq => pow_pos (mem_filter.1 hq).2.pos _)

lemma Kp_fac {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (Kp N).factorization p = if p ≤ Nat.sqrt N then 2 * Nat.log p N else 0 := by
  unfold Kp
  rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (mem_filter.1 hq).2.ne_zero),
    Finset.sum_apply']
  rw [sum_congr rfl (fun q hq => by
    rw [Nat.factorization_pow, (mem_filter.1 hq).2.factorization, Finsupp.smul_apply,
      Finsupp.single_apply])]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq']
  simp [mem_filter, hp, Nat.lt_succ_iff]

lemma Kp_le (N : ℕ) (hN : N ≠ 0) : Kp N ≤ N ^ (2 * (Nat.sqrt N + 1)) := by
  unfold Kp
  calc ∏ q ∈ (range (Nat.sqrt N + 1)).filter Nat.Prime, q ^ (2 * Nat.log q N)
      ≤ ∏ q ∈ (range (Nat.sqrt N + 1)).filter Nat.Prime, N ^ 2 := by
        apply prod_le_prod (fun _ _ => Nat.zero_le _)
        intro q _
        rw [mul_comm, pow_mul]
        exact Nat.pow_le_pow_left (Nat.pow_log_le_self q hN) 2
    _ = (N ^ 2) ^ #((range (Nat.sqrt N + 1)).filter Nat.Prime) := prod_const _
    _ ≤ (N ^ 2) ^ (Nat.sqrt N + 1) := by
        apply Nat.pow_le_pow_right (by positivity)
        exact (card_filter_le _ _).trans (card_range _).le
    _ = N ^ (2 * (Nat.sqrt N + 1)) := by rw [pow_mul]

def numer (N : ℕ) : ℕ := N ! * (N / 4) ! * (N / 6) ! ^ 2 * (N / 12) ! * R 3 N * R 1 (N / 2)
def denom (N : ℕ) : ℕ := (N / 2) ! ^ 2 * (N / 3) ! ^ 2 * R 1 N * R 3 (N / 2) *
  primorial (N / 12) * primorial (N / 25) * Kp N

lemma numer_ne (N : ℕ) : numer N ≠ 0 := by
  unfold numer
  have := R_pos 3 N; have := R_pos 1 (N / 2)
  positivity

lemma denom_ne (N : ℕ) : denom N ≠ 0 := by
  unfold denom
  have := R_pos 1 N; have := R_pos 3 (N / 2); have := Kp_pos N
  have := primorial_pos (N / 12); have := primorial_pos (N / 25)
  positivity

lemma divdiv (N k q : ℕ) : N / k / q = N / q / k := by
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]

lemma numer_fac (N : ℕ) {p b : ℕ} (hp : p.Prime) (hb : Nat.log p N < b) :
    (numer N).factorization p = ∑ i ∈ Ico 1 b, A (N / p ^ i) (p ^ i % 4) := by
  have hb' : ∀ k, Nat.log p (N / k) < b := fun k =>
    lt_of_le_of_lt (Nat.log_mono_right (Nat.div_le_self N k)) hb
  have hq : ∀ i, 0 < p ^ i := fun i => pow_pos hp.pos i
  unfold numer
  have := R_pos 3 N; have := R_pos 1 (N / 2)
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Nat.factorization_factorial hp hb, Nat.factorization_factorial hp (hb' 4),
    Nat.factorization_factorial hp (hb' 6), Nat.factorization_factorial hp (hb' 12),
    R_fac 3 N hp hb, R_fac 1 (N / 2) hp (hb' 2)]
  simp only [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  rw [(cnt_closed N (p ^ i) (hq i)).2, (cnt_closed (N / 2) (p ^ i) (hq i)).1]
  unfold A
  rw [divdiv N 4, divdiv N 6, divdiv N 12, divdiv N 2]

lemma denom_fac (N : ℕ) {p b : ℕ} (hp : p.Prime) (hb : Nat.log p N < b) :
    (denom N).factorization p = ∑ i ∈ Ico 1 b, B (N / p ^ i) (p ^ i % 4) +
      (if p ≤ N / 12 then 1 else 0) + (if p ≤ N / 25 then 1 else 0) +
      (if p ≤ Nat.sqrt N then 2 * Nat.log p N else 0) := by
  have hb' : ∀ k, Nat.log p (N / k) < b := fun k =>
    lt_of_le_of_lt (Nat.log_mono_right (Nat.div_le_self N k)) hb
  have hq : ∀ i, 0 < p ^ i := fun i => pow_pos hp.pos i
  unfold denom
  have := R_pos 1 N; have := R_pos 3 (N / 2); have := Kp_pos N
  have := primorial_pos (N / 12); have := primorial_pos (N / 25)
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_pow, Nat.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Nat.factorization_factorial hp (hb' 2), Nat.factorization_factorial hp (hb' 3),
    R_fac 1 N hp hb, R_fac 3 (N / 2) hp (hb' 2), prim_fac hp, prim_fac hp, Kp_fac hp]
  have : ∑ i ∈ Ico 1 b, B (N / p ^ i) (p ^ i % 4) =
      2 * ∑ i ∈ Ico 1 b, N / 2 / p ^ i + 2 * ∑ i ∈ Ico 1 b, N / 3 / p ^ i +
      ∑ i ∈ Ico 1 b, cnt 1 N (p ^ i) + ∑ i ∈ Ico 1 b, cnt 3 (N / 2) (p ^ i) := by
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [(cnt_closed N (p ^ i) (hq i)).1, (cnt_closed (N / 2) (p ^ i) (hq i)).2]
    unfold B
    rw [divdiv N 2, divdiv N 3]
  rw [this]

lemma ind_eq (N p k : ℕ) (hp : 0 < p) (hk : 0 < k) :
    (if p ≤ N / k then 1 else 0) = (if k ≤ N / p then 1 else 0) := by
  have : p ≤ N / k ↔ k ≤ N / p := by
    rw [Nat.le_div_iff_mul_le hk, Nat.le_div_iff_mul_le hp, mul_comm]
  simp only [this]

lemma key_le (N : ℕ) (hN : 16 ≤ N)
    (hno : ∀ q, q.Prime → q % 4 = 3 → N < 2 * q → q ≤ N → False) :
    (numer N).factorization ≤ (denom N).factorization := by
  intro p
  by_cases hp : p.Prime
  swap
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  by_cases hps : p ≤ Nat.sqrt N
  · rw [numer_fac N hp (Nat.lt_add_one _), denom_fac N hp (Nat.lt_add_one _), if_pos hps]
    have h1 : ∑ i ∈ Ico 1 (Nat.log p N + 1), A (N / p ^ i) (p ^ i % 4) ≤
        ∑ i ∈ Ico 1 (Nat.log p N + 1), (B (N / p ^ i) (p ^ i % 4) + 2) :=
      sum_le_sum (fun i _ => levelA _ _)
    rw [sum_add_distrib, sum_const, Nat.card_Ico] at h1
    simp only [smul_eq_mul] at h1
    omega
  · push Not at hps
    have hN0 : N ≠ 0 := by omega
    have hlt : N < p ^ 2 := Nat.sqrt_lt'.1 hps
    have hb2 : Nat.log p N < 2 := Nat.log_lt_of_lt_pow hN0 hlt
    rw [numer_fac N hp hb2, denom_fac N hp hb2, if_neg (show ¬ p ≤ Nat.sqrt N by omega)]
    rw [Nat.Ico_succ_singleton, sum_singleton, sum_singleton, pow_one]
    rw [ind_eq N p 12 hp.pos (by norm_num), ind_eq N p 25 hp.pos (by norm_num)]
    have hs4 : 4 ≤ Nat.sqrt N := Nat.le_sqrt.2 (by omega)
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    have hs : p % 4 = 1 ∨ p % 4 = 3 := by omega
    by_cases ht : N / p < 25
    · rcases levelB (N / p) ht (p % 4) (Nat.mod_lt _ (by norm_num)) hs with h | h
      · exfalso
        apply hno p hp h.2
        · have := h.1
          have := Nat.lt_mul_div_succ N hp.pos
          rw [h.1] at this
          linarith
        · have := h.1
          exact (Nat.div_pos_iff.1 (by omega)).2
      · have : (if 25 ≤ N / p then 1 else 0) = 0 := if_neg (by omega)
        omega
    · have h1 : (if 12 ≤ N / p then 1 else 0) = 1 := if_pos (by omega)
      have h2 : (if 25 ≤ N / p then 1 else 0) = 1 := if_pos (by omega)
      have := levelA (N / p) (p % 4)
      omega

lemma key_dvd (N : ℕ) (hN : 16 ≤ N)
    (hno : ∀ q, q.Prime → q % 4 = 3 → N < 2 * q → q ≤ N → False) : numer N ≤ denom N :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (denom_ne N))
    ((Nat.factorization_le_iff_dvd (numer_ne N) (denom_ne N)).1 (key_le N hN hno))

lemma fact_add (n k : ℕ) : (n + k)! = n ! * ∏ i ∈ range k, (n + i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Nat.factorial_succ, ih, prod_range_succ]
    ring

lemma fact_bound (a c N m : ℕ) (h : a ≤ c) (hc : c ≤ N) (hk : c - a ≤ m) (hN : 1 ≤ N) :
    c ! ≤ a ! * N ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [fact_add]
  apply Nat.mul_le_mul_left
  calc ∏ i ∈ range k, (a + i + 1) ≤ ∏ i ∈ range k, N := by
        apply prod_le_prod (fun _ _ => Nat.zero_le _)
        intro i hi
        have := mem_range.1 hi
        omega
    _ = N ^ k := by rw [prod_const, card_range]
    _ ≤ N ^ m := Nat.pow_le_pow_right hN (by omega)

def Fp (u : ℕ) : ℕ := (12 * u)! * (3 * u)! * (2 * u)! ^ 2 * u !
def Fm (u : ℕ) : ℕ := (6 * u)! ^ 2 * (4 * u)! ^ 2

lemma poly (u : ℕ) :
    27 * ((∏ i ∈ range 6, (6 * u + i + 1)) ^ 2 * (∏ i ∈ range 4, (4 * u + i + 1)) ^ 2) ≤
    (∏ i ∈ range 12, (12 * u + i + 1)) * (∏ i ∈ range 3, (3 * u + i + 1)) *
      (∏ i ∈ range 2, (2 * u + i + 1)) ^ 2 * (u + 1) := by
  simp only [prod_range_succ, prod_range_zero, one_mul]
  have key : (12 * u + 0 + 1) * (12 * u + 1 + 1) * (12 * u + 2 + 1) * (12 * u + 3 + 1) *
      (12 * u + 4 + 1) * (12 * u + 5 + 1) * (12 * u + 6 + 1) * (12 * u + 7 + 1) *
      (12 * u + 8 + 1) * (12 * u + 9 + 1) * (12 * u + 10 + 1) * (12 * u + 11 + 1) *
      ((3 * u + 0 + 1) * (3 * u + 1 + 1) * (3 * u + 2 + 1)) *
      ((2 * u + 0 + 1) * (2 * u + 1 + 1)) ^ 2 * (u + 1) =
      27 * (((6 * u + 0 + 1) * (6 * u + 1 + 1) * (6 * u + 2 + 1) * (6 * u + 3 + 1) *
        (6 * u + 4 + 1) * (6 * u + 5 + 1)) ^ 2 *
        ((4 * u + 0 + 1) * (4 * u + 1 + 1) * (4 * u + 2 + 1) * (4 * u + 3 + 1)) ^ 2) +
      (1925877696823296 * u ^ 19 + 22120845212123136 * u ^ 18 + 118802580422787072 * u ^ 17 +
        396300232194785280 * u ^ 16 + 919903339201167360 * u ^ 15 +
        1577506895218409472 * u ^ 14 + 2070740052985872384 * u ^ 13 +
        2127082716059074560 * u ^ 12 + 1733100524611190784 * u ^ 11 +
        1128414580851068928 * u ^ 10 + 588584325576923136 * u ^ 9 +
        245465518073149440 * u ^ 8 + 81313160730605568 * u ^ 7 + 21142035504912384 * u ^ 6 +
        4234180386981888 * u ^ 5 + 634634547333120 * u ^ 4 + 68072225236992 * u ^ 3 +
        4853142190080 * u ^ 2 + 200399339520 * u + 3433881600) := by ring
  rw [key]
  exact Nat.le_add_right _ _

lemma growth (u : ℕ) : 27 ^ u * Fm u ≤ Fp u := by
  induction u with
  | zero => simp [Fp, Fm]
  | succ u ih =>
    have e1 : Fp (u + 1) = Fp u * ((∏ i ∈ range 12, (12 * u + i + 1)) *
        (∏ i ∈ range 3, (3 * u + i + 1)) * (∏ i ∈ range 2, (2 * u + i + 1)) ^ 2 * (u + 1)) := by
      unfold Fp
      rw [show 12 * (u + 1) = 12 * u + 12 by ring, show 3 * (u + 1) = 3 * u + 3 by ring,
        show 2 * (u + 1) = 2 * u + 2 by ring, fact_add, fact_add, fact_add, Nat.factorial_succ]
      ring
    have e2 : Fm (u + 1) = Fm u * ((∏ i ∈ range 6, (6 * u + i + 1)) ^ 2 *
        (∏ i ∈ range 4, (4 * u + i + 1)) ^ 2) := by
      unfold Fm
      rw [show 6 * (u + 1) = 6 * u + 6 by ring, show 4 * (u + 1) = 4 * u + 4 by ring,
        fact_add, fact_add]
      ring
    rw [e1, e2, pow_succ]
    calc 27 ^ u * 27 * (Fm u * ((∏ i ∈ range 6, (6 * u + i + 1)) ^ 2 *
        (∏ i ∈ range 4, (4 * u + i + 1)) ^ 2)) = (27 ^ u * Fm u) * (27 *
        ((∏ i ∈ range 6, (6 * u + i + 1)) ^ 2 * (∏ i ∈ range 4, (4 * u + i + 1)) ^ 2)) := by ring
      _ ≤ _ := Nat.mul_le_mul ih (poly u)

lemma numer_ge (N : ℕ) : Fp (N / 12) * (R 3 N * R 1 (N / 2)) ≤ numer N := by
  unfold Fp numer
  have h1 : (12 * (N / 12))! ≤ N ! := Nat.factorial_le (by omega)
  have h2 : (3 * (N / 12))! ≤ (N / 4)! := Nat.factorial_le (by omega)
  have h3 : (2 * (N / 12))! ≤ (N / 6)! := Nat.factorial_le (by omega)
  have h4 : (2 * (N / 12))! ^ 2 ≤ (N / 6)! ^ 2 := Nat.pow_le_pow_left h3 2
  calc (12 * (N / 12))! * (3 * (N / 12))! * (2 * (N / 12))! ^ 2 * (N / 12)! *
      (R 3 N * R 1 (N / 2)) ≤ N ! * (N / 4)! * (N / 6)! ^ 2 * (N / 12)! *
      (R 3 N * R 1 (N / 2)) := by gcongr
    _ = _ := by ring

lemma denom_le (N : ℕ) (hN : 1 ≤ N) : denom N ≤ Fm (N / 12) * N ^ 16 * (N + 2) ^ 2 *
    (R 3 N * R 1 (N / 2)) * 4 ^ (N / 12) * 4 ^ (N / 25) * N ^ (2 * (Nat.sqrt N + 1)) := by
  unfold denom Fm
  have a1 : (N / 2)! ≤ (6 * (N / 12))! * N ^ 5 := fact_bound _ _ _ _ (by omega) (by omega)
    (by omega) hN
  have a2 : (N / 3)! ≤ (4 * (N / 12))! * N ^ 3 := fact_bound _ _ _ _ (by omega) (by omega)
    (by omega) hN
  have r1 : R 1 N ≤ (N + 2) * R 3 N :=
    (R_cross N).1.trans (R_add_two 3 N)
  have r2 : R 3 (N / 2) ≤ (N + 2) * R 1 (N / 2) :=
    (R_cross (N / 2)).2.trans ((R_add_two 1 (N / 2)).trans (Nat.mul_le_mul_right _ (by omega)))
  have p1 := primorial_le_four_pow (N / 12)
  have p2 := primorial_le_four_pow (N / 25)
  have k1 := Kp_le N (by omega)
  calc (N / 2)! ^ 2 * (N / 3)! ^ 2 * R 1 N * R 3 (N / 2) * primorial (N / 12) *
      primorial (N / 25) * Kp N ≤ ((6 * (N / 12))! * N ^ 5) ^ 2 * ((4 * (N / 12))! * N ^ 3) ^ 2 *
      ((N + 2) * R 3 N) * ((N + 2) * R 1 (N / 2)) * 4 ^ (N / 12) * 4 ^ (N / 25) *
      N ^ (2 * (Nat.sqrt N + 1)) := by gcongr
    _ = _ := by ring

lemma small (n : ℕ) (h1 : 100 < n) (h2 : n < 260100) :
    ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n := by
  rcases lt_or_ge n 166 with c0 | c0
  · exact ⟨83, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 326 with c1 | c1
  · exact ⟨163, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 622 with c2 | c2
  · exact ⟨311, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 1238 with c3 | c3
  · exact ⟨619, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 2462 with c4 | c4
  · exact ⟨1231, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 4918 with c5 | c5
  · exact ⟨2459, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 9806 with c6 | c6
  · exact ⟨4903, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 19606 with c7 | c7
  · exact ⟨9803, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 39206 with c8 | c8
  · exact ⟨19603, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 78398 with c9 | c9
  · exact ⟨39199, by norm_num, by norm_num, by omega, by omega⟩
  rcases lt_or_ge n 156734 with c10 | c10
  · exact ⟨78367, by norm_num, by norm_num, by omega, by omega⟩
  exact ⟨156727, by norm_num, by norm_num, by omega, by omega⟩

lemma pow_lin (l : ℕ) (h : 9 ≤ l) : 30 * (l + 1) + 2 ≤ 2 ^ l := by
  induction l, h using Nat.le_induction with
  | base => norm_num
  | succ l _ ih => rw [pow_succ]; omega

lemma final_ineq (N : ℕ) (hN : 260100 ≤ N) :
    N ^ 16 * (N + 2) ^ 2 * 4 ^ (N / 12) * 4 ^ (N / 25) * N ^ (2 * (Nat.sqrt N + 1)) <
      27 ^ (N / 12) := by
  set s := Nat.sqrt N with hsdef
  have hs : 510 ≤ s := Nat.le_sqrt.2 (by omega)
  have hsN : s * s ≤ N := Nat.sqrt_le N
  have hNs : N < (s + 1) * (s + 1) := Nat.lt_succ_sqrt N
  have h2 : N + 2 ≤ (s + 2) ^ 2 := by nlinarith
  set l := Nat.log 2 (s + 2) with hldef
  have hl1 : s + 2 < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have hl2 : 2 ^ l ≤ s + 2 := Nat.pow_log_le_self 2 (by omega)
  have hl9 : 9 ≤ l := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have h30 : 30 * (l + 1) ≤ s := by have := pow_lin l hl9; omega
  have step1 : N ^ 16 * (N + 2) ^ 2 * 4 ^ (N / 12) * 4 ^ (N / 25) * N ^ (2 * (s + 1)) ≤
      (N + 2) ^ (2 * s + 20) * 2 ^ (2 * (N / 12) + 2 * (N / 25)) := by
    have a1 : N ^ 16 ≤ (N + 2) ^ 16 := Nat.pow_le_pow_left (by omega) _
    have a2 : N ^ (2 * (s + 1)) ≤ (N + 2) ^ (2 * (s + 1)) := Nat.pow_le_pow_left (by omega) _
    have e : (N + 2) ^ (2 * s + 20) * 2 ^ (2 * (N / 12) + 2 * (N / 25)) =
        (N + 2) ^ 16 * (N + 2) ^ 2 * 4 ^ (N / 12) * 4 ^ (N / 25) * (N + 2) ^ (2 * (s + 1)) := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, pow_add, ← pow_add, ← pow_add,
        show 2 * s + 20 = 16 + 2 + 2 * (s + 1) by ring, pow_add, pow_add]
      ring
    rw [e]
    gcongr
  have step2 : (N + 2) ^ (2 * s + 20) < 2 ^ ((l + 1) * (4 * s + 40)) := by
    calc (N + 2) ^ (2 * s + 20) ≤ ((s + 2) ^ 2) ^ (2 * s + 20) := Nat.pow_le_pow_left h2 _
      _ < ((2 ^ (l + 1)) ^ 2) ^ (2 * s + 20) :=
          Nat.pow_lt_pow_left (Nat.pow_lt_pow_left hl1 (by norm_num)) (by omega)
      _ = 2 ^ ((l + 1) * (4 * s + 40)) := by rw [← pow_mul, ← pow_mul]; ring_nf
  have step3 : (l + 1) * (4 * s + 40) + (2 * (N / 12) + 2 * (N / 25)) ≤ 19 * (N / 48) := by
    have m1 : 30 * (l + 1) * (4 * s + 40) ≤ s * (4 * s + 40) := Nat.mul_le_mul_right _ h30
    have m2 : 510 * s ≤ s * s := Nat.mul_le_mul_right _ hs
    have d1 : 48 * (N / 48) + 47 ≥ N := by omega
    have d2 : 12 * (N / 12) ≤ N := Nat.mul_div_le N 12
    have d3 : 25 * (N / 25) ≤ N := Nat.mul_div_le N 25
    nlinarith
  have step4 : 2 ^ (19 * (N / 48)) ≤ 27 ^ (N / 12) := by
    calc 2 ^ (19 * (N / 48)) = (2 ^ 19) ^ (N / 48) := by rw [pow_mul]
      _ ≤ (27 ^ 4) ^ (N / 48) := Nat.pow_le_pow_left (by norm_num) _
      _ = 27 ^ (4 * (N / 48)) := by rw [pow_mul]
      _ ≤ 27 ^ (N / 12) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc N ^ 16 * (N + 2) ^ 2 * 4 ^ (N / 12) * 4 ^ (N / 25) * N ^ (2 * (s + 1))
      ≤ (N + 2) ^ (2 * s + 20) * 2 ^ (2 * (N / 12) + 2 * (N / 25)) := step1
    _ < 2 ^ ((l + 1) * (4 * s + 40)) * 2 ^ (2 * (N / 12) + 2 * (N / 25)) :=
        Nat.mul_lt_mul_of_pos_right step2 (by positivity)
    _ = 2 ^ ((l + 1) * (4 * s + 40) + (2 * (N / 12) + 2 * (N / 25))) := (pow_add _ _ _).symm
    _ ≤ 2 ^ (19 * (N / 48)) := Nat.pow_le_pow_right (by norm_num) step3
    _ ≤ 27 ^ (N / 12) := step4

lemma big (n : ℕ) (hn : 260100 ≤ n) : ∃ q : ℕ, q.Prime ∧ q % 4 = 3 ∧ n < 2 * q ∧ q ≤ n := by
  by_contra hcon
  have hno : ∀ q, q.Prime → q % 4 = 3 → n < 2 * q → q ≤ n → False :=
    fun q hq h3 h1 h2 => hcon ⟨q, hq, h3, h1, h2⟩
  have hle := key_dvd n (by omega) hno
  have g := growth (n / 12)
  have lo := numer_ge n
  have hi := denom_le n (by omega)
  have hR : 0 < R 3 n * R 1 (n / 2) := Nat.mul_pos (R_pos _ _) (R_pos _ _)
  have hF : 0 < Fm (n / 12) := by unfold Fm; positivity
  have c1 : (Fm (n / 12) * (R 3 n * R 1 (n / 2))) * 27 ^ (n / 12) ≤
      (Fm (n / 12) * (R 3 n * R 1 (n / 2))) * (n ^ 16 * (n + 2) ^ 2 * 4 ^ (n / 12) *
        4 ^ (n / 25) * n ^ (2 * (Nat.sqrt n + 1))) := by
    calc (Fm (n / 12) * (R 3 n * R 1 (n / 2))) * 27 ^ (n / 12) =
        27 ^ (n / 12) * Fm (n / 12) * (R 3 n * R 1 (n / 2)) := by ring
      _ ≤ Fp (n / 12) * (R 3 n * R 1 (n / 2)) := Nat.mul_le_mul_right _ g
      _ ≤ numer n := lo
      _ ≤ denom n := hle
      _ ≤ _ := hi
      _ = _ := by ring
  have c2 := Nat.le_of_mul_le_mul_left c1 (Nat.mul_pos hF hR)
  have := final_ineq n hn
  omega

end E399

theorem OMA.solution : OMA.R_Erdos399_erdos_399_variants_sum_two_squares_R1.H2 := by
  intro n hn
  rcases lt_or_ge n 260100 with h | h
  · exact E399.small n hn h
  · exact E399.big n h
