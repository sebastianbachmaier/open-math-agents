import OMAReductions.R_Erdos1191_erdos_1191_parts_ii_R1

/-!
# A polylogarithmic pair-sum encoding (Erdős Problem 1191 ii, step R1.H2)

E writes the binary expansion of a in chunks of lengths 1, 2, 4, 8, ...; each chunk
is placed in a slot of radix 2^(2^k) * 64, so pair sums never carry between slots.
The 6 spare bits of each slot hold the k-th binary digit of j = log2 a and the
k-th base-4 digit of j^2. Unique mixed-radix digits of E a + E b then give a + b,
j_a + j_b and j_a^2 + j_b^2, which determine the label pair. With log2 a < 2^(K+1)
only K + 1 = O(log log a) slots are used, so E a is at most 58 a (1 + log2 a)^6.
-/

open Filter Set


namespace OMAH2Enc

open Finset

/-- mixed radix place values -/
def Pr (r : ℕ → ℕ) (k : ℕ) : ℕ := ∏ i ∈ range k, r i

lemma Pr_succ (r : ℕ → ℕ) (k : ℕ) : Pr r (k + 1) = Pr r k * r k := by
  simp [Pr, prod_range_succ]

lemma Pr_pos (r : ℕ → ℕ) (hr : ∀ i, 0 < r i) (k : ℕ) : 0 < Pr r k :=
  prod_pos (fun i _ => hr i)

lemma Pr_const (c k : ℕ) : Pr (fun _ => c) k = c ^ k := by
  simp [Pr]

lemma Pr_mono (r : ℕ → ℕ) (hr : ∀ i, 0 < r i) {m n : ℕ} (h : m ≤ n) : Pr r m ≤ Pr r n := by
  induction n, h using Nat.le_induction with
  | base => exact le_rfl
  | succ n _ ih =>
    rw [Pr_succ]
    exact ih.trans (Nat.le_mul_of_pos_right _ (hr n))

lemma decomp (r : ℕ → ℕ) (x : ℕ) : ∀ n, x % Pr r n = ∑ k ∈ range n, (x / Pr r k % r k) * Pr r k
  | 0 => by simp [Pr, Nat.mod_one]
  | n + 1 => by
    rw [sum_range_succ, ← decomp r x n, Pr_succ, Nat.mod_mul]
    ring

lemma decomp' (r : ℕ → ℕ) (x n : ℕ) (hx : x < Pr r n) :
    x = ∑ k ∈ range n, (x / Pr r k % r k) * Pr r k := by
  rw [← decomp, Nat.mod_eq_of_lt hx]

lemma sum_lt (r : ℕ → ℕ) (d : ℕ → ℕ) : ∀ n, (∀ k < n, d k < r k) →
    ∑ k ∈ range n, d k * Pr r k < Pr r n
  | 0, _ => by simp [Pr]
  | n + 1, hd => by
    rw [sum_range_succ, Pr_succ]
    have h1 := sum_lt r d n (fun k hk => hd k (by omega))
    have h2 : d n + 1 ≤ r n := hd n (by omega)
    calc ∑ k ∈ range n, d k * Pr r k + d n * Pr r n
        < Pr r n + d n * Pr r n := by omega
      _ = (d n + 1) * Pr r n := by ring
      _ ≤ r n * Pr r n := Nat.mul_le_mul_right _ h2
      _ = Pr r n * r n := by ring

lemma uniq (r : ℕ → ℕ) (hr : ∀ i, 0 < r i) (d e : ℕ → ℕ) : ∀ n, (∀ k < n, d k < r k) →
    (∀ k < n, e k < r k) →
    ∑ k ∈ range n, d k * Pr r k = ∑ k ∈ range n, e k * Pr r k → ∀ k < n, d k = e k
  | 0, _, _, _ => by intro k hk; omega
  | n + 1, hd, he, h => by
    rw [sum_range_succ, sum_range_succ] at h
    have hA := sum_lt r d n (fun k hk => hd k (by omega))
    have hB := sum_lt r e n (fun k hk => he k (by omega))
    have hP := Pr_pos r hr n
    set A := ∑ k ∈ range n, d k * Pr r k
    set B := ∑ k ∈ range n, e k * Pr r k
    have h1 : (A + d n * Pr r n) / Pr r n = d n := by
      rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hA, zero_add]
    have h2 : (B + e n * Pr r n) / Pr r n = e n := by
      rw [Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hB, zero_add]
    have h3 : (A + d n * Pr r n) % Pr r n = A := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hA]
    have h4 : (B + e n * Pr r n) % Pr r n = B := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hB]
    have hdn : d n = e n := by rw [← h1, ← h2, h]
    have hAB : A = B := by rw [← h3, ← h4, h]
    have ih := uniq r hr d e n (fun k hk => hd k (by omega)) (fun k hk => he k (by omega)) hAB
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact ih k hk
    · subst hk; exact hdn

/-- radix of the k-th slot -/
def R (k : ℕ) : ℕ := 2 ^ (2 ^ k) * 64

/-- radix of the k-th chunk of the plain binary number -/
def C (k : ℕ) : ℕ := 2 ^ (2 ^ k)

def alpha (a k : ℕ) : ℕ := a / Pr C k % C k

def code (j k : ℕ) : ℕ := j / 2 ^ k % 2 + 4 * (j ^ 2 / 4 ^ k % 4)

def digit (a k : ℕ) : ℕ := 32 * alpha a k + code (Nat.log 2 a) k

def E (a : ℕ) : ℕ := ∑ k ∈ range (a + 1), digit a k * Pr R k

lemma C_pos (i : ℕ) : 0 < C i := by unfold C; positivity
lemma R_pos (i : ℕ) : 0 < R i := by unfold R; positivity

lemma two_mul_PrC (k : ℕ) : 2 * Pr C k = 2 ^ (2 ^ k) := by
  induction k with
  | zero => simp [Pr]
  | succ k ih =>
    rw [Pr_succ, ← mul_assoc, ih, C, ← pow_add, pow_succ]
    ring_nf

lemma PrR_eq (k : ℕ) : Pr R k = Pr C k * 64 ^ k := by
  simp only [Pr, R, C, prod_mul_distrib, prod_const, card_range]

lemma pow_le_PrC (k : ℕ) : 2 ^ k ≤ Pr C k := by
  have h := two_mul_PrC k
  have : 2 ^ (k + 1) ≤ 2 ^ (2 ^ k) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.lt_two_pow_self)
  rw [pow_succ] at this
  omega

lemma alpha_lt (a k : ℕ) : alpha a k < C k := Nat.mod_lt _ (C_pos k)

lemma code_le (j k : ℕ) : code j k ≤ 13 := by
  unfold code
  have := Nat.mod_lt (j / 2 ^ k) (show 0 < 2 by norm_num)
  have := Nat.mod_lt (j ^ 2 / 4 ^ k) (show 0 < 4 by norm_num)
  omega

lemma code_zero (j k : ℕ) (h : j < 2 ^ k) : code j k = 0 := by
  unfold code
  have h2 : j ^ 2 < 4 ^ k := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left h (by norm_num)
  rw [Nat.div_eq_of_lt h, Nat.div_eq_of_lt h2]

lemma digit_zero (a k : ℕ) (ha : a < Pr C k) (hj : Nat.log 2 a < 2 ^ k) : digit a k = 0 := by
  unfold digit alpha
  rw [Nat.div_eq_of_lt ha, code_zero _ _ hj]
  simp

lemma digit_zero_of_gt (a k : ℕ) (hk : a < k) : digit a k = 0 := by
  apply digit_zero
  · exact lt_of_lt_of_le (hk.trans Nat.lt_two_pow_self) (pow_le_PrC k)
  · exact lt_of_le_of_lt (Nat.log_le_self 2 a) (hk.trans Nat.lt_two_pow_self)

lemma E_eq (a n : ℕ) (hn : a < n) : E a = ∑ k ∈ range n, digit a k * Pr R k := by
  unfold E
  apply sum_subset
  · intro k hk; simp at hk ⊢; omega
  · intro k _ hk
    simp at hk
    rw [digit_zero_of_gt a k (by omega), zero_mul]

lemma pair_of_sq {p q s t : ℕ} (h1 : p + q = s + t) (h2 : p ^ 2 + q ^ 2 = s ^ 2 + t ^ 2) :
    (p = s ∧ q = t) ∨ (p = t ∧ q = s) := by
  have hq : (q : ℤ) = s + t - p := by omega
  have h2' : (p : ℤ) ^ 2 + q ^ 2 = s ^ 2 + t ^ 2 := by exact_mod_cast h2
  rw [hq] at h2'
  have h3 : 2 * (((p : ℤ) - s) * (p - t)) = 0 := by linear_combination h2'
  have : ((p : ℤ) - s) * (p - t) = 0 := by omega
  rcases mul_eq_zero.mp this with h | h
  · left; omega
  · right; omega

lemma digit_add_lt (a b k : ℕ) : digit a k + digit b k < R k := by
  unfold digit R
  have h1 := alpha_lt a k
  have h2 := alpha_lt b k
  have h3 := code_le (Nat.log 2 a) k
  have h4 := code_le (Nat.log 2 b) k
  unfold C at h1 h2
  omega

lemma decode (a b u v : ℕ) (h : E a + E b = E u + E v) :
    a + b = u + v ∧ ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)) := by
  set n := a + b + u + v + 1 with hn
  rw [E_eq a n (by omega), E_eq b n (by omega), E_eq u n (by omega), E_eq v n (by omega),
    ← sum_add_distrib, ← sum_add_distrib] at h
  simp only [← add_mul] at h
  have hd := uniq R R_pos (fun k => digit a k + digit b k) (fun k => digit u k + digit v k) n
    (fun k _ => digit_add_lt a b k) (fun k _ => digit_add_lt u v k) h
  -- per-slot equalities
  have hα : ∀ k < n, alpha a k + alpha b k = alpha u k + alpha v k := by
    intro k hk
    have := hd k hk
    simp only [digit] at this
    have := code_le (Nat.log 2 a) k
    have := code_le (Nat.log 2 b) k
    have := code_le (Nat.log 2 u) k
    have := code_le (Nat.log 2 v) k
    omega
  have hc : ∀ k < n, code (Nat.log 2 a) k + code (Nat.log 2 b) k =
      code (Nat.log 2 u) k + code (Nat.log 2 v) k := by
    intro k hk
    have := hd k hk
    simp only [digit] at this
    have := hα k hk
    omega
  have hbit : ∀ x y z w : ℕ, ∀ k < n, code x k + code y k = code z k + code w k →
      x / 2 ^ k % 2 + y / 2 ^ k % 2 = z / 2 ^ k % 2 + w / 2 ^ k % 2 ∧
      x ^ 2 / 4 ^ k % 4 + y ^ 2 / 4 ^ k % 4 = z ^ 2 / 4 ^ k % 4 + w ^ 2 / 4 ^ k % 4 := by
    intro x y z w k _ hxy
    unfold code at hxy
    have := Nat.mod_lt (x / 2 ^ k) (show 0 < 2 by norm_num)
    have := Nat.mod_lt (y / 2 ^ k) (show 0 < 2 by norm_num)
    have := Nat.mod_lt (z / 2 ^ k) (show 0 < 2 by norm_num)
    have := Nat.mod_lt (w / 2 ^ k) (show 0 < 2 by norm_num)
    omega
  have hlt : ∀ x, x < n → x < Pr C n := fun x hx =>
    lt_of_lt_of_le (hx.trans Nat.lt_two_pow_self) (pow_le_PrC n)
  have hlog : ∀ x, x < n → Nat.log 2 x < 2 ^ n := fun x hx =>
    lt_of_le_of_lt (Nat.log_le_self 2 x) (hx.trans Nat.lt_two_pow_self)
  have hlog2 : ∀ x, x < n → (Nat.log 2 x) ^ 2 < 4 ^ n := by
    intro x hx
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left (hlog x hx) (by norm_num)
  have dA : ∀ x, x < n → x = ∑ k ∈ range n, alpha x k * Pr C k := fun x hx =>
    decomp' C x n (hlt x hx)
  have dJ : ∀ x, x < n → Nat.log 2 x = ∑ k ∈ range n, (Nat.log 2 x / 2 ^ k % 2) * 2 ^ k := by
    intro x hx
    have := decomp' (fun _ => 2) (Nat.log 2 x) n (by rw [Pr_const]; exact hlog x hx)
    simpa only [Pr_const] using this
  have dQ : ∀ x, x < n →
      (Nat.log 2 x) ^ 2 = ∑ k ∈ range n, ((Nat.log 2 x) ^ 2 / 4 ^ k % 4) * 4 ^ k := by
    intro x hx
    have := decomp' (fun _ => 4) ((Nat.log 2 x) ^ 2) n (by rw [Pr_const]; exact hlog2 x hx)
    simpa only [Pr_const] using this
  refine ⟨?_, ?_⟩
  · rw [dA a (by omega), dA b (by omega), dA u (by omega), dA v (by omega),
      ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro k hk
    rw [← add_mul, ← add_mul, hα k (mem_range.mp hk)]
  · apply pair_of_sq
    · rw [dJ a (by omega), dJ b (by omega), dJ u (by omega), dJ v (by omega),
        ← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      rw [← add_mul, ← add_mul, (hbit _ _ _ _ k (mem_range.mp hk) (hc k (mem_range.mp hk))).1]
    · rw [dQ a (by omega), dQ b (by omega), dQ u (by omega), dQ v (by omega),
        ← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro k hk
      rw [← add_mul, ← add_mul, (hbit _ _ _ _ k (mem_range.mp hk) (hc k (mem_range.mp hk))).2]

lemma PrC_le (a j K : ℕ) (ha : 1 ≤ a) (hj : j = Nat.log 2 a) (hK : K = Nat.log 2 (j + 1)) :
    Pr C K ≤ a := by
  have h1 : 2 ^ K ≤ j + 1 := by rw [hK]; exact Nat.pow_log_le_self 2 (by omega)
  have h2 : 2 ^ j ≤ a := by rw [hj]; exact Nat.pow_log_le_self 2 (by omega)
  have h3 := two_mul_PrC K
  have h4 : 2 ^ (2 ^ K) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) h1
  rw [pow_succ] at h4
  omega

lemma lt_PrC (a j K : ℕ) (hj : j = Nat.log 2 a) (hK : K = Nat.log 2 (j + 1)) :
    a < Pr C (K + 1) := by
  have h1 : j + 1 < 2 ^ (K + 1) := by rw [hK]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h2 : a < 2 ^ (j + 1) := by rw [hj]; exact Nat.lt_pow_succ_log_self (by norm_num) _
  have h3 := two_mul_PrC (K + 1)
  have h4 : 2 ^ (j + 2) ≤ 2 ^ (2 ^ (K + 1)) := Nat.pow_le_pow_right (by norm_num) h1
  rw [pow_succ] at h4
  omega

lemma sum_PrC_le : ∀ m, ∑ k ∈ range (m + 1), Pr C k ≤ 2 * Pr C m
  | 0 => by simp [Pr]
  | m + 1 => by
    rw [sum_range_succ]
    have ih := sum_PrC_le m
    have h : 2 * Pr C m ≤ Pr C (m + 1) := by
      rw [Pr_succ, mul_comm]
      apply Nat.mul_le_mul_left
      unfold C
      exact le_self_pow₀ (by norm_num) (by positivity)
    omega

lemma E_le (a : ℕ) (ha : 1 ≤ a) : E a ≤ 58 * a * (Nat.log 2 a + 1) ^ 6 := by
  obtain ⟨j, hj⟩ : ∃ j, j = Nat.log 2 a := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = Nat.log 2 (j + 1) := ⟨_, rfl⟩
  rw [← hj]
  have hK1 : 2 ^ K ≤ j + 1 := by rw [hK]; exact Nat.pow_log_le_self 2 (by omega)
  have hjK : j < 2 ^ (K + 1) := by
    have h : j + 1 < 2 ^ (K + 1) := by rw [hK]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    omega
  have hlt := lt_PrC a j K hj hK
  have hE : E a = ∑ k ∈ range (K + 1), digit a k * Pr R k := by
    unfold E
    symm
    apply sum_subset_zero_on_sdiff
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      have : K + 1 ≤ a + 1 := by
        by_contra hc
        have h3 : Pr C (a + 1) ≤ Pr C K := Pr_mono C C_pos (by omega)
        have h4 : a + 1 < Pr C (a + 1) :=
          lt_of_lt_of_le Nat.lt_two_pow_self (pow_le_PrC (a + 1))
        have h5 := PrC_le a j K ha hj hK
        omega
      omega
    · intro k hk
      simp only [Finset.mem_sdiff, Finset.mem_range] at hk
      rw [digit_zero a k, zero_mul]
      · exact lt_of_lt_of_le hlt (Pr_mono C C_pos (by omega))
      · rw [← hj]; exact lt_of_lt_of_le hjK (Nat.pow_le_pow_right (by norm_num) (by omega))
    · intro k _; rfl
  have hA : ∑ k ∈ range (K + 1), alpha a k * Pr C k = a :=
    (decomp' C a (K + 1) hlt).symm
  have hS := sum_PrC_le K
  have hL := PrC_le a j K ha hj hK
  have h64 : 64 ^ K ≤ (j + 1) ^ 6 := by
    calc 64 ^ K = (2 ^ K) ^ 6 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ (j + 1) ^ 6 := Nat.pow_le_pow_left hK1 6
  have hbound : ∀ k ∈ range (K + 1), digit a k * Pr R k ≤
      (32 * (alpha a k * Pr C k) + 13 * Pr C k) * 64 ^ K := by
    intro k hk
    rw [PrR_eq]
    have hk' : k ≤ K := by simp at hk; omega
    have h1 : 64 ^ k ≤ 64 ^ K := Nat.pow_le_pow_right (by norm_num) hk'
    have h2 : digit a k ≤ 32 * alpha a k + 13 := by
      unfold digit; have := code_le (Nat.log 2 a) k; omega
    calc digit a k * (Pr C k * 64 ^ k) ≤ (32 * alpha a k + 13) * (Pr C k * 64 ^ K) :=
          Nat.mul_le_mul h2 (Nat.mul_le_mul_left _ h1)
      _ = (32 * (alpha a k * Pr C k) + 13 * Pr C k) * 64 ^ K := by ring
  calc E a ≤ ∑ k ∈ range (K + 1), (32 * (alpha a k * Pr C k) + 13 * Pr C k) * 64 ^ K := by
        rw [hE]; exact sum_le_sum hbound
    _ = (32 * (∑ k ∈ range (K + 1), alpha a k * Pr C k) +
          13 * ∑ k ∈ range (K + 1), Pr C k) * 64 ^ K := by
        rw [← sum_mul, sum_add_distrib, mul_sum, mul_sum]
    _ ≤ (32 * a + 13 * (2 * a)) * 64 ^ K := by
        rw [hA]; apply Nat.mul_le_mul_right; omega
    _ = 58 * a * 64 ^ K := by ring
    _ ≤ 58 * a * (j + 1) ^ 6 := Nat.mul_le_mul_left _ h64

lemma le_E (a : ℕ) : a ≤ E a := by
  rw [E_eq a (a + 1) (by omega)]
  have hlt : a < Pr C (a + 1) :=
    lt_of_lt_of_le (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega)))
      (pow_le_PrC (a + 1))
  conv_lhs => rw [decomp' C a (a + 1) hlt]
  apply sum_le_sum
  intro k _
  rw [PrR_eq]
  apply Nat.mul_le_mul
  · show alpha a k ≤ digit a k
    unfold digit; omega
  · exact Nat.le_mul_of_pos_right _ (by positivity)

theorem H2_main : ∃ (E : ℕ → ℕ) (d : ℕ),
    (∀ a b u v, E a + E b = E u + E v →
      a + b = u + v ∧
        ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
         (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) ∧
    ∀ᶠ x : ℕ in atTop, ∀ a ∈ Set.Icc 1 (x / (1 + Nat.log 2 x) ^ d), E a ∈ Set.Icc 1 x := by
  refine ⟨E, 7, decode, ?_⟩
  rw [Filter.eventually_atTop]
  refine ⟨2 ^ 57, fun x hx a ha => ?_⟩
  obtain ⟨ha1, ha2⟩ := ha
  set L := Nat.log 2 x
  have hL : 57 ≤ L := Nat.le_log_of_pow_le (by norm_num) hx
  have hmul : a * (1 + L) ^ 7 ≤ x :=
    (Nat.mul_le_mul_right _ ha2).trans (Nat.div_mul_le_self _ _)
  have hax : a ≤ x := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hmul
  have hj : Nat.log 2 a ≤ L := Nat.log_mono_right hax
  refine ⟨le_trans ha1 (le_E a), ?_⟩
  calc E a ≤ 58 * a * (Nat.log 2 a + 1) ^ 6 := E_le a ha1
    _ ≤ (1 + L) * a * (1 + L) ^ 6 := by
        apply Nat.mul_le_mul
        · apply Nat.mul_le_mul_right; omega
        · apply Nat.pow_le_pow_left; omega
    _ = a * (1 + L) ^ 7 := by ring
    _ ≤ x := hmul

end OMAH2Enc

theorem OMA.solution : OMA.R_Erdos1191_erdos_1191_parts_ii_R1.H2 := OMAH2Enc.H2_main
