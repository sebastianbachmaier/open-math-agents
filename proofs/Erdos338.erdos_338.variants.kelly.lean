import FormalConjectures.ErdosProblems.«338»

-- Problem: Erdős Problem 338 — kelly
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/338.lean:174 (declaration Erdos338.erdos_338.variants.kelly)
-- Credit: @sebastianbachmaier (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Erdos338

namespace OMA.Kelly338

/-- m is a sum of at most four distinct elements of A. -/
def Goal (A : Set ℕ) (m : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ x ∈ S, x ∈ A) ∧ S.card ≤ 4 ∧ ∑ x ∈ S, x = m

/-- every n at least M0 is in A or a sum of two elements of A. -/
def Rep (A : Set ℕ) (M0 : ℕ) : Prop :=
  ∀ n, M0 ≤ n → n ∈ A ∨ ∃ a b, a ∈ A ∧ b ∈ A ∧ a + b = n

lemma goal1 {A : Set ℕ} {m a : ℕ} (ha : a ∈ A) (h : a = m) : Goal A m :=
  ⟨{a}, by simp [ha], by simp, by simp [h]⟩

lemma goal2 {A : Set ℕ} {m a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (h : a + b = m) : Goal A m :=
  ⟨{a, b}, by simp [ha, hb], Finset.card_le_two.trans (by norm_num),
    by rw [Finset.sum_pair hab, h]⟩

lemma goal3 {A : Set ℕ} {m a b c : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (h : a + b + c = m) : Goal A m := by
  refine ⟨{a, b, c}, by simp [ha, hb, hc], Finset.card_le_three.trans (by norm_num), ?_⟩
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_pair hbc]
  omega

lemma goal4 {A : Set ℕ} {m a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h : a + b + c + d = m) : Goal A m := by
  refine ⟨{a, b, c, d}, by simp [ha, hb, hc, hd], Finset.card_le_four, ?_⟩
  rw [Finset.sum_insert (by simp [hab, hac, had]), Finset.sum_insert (by simp [hbc, hbd]),
    Finset.sum_pair hcd]
  omega

lemma rep_of {A : Set ℕ} (hA : HasOrder A 2) : ∃ M0, 1 ≤ M0 ∧ Rep A M0 := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hA
  refine ⟨M + 1, by omega, fun n hn => ?_⟩
  obtain ⟨S, hSA, hcard, hsum⟩ := hM n (by omega)
  have : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
  rcases this with h | h | h
  · rw [Multiset.card_eq_zero.mp h] at hsum
    simp at hsum
    omega
  · obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h
    left
    simp at hsum
    subst hsum
    exact hSA a (by simp)
  · obtain ⟨a, b, rfl⟩ := Multiset.card_eq_two.mp h
    right
    refine ⟨a, b, hSA a (by simp), hSA b (by simp), ?_⟩
    simpa using hsum

lemma large_trick {A : Set ℕ} {M0 m t n : ℕ} (hR : Rep A M0) (ht : t ∈ A) (hn : M0 ≤ n)
    (hodd : n % 2 = 1) (hnt : n < t) (hsum : t + n = m) : Goal A m := by
  rcases hR n hn with h | ⟨a, b, ha, hb, hab⟩
  · exact goal2 ht h (by omega) hsum
  · by_cases hab' : a = b
    · omega
    · exact goal3 ht ha hb (by omega) (by omega) hab' (by omega)

lemma main_odd {A : Set ℕ} {M0 x y : ℕ} (hR : Rep A M0) (hM0 : 1 ≤ M0) (hx : x ∈ A)
    (hy : y ∈ A) (hxo : x % 2 = 1) (hxy4 : x % 4 = y % 4) (hne : x ≠ y) (hxM : M0 ≤ x)
    (hyM : M0 ≤ y) : ∀ m, 4 * (x + y) + M0 + 1 ≤ m → Goal A m := by
  intro m hm
  rcases hR m (by omega) with h | ⟨a0, b0, ha0, hb0, hab0⟩
  · exact goal1 h rfl
  by_cases h0 : a0 = b0
  swap
  · exact goal2 ha0 hb0 h0 hab0
  rcases hR (m - x - y) (by omega) with hE | ⟨r, s, hr, hs, hrs⟩
  · exact goal3 hx hy hE hne (by omega) (by omega) (by omega)
  by_cases hrs' : r = s
  · rcases hR ((x + y) / 2) (by omega) with hk | ⟨c, d, hc, hd, hcd⟩
    · exact goal3 ha0 hr hk (by omega) (by omega) (by omega) (by omega)
    · by_cases hcd' : c = d
      · omega
      · exact goal4 ha0 hr hc hd (by omega) (by omega) (by omega) (by omega) (by omega) hcd'
          (by omega)
  · by_cases h1 : r = x
    · exact large_trick (n := 2 * x + y) hR hs (by omega) (by omega) (by omega) (by omega)
    by_cases h2 : r = y
    · exact large_trick (n := x + 2 * y) hR hs (by omega) (by omega) (by omega) (by omega)
    by_cases h3 : s = x
    · exact large_trick (n := 2 * x + y) hR hr (by omega) (by omega) (by omega) (by omega)
    by_cases h4 : s = y
    · exact large_trick (n := x + 2 * y) hR hr (by omega) (by omega) (by omega) (by omega)
    exact goal4 hx hy hr hs hne (Ne.symm h1) (Ne.symm h3) (Ne.symm h2) (Ne.symm h4) hrs'
      (by omega)

/-- elements of A not divisible by 2 ^ j. -/
def G (A : Set ℕ) (j : ℕ) : Set ℕ := {a | a ∈ A ∧ ¬ 2 ^ j ∣ a}

lemma exists_inf {A : Set ℕ} {M0 : ℕ} (hR : Rep A M0) : ∃ j, (G A (j + 1)).Infinite := by
  by_contra hcon
  have hfin : ∀ j, (G A (j + 1)).Finite := fun j =>
    Set.not_infinite.mp (fun h => hcon ⟨j, h⟩)
  obtain ⟨L, hL⟩ := (hfin 0).bddAbove
  obtain ⟨L', hL'⟩ := (hfin L).bddAbove
  have hP : L + 1 < 2 ^ (L + 1) := Nat.lt_two_pow_self
  have hP2 : 2 ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have hpos : 1 ≤ 2 ^ L := Nat.one_le_two_pow
  set c := M0 + L + L' + 2 with hc
  have hQ : c ≤ 2 ^ L * c := Nat.le_mul_of_pos_left c hpos
  have hX : 2 ^ (L + 1) * c = 2 * (2 ^ L * c) := by rw [hP2]; ring
  set n := 2 ^ (L + 1) * c - 1 with hn
  have hodd : ¬ 2 ^ (0 + 1) ∣ n := by
    rintro ⟨q, hq⟩
    simp at hq
    omega
  rcases hR n (by omega) with h | ⟨a, b, ha, hb, hab⟩
  · have := hL (show n ∈ G A (0 + 1) from ⟨h, hodd⟩)
    omega
  · have key : ∀ a b, a ∈ A → b ∈ A → a + b = n → a % 2 = 1 → False := by
      intro a b ha hb hab hao
      have h1 : a ≤ L := hL (show a ∈ G A (0 + 1) from ⟨ha, by
        rintro ⟨q, hq⟩; simp at hq; omega⟩)
      have h2 : b ≤ L' := by
        refine hL' (show b ∈ G A (L + 1) from ⟨hb, ?_⟩)
        intro hdvd
        have h3 : 2 ^ (L + 1) ∣ a + 1 := by
          refine (Nat.dvd_add_right hdvd).mp ?_
          have : b + (a + 1) = 2 ^ (L + 1) * c := by omega
          rw [this]
          exact dvd_mul_right _ _
        have := Nat.le_of_dvd (by omega) h3
        omega
      omega
    by_cases hao : a % 2 = 1
    · exact key a b ha hb hab hao
    · exact key b a hb ha (by omega) (by omega)

lemma final (A : Set ℕ) (hA : HasOrder A 2) : HasRestrictedOrder A 4 := by
  classical
  obtain ⟨M0, hM1, hR⟩ := rep_of hA
  have hex := exists_inf hR
  obtain ⟨j, hj, hjmin⟩ : ∃ j, (G A (j + 1)).Infinite ∧ ∀ i < j, ¬ (G A (i + 1)).Infinite :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hjfin : (G A j).Finite := by
    rcases j with _ | i
    · refine Set.Finite.subset (Set.finite_empty) ?_
      intro a ha
      exact absurd (one_dvd a) (by simpa using ha.2)
    · exact Set.not_infinite.mp (hjmin i (by omega))
  obtain ⟨LB, hLB⟩ := hjfin.bddAbove
  have hpos : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  set B : Set ℕ := {b | 2 ^ j * b ∈ A} with hBdef
  set M0B := M0 + 2 * LB + 1 with hM0B
  have hRB : Rep B M0B := by
    intro k hk
    have hkk : k ≤ 2 ^ j * k := Nat.le_mul_of_pos_left k hpos
    rcases hR (2 ^ j * k) (by omega) with h | ⟨a, b, ha, hb, hab⟩
    · left; exact h
    · by_cases hda : 2 ^ j ∣ a
      · have hdb : 2 ^ j ∣ b := (Nat.dvd_add_right hda).mp (by rw [hab]; exact dvd_mul_right _ _)
        obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        right
        refine ⟨a', b', ha, hb, ?_⟩
        have : 2 ^ j * (a' + b') = 2 ^ j * k := by rw [mul_add]; exact hab
        exact Nat.eq_of_mul_eq_mul_left (by positivity) this
      · have hdb : ¬ 2 ^ j ∣ b := fun hdb =>
          hda ((Nat.dvd_add_left hdb).mp (by rw [hab]; exact dvd_mul_right _ _))
        have h1 := hLB (show a ∈ G A j from ⟨ha, hda⟩)
        have h2 := hLB (show b ∈ G A j from ⟨hb, hdb⟩)
        omega
  have hdiff : (G A (j + 1) \ G A j).Infinite := hj.sdiff hjfin
  have key : ∀ N, ∃ b, b ∈ B ∧ b % 2 = 1 ∧ N < b := by
    intro N
    obtain ⟨a, ⟨⟨haA, hnd⟩, hnd'⟩, hlt⟩ := hdiff.exists_gt (2 ^ j * N)
    have hd : 2 ^ j ∣ a := by
      by_contra h
      exact hnd' ⟨haA, h⟩
    obtain ⟨b, rfl⟩ := hd
    refine ⟨b, haA, ?_, ?_⟩
    · by_contra h
      apply hnd
      obtain ⟨c, rfl⟩ : 2 ∣ b := by omega
      exact ⟨c, by ring⟩
    · exact Nat.lt_of_mul_lt_mul_left hlt
  obtain ⟨b1, hb1, hb1o, hb1l⟩ := key M0B
  obtain ⟨b2, hb2, hb2o, hb2l⟩ := key b1
  obtain ⟨b3, hb3, hb3o, hb3l⟩ := key b2
  obtain ⟨x, y, hx, hy, hxo, hxy4, hne, hxM, hyM⟩ : ∃ x y, x ∈ B ∧ y ∈ B ∧ x % 2 = 1 ∧
      x % 4 = y % 4 ∧ x ≠ y ∧ M0B ≤ x ∧ M0B ≤ y := by
    have : b1 % 4 = b2 % 4 ∨ b1 % 4 = b3 % 4 ∨ b2 % 4 = b3 % 4 := by omega
    rcases this with h | h | h
    · exact ⟨b1, b2, hb1, hb2, hb1o, h, by omega, by omega, by omega⟩
    · exact ⟨b1, b3, hb1, hb3, hb1o, h, by omega, by omega, by omega⟩
    · exact ⟨b2, b3, hb2, hb3, hb2o, h, by omega, by omega, by omega⟩
  have hB := main_odd hRB (by omega) hx hy hxo hxy4 hne hxM hyM
  set Bd := 4 * (x + y) + M0B + 1 with hBd
  refine Filter.eventually_atTop.mpr ⟨2 ^ j * Bd + M0 + 2 * LB + 1, fun m hm => ?_⟩
  by_cases hdm : 2 ^ j ∣ m
  · obtain ⟨k, rfl⟩ := hdm
    have hk : Bd ≤ k := Nat.le_of_mul_le_mul_left (by omega) (by positivity : 0 < 2 ^ j)
    obtain ⟨S, hSB, hcard, hsum⟩ := hB k hk
    refine ⟨S.image (fun z => 2 ^ j * z), ?_, (Finset.card_image_le).trans hcard, ?_⟩
    · intro z hz
      simp only [Finset.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact hSB w hw
    · rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (by positivity) h),
        ← Finset.mul_sum, hsum]
  · rcases hR m (by omega) with h | ⟨a, b, ha, hb, hab⟩
    · exact goal1 h rfl
    · by_cases hab' : a = b
      · subst hab'
        have hna : ¬ 2 ^ j ∣ a := fun h => hdm (by rw [← hab]; exact Dvd.dvd.add h h)
        have := hLB (show a ∈ G A j from ⟨ha, hna⟩)
        omega
      · exact goal2 ha hb hab' hab

end OMA.Kelly338

theorem OMA.solution : type_of% @Erdos338.erdos_338.variants.kelly := by
  intro A hA
  exact OMA.Kelly338.final A hA
