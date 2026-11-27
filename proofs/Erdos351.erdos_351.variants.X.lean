import FormalConjectures.ErdosProblems.«351»

-- Problem: Erdős Problem 351 — X
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/351.lean:70 (declaration Erdos351.erdos_351.variants.X)
-- Credit: @sebastianbachmaier (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA351

open Finset

lemma pow_odd_inj {a b o o' : ℕ} (ho : Odd o) (ho' : Odd o') (h : 2 ^ a * o = 2 ^ b * o') :
    a = b ∧ o = o' := by
  rcases le_total a b with hab | hab
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases k with _ | k
    · simp at h2
      exact ⟨by simp, h2⟩
    · exfalso
      rw [h2] at ho
      exact Nat.not_odd_iff_even.mpr ((Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right o') ho
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [pow_add, mul_assoc] at h
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rcases k with _ | k
    · simp at h2
      exact ⟨by simp, h2⟩
    · exfalso
      rw [← h2] at ho'
      exact Nat.not_odd_iff_even.mpr ((Nat.even_pow.mpr ⟨even_two, by omega⟩).mul_right o) ho'

lemma disj_odd {X Y : Finset ℕ} {B : ℕ}
    (hX : ∀ x ∈ X, ∃ a o, x = 2 ^ a * o ∧ Odd o ∧ o ≤ B)
    (hY : ∀ y ∈ Y, ∃ a o, y = 2 ^ a * o ∧ Odd o ∧ B < o) : Disjoint X Y := by
  rw [Finset.disjoint_left]
  intro x hx hy
  obtain ⟨a, o, rfl, ho, hoB⟩ := hX x hx
  obtain ⟨b, o', h, ho', hB⟩ := hY _ hy
  have := (pow_odd_inj ho ho' h).2
  omega

lemma not_dvd_odd {q a o : ℕ} (hq : Odd q) (ho : Odd o) (hlt : o < q) : ¬ q ∣ 2 ^ a * o := by
  intro h
  have hc : Nat.Coprime q (2 ^ a) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hq)
  have h1 := hc.dvd_of_dvd_mul_left h
  have := Nat.le_of_dvd ho.pos h1
  omega

lemma greedy : ∀ a b : ℕ, 0 < b → a ≤ b →
    ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ b ≤ n * a) ∧ ∑ n ∈ S, (1 / (n : ℚ)) = a / b := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
  intro b hb hab
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨∅, by simp, by simp⟩
  set n := (b + a - 1) / a with hn
  have h1 : n * a ≤ b + a - 1 := Nat.div_mul_le_self _ _
  have h2 : b + a - 1 < n * a + a := Nat.lt_div_mul_add ha
  generalize hP : n * a = P at h1 h2
  have hbP : b ≤ P := by omega
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hP; omega
    · exact h0
  set a' := P - b with ha'
  have ha'a : a' < a := by omega
  have hbn : 0 < b * n := by positivity
  have ha'b : a' ≤ b * n := by nlinarith
  obtain ⟨S', hS', hsum⟩ := ih a' ha'a (b * n) hbn ha'b
  have hnS : n ∉ S' := by
    intro hm
    have := (hS' n hm).2
    have : a' < b := by omega
    nlinarith
  refine ⟨insert n S', ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ⟨by omega, by omega⟩
    · obtain ⟨hx0, hx1⟩ := hS' x hx
      refine ⟨hx0, ?_⟩
      have : x * a' ≤ x * a := Nat.mul_le_mul_left _ ha'a.le
      nlinarith
  · rw [Finset.sum_insert hnS, hsum]
    have hca : (a' : ℚ) = (n : ℚ) * a - b := by
      rw [ha', Nat.cast_sub hbP, ← hP]; push_cast; ring
    rw [hca]
    have : (n : ℚ) ≠ 0 := by positivity
    have : (b : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

lemma rat_nat_div (r : ℚ) (hr : 0 ≤ r) : ∃ a b : ℕ, 0 < b ∧ r = a / b := by
  refine ⟨r.num.toNat, r.den, r.den_pos, ?_⟩
  have h := Int.toNat_of_nonneg (Rat.num_nonneg.mpr hr)
  have : ((r.num.toNat : ℕ) : ℚ) = (r.num : ℚ) := by exact_mod_cast h
  rw [this]
  exact (Rat.num_div_den r).symm

lemma harm_unbounded (r : ℚ) : ∃ L : ℕ, r < ∑ i ∈ range L, (1 / ((i : ℚ) + 1)) := by
  have := (Real.tendsto_sum_range_one_div_nat_succ_atTop).eventually_gt_atTop (r : ℝ)
  obtain ⟨L, hL⟩ := this.exists
  refine ⟨L, ?_⟩
  have : ((∑ i ∈ range L, (1 / ((i : ℚ) + 1)) : ℚ) : ℝ) = ∑ i ∈ range L, (1 / ((i : ℝ) + 1)) := by
    push_cast; rfl
  exact_mod_cast (this ▸ hL)

lemma ef (r : ℚ) (hr : 0 ≤ r) : ∃ S : Finset ℕ, (∀ n ∈ S, 0 < n) ∧ ∑ n ∈ S, (1 / (n : ℚ)) = r := by
  classical
  have hex := harm_unbounded r
  set L0 := Nat.find hex with hL0
  have hspec : r < ∑ i ∈ range L0, (1 / ((i : ℚ) + 1)) := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos L0 with h0 | h0
  · rw [h0] at hspec; simp at hspec; linarith
  obtain ⟨L, hL⟩ : ∃ L, L0 = L + 1 := ⟨L0 - 1, by omega⟩
  have hmin : ∑ i ∈ range L, (1 / ((i : ℚ) + 1)) ≤ r := not_lt.mp (Nat.find_min hex (by omega))
  rw [hL, Finset.sum_range_succ] at hspec
  set H := ∑ i ∈ range L, (1 / ((i : ℚ) + 1)) with hH
  set rem := r - H with hrem
  have hrem0 : 0 ≤ rem := by linarith
  have hrem1 : rem < 1 / ((L : ℚ) + 1) := by linarith
  obtain ⟨a, b, hb, hab⟩ := rat_nat_div rem hrem0
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hlt : a * (L + 1) < b := by
    rw [hab, div_lt_div_iff₀ hbq (by positivity)] at hrem1
    have : (a : ℚ) * ((L : ℚ) + 1) < b := by linarith
    exact_mod_cast this
  have hale : a ≤ b := by nlinarith
  obtain ⟨S', hS', hsum⟩ := greedy a b hb hale
  refine ⟨(range L).image (fun i => i + 1) ∪ S', ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; omega
    · exact (hS' x hx).1
  · have hdisj : Disjoint ((range L).image (fun i => i + 1)) S' := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      have hi' := Finset.mem_range.mp hi
      have h3 := (hS' _ hx').2
      have h4 : a * (L + 1) < (i + 1) * a := lt_of_lt_of_le hlt h3
      have h5 : (i + 1) * a ≤ (L + 1) * a := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    rw [Finset.sum_union hdisj, hsum, Finset.sum_image (by intro x _ y _ h; simpa using h)]
    rw [← hab]
    push_cast
    rw [← hH, hrem]
    ring


def val (S : Finset ℕ) : ℚ := ∑ x ∈ S, ((x : ℚ) + 1 / x)

lemma val_union {S T : Finset ℕ} (h : Disjoint S T) : val (S ∪ T) = val S + val T :=
  Finset.sum_union h

def sA (u : ℕ) : Finset ℕ := {2 * (3 + 10 * u), 2 * (2 + 7 * u), 3 * (2 + 7 * u), 6 * (2 + 7 * u)}
def sB (u : ℕ) : Finset ℕ := {3 * (3 + 10 * u), 6 * (3 + 10 * u), 2 + 7 * u}
def rr (u : ℕ) : ℚ := 1 / (2 * (3 + 10 * (u : ℚ))) + 1 / (2 + 7 * (u : ℚ))

lemma val_sA (u : ℕ) (hu : 1 ≤ u) : val (sA u) = ((28 + 97 * u : ℕ) : ℚ) + rr u := by
  unfold val sA rr
  rw [Finset.sum_insert (by simp <;> omega), Finset.sum_insert (by simp <;> omega),
    Finset.sum_insert (by simp <;> omega), Finset.sum_singleton]
  push_cast
  field_simp
  ring

lemma val_sB (u : ℕ) (hu : 1 ≤ u) : val (sB u) = ((28 + 97 * u : ℕ) : ℚ) + 1 + rr u := by
  unfold val sB rr
  rw [Finset.sum_insert (by simp <;> omega), Finset.sum_insert (by simp <;> omega),
    Finset.sum_singleton]
  push_cast
  field_simp
  ring

lemma sAB_mem (u : ℕ) (hu : Odd u) (x : ℕ) (hx : x ∈ sA u ∨ x ∈ sB u) :
    2 + 7 * u ≤ x ∧ x ≤ 18 + 60 * u ∧ ∃ a o, x = 2 ^ a * o ∧ Odd o ∧ 2 + 7 * u ≤ o := by
  obtain ⟨k, rfl⟩ := hu
  have o1 : Odd (3 + 10 * (2 * k + 1)) := ⟨10 * k + 6, by ring⟩
  have o2 : Odd (2 + 7 * (2 * k + 1)) := ⟨7 * k + 4, by ring⟩
  have o3 : Odd (3 * (3 + 10 * (2 * k + 1))) := (by decide : Odd 3).mul o1
  have o4 : Odd (3 * (2 + 7 * (2 * k + 1))) := (by decide : Odd 3).mul o2
  simp only [sA, sB, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with (rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)
  · exact ⟨by omega, by omega, 1, _, by ring, o1, by omega⟩
  · exact ⟨by omega, by omega, 1, _, by ring, o2, by omega⟩
  · exact ⟨by omega, by omega, 0, _, by ring, o4, by omega⟩
  · exact ⟨by omega, by omega, 1, _, by ring, o4, by omega⟩
  · exact ⟨by omega, by omega, 0, _, by ring, o3, by omega⟩
  · exact ⟨by omega, by omega, 1, _, by ring, o3, by omega⟩
  · exact ⟨by omega, by omega, 0, _, by ring, o2, by omega⟩

def piece (U a j : ℕ) : Finset ℕ := if j < a then sB (U * 9 ^ j) else sA (U * 9 ^ j)

def SW (U N a : ℕ) : Finset ℕ := (range N).biUnion (piece U a)

lemma piece_mem (U a j : ℕ) (hU : Odd U) (x : ℕ) (hx : x ∈ piece U a j) :
    2 + 7 * (U * 9 ^ j) ≤ x ∧ x ≤ 18 + 60 * (U * 9 ^ j) ∧
      ∃ a o, x = 2 ^ a * o ∧ Odd o ∧ 2 + 7 * (U * 9 ^ j) ≤ o := by
  have hu : Odd (U * 9 ^ j) := hU.mul (Odd.pow (by decide))
  unfold piece at hx
  split_ifs at hx
  · exact sAB_mem _ hu x (Or.inr hx)
  · exact sAB_mem _ hu x (Or.inl hx)

lemma SW_mem (U N a : ℕ) (hU : Odd U) (x : ℕ) (hx : x ∈ SW U N a) :
    2 + 7 * U ≤ x ∧ x < 18 + 60 * (U * 9 ^ N) ∧
      ∃ a o, x = 2 ^ a * o ∧ Odd o ∧ 2 + 7 * U ≤ o := by
  obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
  have hj' := Finset.mem_range.mp hj
  obtain ⟨h1, h2, a', o, h3, h4, h5⟩ := piece_mem U a j hU x hxj
  have e1 : U ≤ U * 9 ^ j := Nat.le_mul_of_pos_right _ (by positivity)
  have e2 : 9 ^ j < 9 ^ N := Nat.pow_lt_pow_right (by norm_num) hj'
  have e3 : U * 9 ^ j < U * 9 ^ N := Nat.mul_lt_mul_of_pos_left e2 hU.pos
  exact ⟨by omega, by omega, a', o, h3, h4, by omega⟩

lemma SW_succ (U N a : ℕ) : SW U (N + 1) a = SW U N a ∪ piece U a N := by
  unfold SW
  rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]

lemma SW_val (U a : ℕ) (hU : Odd U) (hU6 : 6 ≤ U) : ∀ N, a ≤ N →
    val (SW U N a) = ∑ j ∈ range N, (((28 + 97 * (U * 9 ^ j) : ℕ) : ℚ) + rr (U * 9 ^ j)) + a := by
  have hpos : ∀ j, 1 ≤ U * 9 ^ j := fun j => Nat.mul_pos (by omega) (by positivity)
  have key : ∀ N, val (SW U N a) =
      ∑ j ∈ range N, (((28 + 97 * (U * 9 ^ j) : ℕ) : ℚ) + rr (U * 9 ^ j)) + (min a N : ℕ) := by
    intro N
    induction N with
    | zero => simp [SW, val]
    | succ N ih =>
      have hd : Disjoint (SW U N a) (piece U a N) := by
        rw [Finset.disjoint_left]
        intro x hx hx'
        obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
        have hj' := Finset.mem_range.mp hj
        have h1 := (piece_mem U a j hU x hxj).2.1
        have h2 := (piece_mem U a N hU x hx').1
        have e2 : 9 ^ (j + 1) ≤ 9 ^ N := Nat.pow_le_pow_right (by norm_num) hj'
        have e3 : U * 9 ^ (j + 1) ≤ U * 9 ^ N := Nat.mul_le_mul_left _ e2
        rw [pow_succ] at e3
        have e4 : U ≤ U * 9 ^ j := Nat.le_mul_of_pos_right _ (by positivity)
        nlinarith
      rw [SW_succ, val_union hd, ih, Finset.sum_range_succ]
      unfold piece
      split_ifs with h
      · rw [val_sB _ (hpos N)]
        rw [show min a (N + 1) = min a N + 1 by omega]
        push_cast; ring
      · rw [val_sA _ (hpos N)]
        rw [show min a (N + 1) = min a N by omega]
        ring
  intro N hN
  rw [key N, show min a N = a by omega]


def E : Finset ℕ := {3, 5, 7, 9, 11, 15, 35, 45, 231}

lemma E_prop : ∀ e ∈ E, Odd e ∧ 3 ≤ e ∧ e ≤ 231 ∧ e ≠ 17 := by decide

lemma E_recip : ∑ e ∈ E, (1 / (e : ℚ)) = 1 := by
  simp only [E]
  norm_num

lemma E_sum : ∑ e ∈ E, (e : ℚ) = 361 := by
  simp only [E]
  norm_num

def CP (T : ℕ) (I : Finset ℕ) (i : ℕ) : Finset ℕ :=
  if i ∈ I then E.image (fun e => 2 ^ (T + 5 + i) * e) else {2 ^ (T + 5 + i)}

def AB (T n : ℕ) : Finset ℕ := {17 * 2 ^ (T + n), 17 * 2 ^ (T + n + 4)}

def CH (T n : ℕ) (I : Finset ℕ) : Finset ℕ := (range n).biUnion (CP T I) ∪ AB T n

lemma CP_mem (T : ℕ) (I : Finset ℕ) (i x : ℕ) (hx : x ∈ CP T I i) :
    ∃ o, x = 2 ^ (T + 5 + i) * o ∧ Odd o ∧ o ≤ 231 ∧ o ≠ 17 := by
  unfold CP at hx
  split_ifs at hx
  · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨h1, _, h3, h4⟩ := E_prop e he
    exact ⟨e, rfl, h1, h3, h4⟩
  · rw [Finset.mem_singleton] at hx
    exact ⟨1, by rw [hx, mul_one], by decide, by norm_num, by norm_num⟩

lemma val_CP (T : ℕ) (I : Finset ℕ) (i : ℕ) :
    val (CP T I i) = (2 : ℚ) ^ (T + 5 + i) + 1 / (2 : ℚ) ^ (T + 5 + i) +
      (if i ∈ I then 360 * (2 : ℚ) ^ (T + 5 + i) else 0) := by
  unfold CP val
  split_ifs
  · rw [Finset.sum_image (by
      intro x _ y _ h
      exact Nat.eq_of_mul_eq_mul_left (by positivity) h)]
    have : ∀ e ∈ E, (((2 ^ (T + 5 + i) * e : ℕ) : ℚ) + 1 / ((2 ^ (T + 5 + i) * e : ℕ) : ℚ)) =
        (2 : ℚ) ^ (T + 5 + i) * (e : ℚ) + (1 / (2 : ℚ) ^ (T + 5 + i)) * (1 / (e : ℚ)) := by
      intro e _
      push_cast
      rw [one_div_mul_one_div]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      E_sum, E_recip]
    ring
  · rw [Finset.sum_singleton]
    push_cast
    ring

lemma val_AB (T n : ℕ) : val (AB T n) = 289 * (2 : ℚ) ^ (T + n) + 1 / (2 : ℚ) ^ (T + n + 4) := by
  unfold val AB
  rw [Finset.sum_insert (by
    simp only [Finset.mem_singleton]
    intro h
    have := Nat.eq_of_mul_eq_mul_left (by norm_num) h
    have := Nat.pow_right_injective (le_refl 2) this
    omega), Finset.sum_singleton]
  push_cast
  rw [pow_add _ (T + n) 4]
  field_simp
  ring

lemma geo_inv (T : ℕ) : ∀ n, ∑ i ∈ range n, (1 / (2 : ℚ) ^ (T + 5 + i)) =
    1 / (2 : ℚ) ^ (T + 4) - 1 / (2 : ℚ) ^ (T + 4 + n) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show T + 5 + n = (T + 4 + n) + 1 by omega,
      show T + 4 + (n + 1) = (T + 4 + n) + 1 by omega, pow_succ]
    field_simp
    ring

lemma CH_disj (T n : ℕ) (I : Finset ℕ) :
    Disjoint ((range n).biUnion (CP T I)) (AB T n) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨o, rfl, ho, _, ho17⟩ := CP_mem T I i x hxi
  simp only [AB, Finset.mem_insert, Finset.mem_singleton] at hx'
  rcases hx' with h | h
  · rw [mul_comm 17] at h
    exact ho17 (pow_odd_inj ho (by decide) h).2
  · rw [mul_comm 17] at h
    exact ho17 (pow_odd_inj ho (by decide) h).2

lemma CP_pd (T : ℕ) (I : Finset ℕ) (n : ℕ) :
    (↑(range n) : Set ℕ).PairwiseDisjoint (CP T I) := by
  intro i _ j _ hij
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨o, rfl, ho, _, _⟩ := CP_mem T I i x hx
  obtain ⟨o', h, ho', _, _⟩ := CP_mem T I j _ hx'
  have := (pow_odd_inj ho ho' h).1
  exact hij (by omega)

lemma val_CH (T n : ℕ) (I : Finset ℕ) (hI : I ⊆ range n) :
    val (CH T n I) = (((∑ i ∈ range n, 2 ^ (T + 5 + i)) + 289 * 2 ^ (T + n) : ℕ) : ℚ) +
      360 * ((∑ i ∈ I, 2 ^ (T + 5 + i) : ℕ) : ℚ) + 1 / (2 : ℚ) ^ (T + 4) := by
  unfold CH
  rw [val_union (CH_disj T n I), val_AB]
  have h1 : val ((range n).biUnion (CP T I)) = ∑ i ∈ range n, val (CP T I i) := by
    unfold val
    rw [Finset.sum_biUnion (CP_pd T I n)]
  rw [h1, Finset.sum_congr rfl (fun i _ => val_CP T I i), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.inter_eq_right.mpr hI, geo_inv]
  push_cast
  rw [← Finset.mul_sum, show T + 4 + n = (T + n) + 4 by omega]
  ring

lemma CH_mem (T n : ℕ) (I : Finset ℕ) (x : ℕ) (hx : x ∈ CH T n I) :
    (∃ a o, x = 2 ^ a * o ∧ Odd o ∧ o ≤ 231) ∧ 2 ^ T ≤ x := by
  unfold CH at hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨o, rfl, ho, ho2, _⟩ := CP_mem T I i x hxi
    refine ⟨⟨_, o, rfl, ho, ho2⟩, ?_⟩
    have : 2 ^ T ≤ 2 ^ (T + 5 + i) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact le_trans this (Nat.le_mul_of_pos_right _ ho.pos)
  · simp only [AB, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · refine ⟨⟨_, 17, mul_comm _ _, by decide, by norm_num⟩, ?_⟩
      have : 2 ^ T ≤ 2 ^ (T + n) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · refine ⟨⟨_, 17, mul_comm _ _, by decide, by norm_num⟩, ?_⟩
      have : 2 ^ T ≤ 2 ^ (T + n + 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega


lemma binary : ∀ n b : ℕ, b < 2 ^ n → ∃ I ⊆ range n, ∑ i ∈ I, 2 ^ i = b := by
  intro n
  induction n with
  | zero =>
    intro b hb
    exact ⟨∅, by simp, by simp at hb ⊢; omega⟩
  | succ n ih =>
    intro b hb
    by_cases h : b < 2 ^ n
    · obtain ⟨I, hI, hs⟩ := ih b h
      refine ⟨I, fun x hx => ?_, hs⟩
      have := Finset.mem_range.mp (hI hx)
      exact Finset.mem_range.mpr (by omega)
    · rw [pow_succ] at hb
      obtain ⟨I, hI, hs⟩ := ih (b - 2 ^ n) (by omega)
      have hn : n ∉ I := fun h => by simpa using hI h
      refine ⟨insert n I, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_range.mpr (by omega)
        · have := Finset.mem_range.mp (hI hx)
          exact Finset.mem_range.mpr (by omega)
      · rw [Finset.sum_insert hn, hs]
        omega

lemma main (K : ℕ) : ∃ M : ℕ, ∀ m ≥ M, ∃ S : Finset ℕ, (∀ x ∈ S, K ≤ x) ∧ val S = m := by
  classical
  obtain ⟨T, hT⟩ : ∃ T, T = K := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N, N = 360 * 2 ^ (T + 5) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U, U = 2 * K + 233 := ⟨_, rfl⟩
  have hUodd : Odd U := ⟨K + 116, by omega⟩
  obtain ⟨q, hq⟩ : ∃ q, q = 2 * (18 + 60 * (U * 9 ^ N)) + 1 := ⟨_, rfl⟩
  have hqodd : Odd q := ⟨_, hq⟩
  have hqpos : 0 < q := by omega
  obtain ⟨R, hR⟩ : ∃ R : ℚ, R = 1 / (2 : ℚ) ^ (T + 4) + ∑ j ∈ range N, rr (U * 9 ^ j) :=
    ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hR]
    unfold rr
    positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊R⌋₊ + 1 := ⟨_, rfl⟩
  have hkR : R < k := by
    rw [hk]
    push_cast
    exact Nat.lt_floor_add_one R
  obtain ⟨W', hW'pos, hW'sum⟩ := ef ((q : ℚ) * (k - R)) (by
    have : (0 : ℚ) ≤ k - R := by linarith
    positivity)
  have hWval : val (W'.image (fun w => q * w)) = ((∑ w ∈ W', q * w : ℕ) : ℚ) + (k - R) := by
    unfold val
    rw [Finset.sum_image (by
      intro x _ y _ h
      exact Nat.eq_of_mul_eq_mul_left hqpos h)]
    have : ∀ w ∈ W', (((q * w : ℕ) : ℚ) + 1 / ((q * w : ℕ) : ℚ)) =
        (q : ℚ) * w + (1 / (q : ℚ)) * (1 / (w : ℚ)) := by
      intro w _
      push_cast
      rw [one_div_mul_one_div]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hW'sum]
    push_cast
    have : (q : ℚ) ≠ 0 := by positivity
    field_simp
    rw [Finset.mul_sum]
  obtain ⟨base, hbase⟩ : ∃ base : ℕ,
      base = (∑ w ∈ W', q * w) + (∑ j ∈ range N, (28 + 97 * (U * 9 ^ j))) + k := ⟨_, rfl⟩
  have hcs : ∀ n, (∑ i ∈ range (n + 1), 2 ^ (T + 5 + i)) + 289 * 2 ^ (T + (n + 1)) =
      (∑ i ∈ range n, 2 ^ (T + 5 + i)) + 289 * 2 ^ (T + n) + 321 * 2 ^ (T + n) := by
    intro n
    rw [Finset.sum_range_succ, show T + (n + 1) = T + n + 1 by omega, pow_succ,
      show T + 5 + n = T + n + 5 by omega, pow_add]
    ring
  refine ⟨base + 289 * 2 ^ T, fun m hm => ?_⟩
  have hex : ∃ n, m < base + ((∑ i ∈ range (n + 1), 2 ^ (T + 5 + i)) + 289 * 2 ^ (T + (n + 1))) :=
    ⟨m, by
      have h1 : m < 2 ^ m := Nat.lt_two_pow_self
      have h2 : 2 ^ m ≤ 2 ^ (T + (m + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega⟩
  obtain ⟨n, hn⟩ : ∃ n, n = Nat.find hex := ⟨_, rfl⟩
  have hn1 : m < base + ((∑ i ∈ range (n + 1), 2 ^ (T + 5 + i)) + 289 * 2 ^ (T + (n + 1))) := by
    rw [hn]; exact Nat.find_spec hex
  have hn0 : base + ((∑ i ∈ range n, 2 ^ (T + 5 + i)) + 289 * 2 ^ (T + n)) ≤ m := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0]; simp; omega
    · obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      have := Nat.find_min hex (show n' < Nat.find hex by omega)
      rw [hn']; omega
  rw [hcs] at hn1
  obtain ⟨t, ht⟩ : ∃ t, t = m - (base + ((∑ i ∈ range n, 2 ^ (T + 5 + i)) + 289 * 2 ^ (T + n))) :=
    ⟨_, rfl⟩
  have htlt : t < 321 * 2 ^ (T + n) := by omega
  have hNpos : 0 < N := by rw [hN]; positivity
  have hb : t / N < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul hNpos]
    calc t < 321 * 2 ^ (T + n) := htlt
      _ ≤ 2 ^ n * N := by
        rw [hN, pow_add, pow_add]
        have : 0 < 2 ^ T * 2 ^ n := by positivity
        nlinarith
  have ha : t % N < N := Nat.mod_lt _ hNpos
  have htd := Nat.div_add_mod t N
  obtain ⟨I, hI, hIs⟩ := binary n (t / N) hb
  have hU6 : 6 ≤ U := by omega
  have hUc : U ≤ U * 9 ^ N := Nat.le_mul_of_pos_right _ (by positivity)
  refine ⟨W'.image (fun w => q * w) ∪ (SW U N (t % N) ∪ CH T n I), ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      have := hW'pos w hw
      have : q ≤ q * w := Nat.le_mul_of_pos_right _ this
      omega
    rcases Finset.mem_union.mp hx with hx | hx
    · have := (SW_mem U N _ hUodd x hx).1
      omega
    · have := (CH_mem T n I x hx).2
      have : K < 2 ^ K := Nat.lt_two_pow_self
      rw [← hT] at this
      omega
  · have hd1 : Disjoint (SW U N (t % N)) (CH T n I) := by
      refine (disj_odd (B := 231) (fun x hx => (CH_mem T n I x hx).1) ?_).symm
      intro y hy
      obtain ⟨_, _, a', o, h1, h2, h3⟩ := SW_mem U N _ hUodd y hy
      exact ⟨a', o, h1, h2, by omega⟩
    have hd2 : Disjoint (W'.image (fun w => q * w)) (SW U N (t % N) ∪ CH T n I) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      rcases Finset.mem_union.mp hx' with hx' | hx'
      · have h1 := (SW_mem U N _ hUodd _ hx').2.1
        have := hW'pos w hw
        have : q ≤ q * w := Nat.le_mul_of_pos_right _ this
        omega
      · obtain ⟨⟨a', o, h1, h2, h3⟩, _⟩ := CH_mem T n I _ hx'
        exact not_dvd_odd hqodd h2 (by omega) (h1 ▸ Dvd.intro w rfl)
    rw [val_union hd2, val_union hd1, hWval, SW_val U _ hUodd hU6 N ha.le, val_CH T n I hI]
    have hsI : ∑ i ∈ I, 2 ^ (T + 5 + i) = 2 ^ (T + 5) * (t / N) := by
      rw [← hIs, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => pow_add _ _ _)
    rw [hsI, Finset.sum_add_distrib]
    have hm' : m = base + ((∑ i ∈ range n, 2 ^ (T + 5 + i)) + 289 * 2 ^ (T + n)) +
        (N * (t / N) + t % N) := by omega
    have hNq : (N : ℚ) = 360 * 2 ^ (T + 5) := by rw [hN]; push_cast; ring
    rw [hm', hbase, hR]
    push_cast
    rw [hNq]
    ring

end OMA351

theorem OMA.solution : type_of% @Erdos351.erdos_351.variants.X := by
  show Erdos351.HasCompleteImage Polynomial.X
  intro B
  obtain ⟨ub, hub⟩ := (B.bddAbove : BddAbove (B : Set ℚ))
  obtain ⟨K0, hK0⟩ := exists_nat_gt ub
  obtain ⟨M, hM⟩ := OMA351.main (max K0 2)
  rw [Filter.eventually_atTop]
  refine ⟨M, fun m hm => ?_⟩
  obtain ⟨S, hSK, hSv⟩ := hM m hm
  have hinj : Set.InjOn (fun n : ℕ => (n : ℚ) + 1 / n) (S : Set ℕ) := by
    intro x hx y hy hxy
    have hx2 : 2 ≤ x := le_trans (le_max_right _ _) (hSK x hx)
    have hy2 : 2 ≤ y := le_trans (le_max_right _ _) (hSK y hy)
    simp only at hxy
    have bx : (1 : ℚ) / x < 1 := by
      rw [div_lt_one (by positivity)]; exact_mod_cast (by omega : 1 < x)
    have by' : (1 : ℚ) / y < 1 := by
      rw [div_lt_one (by positivity)]; exact_mod_cast (by omega : 1 < y)
    have px : (0 : ℚ) < 1 / x := by positivity
    have py : (0 : ℚ) < 1 / y := by positivity
    rcases lt_trichotomy x y with h | h | h
    · have : (x : ℚ) + 1 ≤ y := by exact_mod_cast h
      linarith
    · exact h
    · have : (y : ℚ) + 1 ≤ x := by exact_mod_cast h
      linarith
  refine ⟨S.image (fun n : ℕ => (n : ℚ) + 1 / n), ?_, ?_⟩
  · intro z hz
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
    obtain ⟨n, hn, rfl⟩ := hz
    refine ⟨⟨n, by simp⟩, ?_⟩
    intro hB
    have h1 := hub hB
    have h2 : (K0 : ℚ) ≤ n := by exact_mod_cast le_trans (le_max_left _ _) (hSK n hn)
    have h3 : (0 : ℚ) ≤ 1 / n := by positivity
    linarith
  · rw [Finset.sum_image hinj]
    exact hSv
