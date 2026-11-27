import OMAReductions.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1

/-!
Missing colours in a proper (k+1)-edge-colouring of K_(k+1), k even (Erdős 835, step R1.H1.R1.H2).

Each vertex sees k distinct colours. Each colour class is a matching, found by a fixed-point-free
involution, so it covers an even number of the k + 1 vertices, hence at most k of them.
If two vertices missed the same colour, that class would cover at most k - 2 vertices, and
the total number of (vertex, seen colour) incidences would be at most k * k + k - 2 < (k + 1) * k.
-/

namespace OMAJohnsonMiss

open Finset

theorem main_thm : ∀ (k : ℕ), Even k → ∀ (Q : Finset (Fin (2 * k))), Q.card = k + 1 →
    ∀ e : Fin (2 * k) → Fin (2 * k) → Fin (k + 1),
      (∀ a ∈ Q, ∀ b ∈ Q, e a b = e b a) →
      (∀ a ∈ Q, ∀ b ∈ Q, ∀ d ∈ Q, b ≠ a → d ≠ a → b ≠ d → e a b ≠ e a d) →
      ∀ a ∈ Q, ∀ b ∈ Q, a ≠ b → ∀ i j : Fin (k + 1),
        (∀ t ∈ Q, t ≠ a → i ≠ e a t) → (∀ t ∈ Q, t ≠ b → j ≠ e b t) → i ≠ j := by
  classical
  intro k hk Q hQ e hsym hprop a ha b hb hab i j hi hj hij
  subst hij
  set used : Fin (2 * k) → Finset (Fin (k + 1)) := fun t => (Q.erase t).image (e t) with hused
  set M : Fin (k + 1) → Finset (Fin (2 * k)) := fun γ => Q.filter (fun t => γ ∈ used t) with hM
  have hcard_used : ∀ t ∈ Q, (used t).card = k := by
    intro t ht
    simp only [hused]
    rw [card_image_of_injOn, card_erase_of_mem ht, hQ]
    · rfl
    · intro x hx y hy hxy
      simp only [coe_erase, Set.mem_sdiff, mem_coe, Set.mem_singleton_iff] at hx hy
      by_contra hne
      exact hprop t ht x hx.1 y hy.1 hx.2 hy.2 hne hxy
  have hsum : ∑ t ∈ Q, (used t).card = ∑ γ, (M γ).card := by
    simp only [hM, card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    simp
  have heven : ∀ γ, Even (M γ).card := by
    intro γ
    have hmem : ∀ t ∈ M γ, ∃ s, s ∈ Q ∧ s ≠ t ∧ e t s = γ := by
      intro t ht
      simp only [hM, hused, mem_filter, mem_image, mem_erase] at ht
      obtain ⟨_, s, ⟨hs1, hs2⟩, hs3⟩ := ht
      exact ⟨s, hs2, hs1, hs3⟩
    have hz : ∑ t ∈ M γ, (1 : ZMod 2) = 0 := by
      refine sum_involution (fun t ht => Classical.choose (hmem t ht)) ?_ ?_ ?_ ?_
      · intro t ht; decide
      · intro t ht _
        exact (Classical.choose_spec (hmem t ht)).2.1
      · intro t ht
        have hs := Classical.choose_spec (hmem t ht)
        have htQ : t ∈ Q := (mem_filter.mp ht).1
        simp only [hM, hused, mem_filter, mem_image, mem_erase]
        refine ⟨hs.1, t, ⟨hs.2.1.symm, htQ⟩, ?_⟩
        rw [hsym _ hs.1 _ htQ]; exact hs.2.2
      · intro t ht
        have hs := Classical.choose_spec (hmem t ht)
        set s := Classical.choose (hmem t ht)
        have htQ : t ∈ Q := (mem_filter.mp ht).1
        have hsM : s ∈ M γ := by
          simp only [hM, hused, mem_filter, mem_image, mem_erase]
          refine ⟨hs.1, t, ⟨hs.2.1.symm, htQ⟩, ?_⟩
          rw [hsym _ hs.1 _ htQ]; exact hs.2.2
        have hs' := Classical.choose_spec (hmem s hsM)
        set s' := Classical.choose (hmem s hsM)
        by_contra hne
        apply hprop s hs.1 s' hs'.1 t htQ hs'.2.1 hs.2.1.symm hne
        rw [hs'.2.2, hsym _ hs.1 _ htQ, hs.2.2]
    rw [sum_const, nsmul_eq_mul, mul_one] at hz
    exact (ZMod.natCast_eq_zero_iff_even).mp hz
  have hk2 : 2 ≤ k := by
    have : 2 ≤ Q.card := by
      have h := card_le_card (show ({a, b} : Finset _) ⊆ Q by
        intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption)
      rwa [card_pair hab] at h
    obtain ⟨r, hr⟩ := hk
    omega
  have hle : ∀ γ, (M γ).card ≤ k := by
    intro γ
    have h1 : (M γ).card ≤ k + 1 := hQ ▸ card_filter_le _ _
    obtain ⟨r, hr⟩ := heven γ
    obtain ⟨s, hs⟩ := hk
    omega
  have hMi : (M i).card + 2 ≤ k := by
    have hsub : M i ⊆ (Q.erase a).erase b := by
      intro t ht
      simp only [hM, hused, mem_filter, mem_image, mem_erase] at ht ⊢
      obtain ⟨htQ, s, ⟨hs1, hs2⟩, hs3⟩ := ht
      refine ⟨?_, ?_, htQ⟩
      · rintro rfl; exact hj s hs2 hs1 hs3.symm
      · rintro rfl; exact hi s hs2 hs1 hs3.symm
    have h1 := card_le_card hsub
    rw [card_erase_of_mem (mem_erase.mpr ⟨hab.symm, hb⟩), card_erase_of_mem ha, hQ] at h1
    obtain ⟨r, hr⟩ := heven i
    obtain ⟨s, hs⟩ := hk
    omega
  have hL : ∑ t ∈ Q, (used t).card = (k + 1) * k := by
    rw [sum_congr rfl hcard_used, sum_const, hQ, smul_eq_mul]
  have hR : ∑ γ, (M γ).card ≤ (M i).card + k * k := by
    rw [← add_sum_erase _ _ (mem_univ i)]
    apply Nat.add_le_add_left
    calc ∑ γ ∈ univ.erase i, (M γ).card ≤ ∑ γ ∈ univ.erase i, k := sum_le_sum (fun γ _ => hle γ)
      _ = k * k := by rw [sum_const, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]; simp
  rw [hsum] at hL
  nlinarith

end OMAJohnsonMiss

theorem OMA.solution : OMA.R_Erdos835_erdos_835_variants_johnson_R1_H1_R1.H2 :=
  OMAJohnsonMiss.main_thm
