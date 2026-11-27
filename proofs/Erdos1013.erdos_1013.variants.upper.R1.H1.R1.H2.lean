import OMAReductions.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1

-- Step Erdos1013.erdos_1013.variants.upper.R1.H1.R1.H2: hypothesis H2 of reduction Erdos1013.erdos_1013.variants.upper.R1.H1.R1
-- Credit: @sebastianbachmaier
-- H2 := ∀ (n k c : ℕ) (G : SimpleGraph (Fin n)),   Gᶜ.CliqueFree k → G.Colorable c → n ≤ c * k  /-- The choice of k: for ε in (0,1) there is δ > 0 such that for every bound K and all large n some k ≥ K has n log k ≤ (1/2 - δ) k^2 and (1 - ε) (n / log n)^(1/2) k ≤ n. -/
theorem OMA.solution : OMA.R_Erdos1013_erdos_1013_variants_upper_R1_H1_R1.H2 := by
  classical
  intro n k c G hk hc
  obtain ⟨C⟩ := hc
  have hfib : ∀ i : Fin c, (Finset.univ.filter (fun v => C v = i)).card ≤ k := by
    intro i
    by_contra h
    push Not at h
    obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq h.le
    apply hk t
    refine ⟨?_, htc⟩
    intro x hx y hy hxy
    have hx' := ht hx
    have hy' := ht hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx' hy'
    rw [SimpleGraph.compl_adj]
    refine ⟨hxy, fun hadj => C.valid hadj ?_⟩
    rw [hx', hy']
  calc n = (Finset.univ : Finset (Fin n)).card := by simp
    _ = ∑ i : Fin c, (Finset.univ.filter (fun v => C v = i)).card :=
        Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
    _ ≤ ∑ _i : Fin c, k := Finset.sum_le_sum (fun i _ => hfib i)
    _ = c * k := by simp
