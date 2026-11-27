import OMAReductions.R_Erdos936_erdos_936_variants_factorial_add_one_R1

-- Step Erdos936.erdos_936.variants.factorial_add_one.R1.H1: hypothesis H1 of reduction Erdos936.erdos_936.variants.factorial_add_one.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ c : ℕ, 0 < c → c.Powerful → (∏ p ∈ c.primeFactors, p) ^ 2 ∣ c  /-- Factorials eventually dominate every fixed power of the primorial. -/

namespace OMAB936

theorem aux (c : ℕ) (hc : ∀ p ∈ c.primeFactors, p ^ 2 ∣ c) :
    ∀ s : Finset ℕ, s ⊆ c.primeFactors → (∏ p ∈ s, p ^ 2) ∣ c := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha]
    have haP : a ∈ c.primeFactors := hs (Finset.mem_insert_self a s)
    have hsub : s ⊆ c.primeFactors := fun x hx => hs (Finset.mem_insert_of_mem hx)
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd _ (hc a haP) (ih hsub)
    apply Nat.Coprime.prod_right
    intro q hq
    have hqP : q ∈ c.primeFactors := hsub hq
    have hne : a ≠ q := fun h => ha (h ▸ hq)
    exact Nat.Coprime.pow 2 2 ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors haP)
      (Nat.prime_of_mem_primeFactors hqP)).2 hne)

end OMAB936

theorem OMA.solution : OMA.R_Erdos936_erdos_936_variants_factorial_add_one_R1.H1 := by
  intro c _ hc
  rw [← Finset.prod_pow]
  exact OMAB936.aux c hc _ (Finset.Subset.refl _)
