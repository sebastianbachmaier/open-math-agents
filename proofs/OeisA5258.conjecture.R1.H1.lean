import OMAReductions.R_OeisA5258_conjecture_R1

-- Step OeisA5258.conjecture.R1.H1: hypothesis H1 of reduction OeisA5258.conjecture.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ n : ℕ, 1 ≤ n → (n + 1).Prime → Irreducible (OeisA5258.aperyPoly n)  /-- The case where n + 1 is not prime (open). -/

open Polynomial

namespace OMAB5258

def c (n k : ℕ) : ℕ := (n.choose k) ^ 2 * ((n + k).choose k)

noncomputable def F (n : ℕ) : ℤ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((c n k : ℕ) : ℤ) * X ^ k

theorem coeff_F (n k : ℕ) : (F n).coeff k = if k ≤ n then ((c n k : ℕ) : ℤ) else 0 := by
  simp only [F, finsetSum_coeff, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem c_pos (n k : ℕ) (hk : k ≤ n) : 0 < c n k := by
  unfold c
  have h1 := Nat.choose_pos hk
  have h2 := Nat.choose_pos (show k ≤ n + k by omega)
  positivity

theorem natDegree_F (n : ℕ) : (F n).natDegree = n := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_F, if_neg]
    exact_mod_cast (not_le.2 hN)
  · rw [coeff_F, if_pos le_rfl]
    exact_mod_cast (c_pos n n le_rfl).ne'

theorem coeff_F_zero (n : ℕ) : (F n).coeff 0 = 1 := by
  rw [coeff_F, if_pos (Nat.zero_le _)]
  simp [c]

theorem map_F (n : ℕ) : (F n).map (Int.castRingHom ℚ) = OeisA5258.aperyPoly n := by
  simp [F, OeisA5258.aperyPoly, Polynomial.map_sum, c]

theorem coeff_G (n k : ℕ) (hk : k ≤ n) : (F n).reverse.coeff k = ((c n (n - k) : ℕ) : ℤ) := by
  rw [coeff_reverse, natDegree_F, revAt_le hk, coeff_F, if_pos (Nat.sub_le _ _)]

theorem natTrail_F (n : ℕ) : (F n).natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero]; right; rw [coeff_F_zero]; norm_num

theorem natDegree_G (n : ℕ) : (F n).reverse.natDegree = n := by
  rw [reverse_natDegree, natDegree_F, natTrail_F]; rfl

theorem monic_G (n : ℕ) : (F n).reverse.Monic := by
  unfold Monic
  rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero] <;> rw [coeff_F_zero]; norm_num

theorem irr_G (n : ℕ) (hn : 1 ≤ n) (hp : (n + 1).Prime) : Irreducible (F n).reverse := by
  set p := n + 1 with hpdef
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hP : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 hpZ
  apply irreducible_of_eisenstein_criterion hP
  · rw [(monic_G n).leadingCoeff, Ideal.mem_span_singleton]
    intro h
    have := Int.eq_one_of_dvd_one (by positivity) h
    have := hp.one_lt
    omega
  · intro m hm
    rw [degree_eq_natDegree (monic_G n).ne_zero, natDegree_G] at hm
    have hm' : m < n := by exact_mod_cast hm
    rw [coeff_G n m hm'.le, Ideal.mem_span_singleton]
    have hdv : p ∣ c n (n - m) := by
      unfold c
      apply Dvd.dvd.mul_left
      apply hp.dvd_choose <;> omega
    exact_mod_cast hdv
  · rw [degree_eq_natDegree (monic_G n).ne_zero, natDegree_G]
    exact_mod_cast hn
  · rw [coeff_G n 0 (Nat.zero_le _), Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro h
    have h' : p ^ 2 ∣ c n (n - 0) := by exact_mod_cast h
    simp only [c, Nat.sub_zero, Nat.choose_self, one_pow, one_mul] at h'
    have hle : ((n + n).choose n).factorization p ≤ 1 :=
      Nat.factorization_choose_le_one (by nlinarith)
    have hne : (n + n).choose n ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have := (hp.pow_dvd_iff_le_factorization hne).1 h'
    omega
  · exact (monic_G n).isPrimitive

theorem irr_F (n : ℕ) (hn : 1 ≤ n) (hp : (n + 1).Prime) : Irreducible (F n) := by
  have hG := irr_G n hn hp
  have key : ∀ a b : ℤ[X], F n = a * b → IsUnit a.reverse → IsUnit a := by
    intro a b hab hu
    have h0 : a.coeff 0 * b.coeff 0 = 1 := by
      rw [← mul_coeff_zero, ← hab, coeff_F_zero]
    have ha0 : a.coeff 0 ≠ 0 := left_ne_zero_of_mul_eq_one h0
    have hd : a.reverse.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    rw [reverse_natDegree] at hd
    have ht : a.natTrailingDegree = 0 := by
      rw [natTrailingDegree_eq_zero]; right; exact ha0
    rw [ht, Nat.sub_zero] at hd
    rw [eq_C_of_natDegree_eq_zero hd]
    exact isUnit_C.2 (IsUnit.of_mul_eq_one _ h0)
  refine ⟨?_, ?_⟩
  · intro hu
    have := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_F] at this
    omega
  · intro a b hab
    have hr : (F n).reverse = a.reverse * b.reverse := by
      rw [hab, reverse_mul_of_domain]
    rcases hG.isUnit_or_isUnit hr with h | h
    · exact Or.inl (key a b hab h)
    · exact Or.inr (key b a (by rw [hab, mul_comm]) h)

end OMAB5258

theorem OMA.solution : OMA.R_OeisA5258_conjecture_R1.H1 := by
  intro n hn hp
  rw [← OMAB5258.map_F]
  have hprim : (OMAB5258.F n).IsPrimitive := by
    intro r hr
    have := (C_dvd_iff_dvd_coeff r _).1 hr 0
    rw [OMAB5258.coeff_F_zero] at this
    exact isUnit_of_dvd_one this
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).1 (OMAB5258.irr_F n hn hp)
