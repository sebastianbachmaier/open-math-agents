import OMAReductions.R_Hadamard_HadamardConjecture_R1

-- Step Hadamard.HadamardConjecture.R1.H1: hypothesis H1 of reduction Hadamard.HadamardConjecture.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ q : ℕ, IsPrimePow q → q % 4 = 3 → ∃ M, IsHadamard' (n := q + 1) M  /-- Paley II: a Hadamard matrix of order `2(q + 1)` for each prime power `q ≡ 1 (mod 4)`. -/

open Matrix

namespace OMAPaleyA

section
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem jac (hF : ringChar F ≠ 2) :
    ∑ x : F, quadraticChar F x * quadraticChar F (1 - x) = -quadraticChar F (-1) := by
  have h := jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)
  rw [(quadraticChar_isQuadratic F).inv] at h
  exact h

theorem shift (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = -1) {a b : F} (hab : a ≠ b) :
    ∑ c : F, quadraticChar F (c - a) * quadraticChar F (c - b) = -1 := by
  have hd : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  let e : F ≃ F := (Equiv.mulLeft₀ (b - a) hd).trans (Equiv.addLeft a)
  have hsum : ∑ c : F, quadraticChar F (c - a) * quadraticChar F (c - b) =
      ∑ x : F, (- (quadraticChar F x * quadraticChar F (1 - x))) := by
    symm
    apply Fintype.sum_equiv e
    intro x
    have hm : e x = a + (b - a) * x := rfl
    rw [hm]
    have h1 : a + (b - a) * x - a = (b - a) * x := by ring
    have h2 : a + (b - a) * x - b = (-1) * ((b - a) * (1 - x)) := by ring
    rw [h1, h2, map_mul, map_mul, map_mul, hneg]
    have hsq := quadraticChar_sq_one hd
    linear_combination (quadraticChar F x * quadraticChar F (1 - x)) * hsq
  rw [hsum, Finset.sum_neg_distrib, jac hF, hneg]
  ring

theorem diag (a : F) :
    ∑ c : F, quadraticChar F (c - a) * quadraticChar F (c - a) = (Fintype.card F : ℤ) - 1 := by
  have : ∀ c : F, quadraticChar F (c - a) * quadraticChar F (c - a) = 1 - if c = a then 1 else 0 := by
    intro c
    split_ifs with h
    · simp [h]
    · rw [← pow_two, sub_zero]; exact quadraticChar_sq_one (sub_ne_zero.mpr h)
  rw [Finset.sum_congr rfl (fun c _ => this c), Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

noncomputable def chi (x : F) : ℝ := ((quadraticChar F x : ℤ) : ℝ)

noncomputable def H : Matrix (Option F) (Option F) ℝ := fun x y =>
  match x, y with
  | none, _ => 1
  | some _, none => -1
  | some a, some b => chi (a - b) + if a = b then 1 else 0

theorem sumchi (hF : ringChar F ≠ 2) (b : F) : ∑ c : F, chi (c - b) = 0 := by
  have h : ∑ c : F, quadraticChar F (c - b) = ∑ c : F, quadraticChar F c :=
    Fintype.sum_equiv (Equiv.subRight b) _ _ (fun _ => rfl)
  rw [quadraticChar_sum_zero hF] at h
  have := congrArg (Int.cast : ℤ → ℝ) h
  push_cast at this
  simpa [chi] using this

theorem shiftR (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = -1) {a b : F} (hab : a ≠ b) :
    ∑ c : F, chi (c - a) * chi (c - b) = -1 := by
  have := congrArg (Int.cast : ℤ → ℝ) (shift hF hneg hab)
  push_cast at this
  simpa [chi] using this

theorem diagR (a : F) : ∑ c : F, chi (c - a) * chi (c - a) = (Fintype.card F : ℝ) - 1 := by
  have := congrArg (Int.cast : ℤ → ℝ) (diag a)
  push_cast at this
  simpa [chi] using this

theorem chi_zero : chi (0 : F) = 0 := by simp [chi]

theorem chi_neg (hneg : quadraticChar F (-1) = -1) (a b : F) : chi (b - a) = - chi (a - b) := by
  have h : b - a = (-1) * (a - b) := by ring
  simp only [chi, h, map_mul, hneg]
  push_cast; ring

theorem col (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = -1) (x y : Option F) :
    ∑ z, H z x * H z y = if x = y then (Fintype.card F : ℝ) + 1 else 0 := by
  rw [Fintype.sum_option]
  rcases x with _ | a <;> rcases y with _ | b
  · simp [H]; ring
  · simp only [H, one_mul, neg_one_mul, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sumchi hF b, reduceCtorEq, if_false]
    ring
  · simp only [H, mul_one, mul_neg_one, Finset.sum_neg_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, sumchi hF a, reduceCtorEq, if_false]
    ring
  · simp only [H, one_mul, mul_add, add_mul, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one,
      one_mul, mul_zero, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Option.some.injEq]
    by_cases hab : a = b
    · subst hab
      simp [diagR, chi_zero]
      ring
    · rw [shiftR hF hneg hab, chi_neg hneg a b]
      simp [hab, Ne.symm hab]

theorem entries (x y : Option F) : H x y ∈ ({1, -1} : Finset ℝ) := by
  rcases x with _ | a <;> rcases y with _ | b
  · simp [H]
  · simp [H]
  · simp [H]
  · by_cases hab : a = b
    · subst hab; simp [H, chi]
    · have hd : a - b ≠ 0 := sub_ne_zero.mpr hab
      rcases quadraticChar_dichotomy hd with h | h <;> simp [H, chi, h, hab]

end

theorem paley {F : Type*} [Field F] [Fintype F] [DecidableEq F] (q : ℕ)
    (hF : ringChar F ≠ 2) (hneg : quadraticChar F (-1) = -1) (hcard : Fintype.card F = q) :
    ∃ M, Hadamard.IsHadamard' (n := q + 1) M := by
  let e : Fin (q + 1) ≃ Option F :=
    (Fintype.equivFinOfCardEq (by simp [hcard] : Fintype.card (Option F) = q + 1)).symm
  refine ⟨H.submatrix e e, fun i j => entries _ _, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  simp only [transpose_apply, submatrix_apply]
  rw [show ∑ k, H (e k) (e i) * H (e k) (e j) = ∑ z, H z (e i) * H z (e j) from
    Fintype.sum_equiv e _ _ (fun _ => rfl)]
  rw [col hF hneg, Matrix.natCast_apply]
  simp [e.injective.eq_iff, hcard]

end OMAPaleyA

theorem OMA.solution : OMA.R_Hadamard_HadamardConjecture_R1.H1 := by
  intro q hq h3
  obtain ⟨p, k, hp, hk, rfl⟩ := hq
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have := Fact.mk hp'
  classical
  let _ : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card]; exact GaloisField.card p k hk.ne'
  have hp2 : p ≠ 2 := by
    rintro rfl
    have : 2 ∣ 2 ^ k := dvd_pow_self 2 hk.ne'
    omega
  have hF : ringChar (GaloisField p k) ≠ 2 := by
    rw [ringChar.eq (GaloisField p k) p]; exact hp2
  have hneg : quadraticChar (GaloisField p k) (-1) = -1 := by
    rw [quadraticChar_neg_one hF, hcard]
    exact ZMod.χ₄_nat_three_mod_four h3
  exact OMAPaleyA.paley (p ^ k) hF hneg hcard
