import FormalConjectures.ErdosProblems.«1140»

/-! Reduction of Erdős 1140 (finiteness) via a least-prime-factor sieve. The sieve, the
finite check below 200 and the residue analysis modulo 60 are taken from the existing reduction
of the variant at_most_one_exception. Here the class 3 modulo 4 only needs to be finite. -/

open Erdos1140

namespace OMA.R_Erdos1140_erdos_1140_R1

-- No further primes in the two surviving classes that are 1 modulo 4 (Epure and Gica).
def H1 : Prop :=
  ∀ n : ℕ, 199 < n → n.Prime → (n % 60 = 1 ∨ n % 60 = 49) → ¬ (
      (∀ x : ℕ, n ≠ 2 * x^2 + 1) ∧
      ∀ p : ℕ, p.Prime → p^2 ≤ n → ∀ r < p,
        2 * r^2 + p < n → ¬ (2 * r^2 ≡ n [MOD p]))

-- Only finitely many primes in the two surviving classes that are 3 modulo 4.
def H2 : Prop :=
  {n : ℕ | 199 < n ∧ n.Prime ∧ (n % 60 = 19 ∨ n % 60 = 31) ∧
      (∀ x : ℕ, n ≠ 2 * x^2 + 1) ∧
      ∀ p : ℕ, p.Prime → p^2 ≤ n → ∀ r < p,
        2 * r^2 + p < n → ¬ (2 * r^2 ≡ n [MOD p])}.Finite


lemma sieve_iff (n : ℕ) (hn : 0 < n) : Erdos1140Prop n ↔
    (∀ x : ℕ, n ≠ 2 * x^2 + 1) ∧
      ∀ p : ℕ, p.Prime → p^2 ≤ n → ∀ r < p,
        2 * r^2 + p < n → ¬ (2 * r^2 ≡ n [MOD p]) := by
  constructor
  · intro h
    constructor
    · intro x he
      have := h.2 x (by omega)
      simp [he] at this
    · intro p hp _ r _ hr he
      have hq := h.2 r (by omega)
      have hd := (Nat.modEq_iff_dvd' (by omega : 2*r^2 ≤ n)).mp he
      have := (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
      omega
  · rintro ⟨one, sieve⟩
    refine ⟨hn, ?_⟩
    intro x hx
    by_contra bad
    let m := n - 2*x^2
    let p := m.minFac
    have hm : 1 < m := by dsimp [m]; specialize one x; omega
    have hp : p.Prime := Nat.minFac_prime (by omega : m ≠ 1)
    have hsq : p^2 ≤ m := Nat.minFac_sq_le_self (by omega) bad
    have hpm : p < m := by have := hp.two_le; nlinarith
    have hmod : 2*x^2 ≡ n [MOD p] := (Nat.modEq_iff_dvd' hx.le).mpr (Nat.minFac_dvd m)
    have hred : 2*(x%p)^2 ≡ 2*x^2 [MOD p] :=
      (Nat.ModEq.refl 2).mul ((Nat.mod_modEq x p).pow 2)
    have hle := Nat.pow_le_pow_left (Nat.mod_le x p) 2
    dsimp [m] at hpm hsq
    exact sieve p hp (by omega) (x%p) (Nat.mod_lt _ hp.pos) (by omega) (hred.trans hmod)

lemma finite_check : ∀ n : Fin 200, 0 < n.val →
    (∀ x : Fin 10, 2*(x:ℕ)^2 < n.val → Nat.Prime (n.val-2*(x:ℕ)^2)) →
    n.val ∈ ({2,5,7,13,31,61,181,199} : Set ℕ) := by
  set_option maxRecDepth 10000 in decide +kernel

lemma residues (n : ℕ) (hn : 199 < n) (h : Erdos1140Prop n) :
    n % 60 = 1 ∨ n % 60 = 49 ∨ n % 60 = 19 ∨ n % 60 = 31 := by
  have prime (x : ℕ) (hx : 2*x^2 < n) := h.2 x hx
  have a := prime 0 (by norm_num; omega)
  have b := prime 1 (by norm_num; omega)
  have c := prime 2 (by norm_num; omega)
  norm_num at a b c
  have ex {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hlt : p < q) : ¬ p ∣ q :=
    fun hd => (Nat.ne_of_lt hlt) ((Nat.prime_dvd_prime_iff_eq hp hq).mp hd)
  have a2 := ex Nat.prime_two a (by omega)
  have a3 := ex Nat.prime_three a (by omega)
  have b3 := ex Nat.prime_three b (by omega)
  have a5 := ex (by decide : Nat.Prime 5) a (by omega)
  have b5 := ex (by decide : Nat.Prime 5) b (by omega)
  have c5 := ex (by decide : Nat.Prime 5) c (by omega)
  have check : ∀ k : Fin 60, k.val % 2 ≠ 0 → k.val % 3 = 1 →
      (k.val % 5 = 1 ∨ k.val % 5 = 4) →
      k.val = 1 ∨ k.val = 49 ∨ k.val = 19 ∨ k.val = 31 := by decide +kernel
  apply check ⟨n%60, Nat.mod_lt _ (by decide)⟩
  · rw [Nat.mod_mod_of_dvd n (by decide : 2 ∣ 60)]
    omega
  · rw [Nat.mod_mod_of_dvd n (by decide : 3 ∣ 60)]
    omega
  · rw [Nat.mod_mod_of_dvd n (by decide : 5 ∣ 60)]
    have avoid (j : ℕ) (hj : j ≤ n) (hnj : ¬ 5 ∣ n-j) : n%5 ≠ j%5 := by
      intro eq
      exact hnj ((Nat.modEq_iff_dvd' hj).mp eq.symm)
    have h0 := avoid 0 (by omega) (by simpa using a5)
    have h2 := avoid 2 (by omega) b5
    have h8 := avoid 8 (by omega) c5
    norm_num at h0 h2 h8
    omega

theorem main : H1 → H2 → type_of% @Erdos1140.erdos_1140 := by
  intro h1 h2
  have lift (n : ℕ) (hn : n ∈ {n : ℕ | Erdos1140Prop n} \ ({2,5,7,13,31,61,181,199} : Set ℕ)) :
      199 < n ∧ n.Prime ∧ (n % 60 = 19 ∨ n % 60 = 31) ∧
      (∀ x : ℕ, n ≠ 2 * x^2 + 1) ∧
      ∀ p : ℕ, p.Prime → p^2 ≤ n → ∀ r < p,
        2 * r^2 + p < n → ¬ (2 * r^2 ≡ n [MOD p]) := by
    obtain ⟨good, exc⟩ := hn
    change Erdos1140Prop n at good
    have large : 199 < n := by
      by_contra! small
      exact exc (finite_check ⟨n, by omega⟩ good.1 (fun x hx => good.2 x.val hx))
    have pr : n.Prime := by simpa using good.2 0 (by simpa using good.1)
    have criterion := (sieve_iff n good.1).mp good
    have res := residues n large good
    refine ⟨large, pr, ?_, criterion⟩
    rcases res with h | h | h
    · exact (h1 n large pr (Or.inl h) criterion).elim
    · exact (h1 n large pr (Or.inr h) criterion).elim
    · exact h
  have hT : ({n : ℕ | Erdos1140Prop n} \ ({2,5,7,13,31,61,181,199} : Set ℕ)).Finite :=
    h2.subset (fun n hn => lift n hn)
  have hsub : {n : ℕ | Erdos1140Prop n} ⊆
      ({n : ℕ | Erdos1140Prop n} \ ({2,5,7,13,31,61,181,199} : Set ℕ)) ∪
        ({2,5,7,13,31,61,181,199} : Set ℕ) := by
    intro n hn
    by_cases hk : n ∈ ({2,5,7,13,31,61,181,199} : Set ℕ)
    · exact Or.inr hk
    · exact Or.inl ⟨hn, hk⟩
  exact Set.not_infinite.mpr ((hT.union (Set.toFinite _)).subset hsub)

end OMA.R_Erdos1140_erdos_1140_R1
