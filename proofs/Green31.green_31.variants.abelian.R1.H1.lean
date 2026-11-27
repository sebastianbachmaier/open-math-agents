import OMAReductions.R_Green31_green_31_variants_abelian_R1

/-! Step H1 of the reduction Green31.green_31.variants.abelian.R1: a Sidon set of size
at least sqrt(L)/2 inside the range [0, L).

For L < 16 the sets {0} and {0, 1} suffice. Otherwise, with s = Nat.sqrt L and k = s / 2,
Bertrand's postulate gives an odd prime p with k < p <= 2k - 1. The Erdos-Turan prefix
a |-> 2 p a + (a^2 mod p), for a = 0, ..., k, lies below p (2k + 1) < L and is Sidon,
since equal sums force equal index sums and equal index products in ZMod p.
The Sidon lemma is adapted (shifted by one) from the checked proof
proofs/Erdos44.sidon_set_lower_bound.lean. -/

namespace OMA.Green31SidonH1

lemma bosePrefix_sidon {p k : ℕ} (hp : Nat.Prime p) (hk : k < p) (hp2 : p ≠ 2) :
    IsSidon
      (((Finset.range (k + 1)).image (fun a => 2 * p * a + (a * a) % p) : Finset ℕ) :
        Set ℕ) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  intro i₁ hi₁ j₁ hj₁ i₂ hi₂ j₂ hj₂ hsum
  rw [Finset.mem_coe, Finset.mem_image] at hi₁ hj₁ hi₂ hj₂
  obtain ⟨a, ha, rfl⟩ := hi₁
  obtain ⟨c, hc, rfl⟩ := hj₁
  obtain ⟨b, hb, rfl⟩ := hi₂
  obtain ⟨d, hd, rfl⟩ := hj₂
  have ha_lt : a < p := by rw [Finset.mem_range] at ha; omega
  have hb_lt : b < p := by rw [Finset.mem_range] at hb; omega
  have hc_lt : c < p := by rw [Finset.mem_range] at hc; omega
  have hd_lt : d < p := by rw [Finset.mem_range] at hd; omega
  have hpos : 0 < p := hp.pos
  have hsum' :
      2 * p * (a + b) + ((a * a) % p + (b * b) % p) =
        2 * p * (c + d) + ((c * c) % p + (d * d) % p) := by
    have hcancel :
        2 * p * a + (a * a) % p + (2 * p * b + (b * b) % p) =
          2 * p * c + (c * c) % p + (2 * p * d + (d * d) % p) := by
      omega
    calc
      2 * p * (a + b) + ((a * a) % p + (b * b) % p)
          = 2 * p * a + (a * a) % p + (2 * p * b + (b * b) % p) := by ring
      _ = 2 * p * c + (c * c) % p + (2 * p * d + (d * d) % p) := hcancel
      _ = 2 * p * (c + d) + ((c * c) % p + (d * d) % p) := by ring
  have hσ : (a * a) % p + (b * b) % p < 2 * p := by
    have haσ : (a * a) % p < p := Nat.mod_lt _ hpos
    have hbσ : (b * b) % p < p := Nat.mod_lt _ hpos
    omega
  have hτ : (c * c) % p + (d * d) % p < 2 * p := by
    have hcτ : (c * c) % p < p := Nat.mod_lt _ hpos
    have hdτ : (d * d) % p < p := Nat.mod_lt _ hpos
    omega
  have htwo : 0 < 2 * p := by omega
  have hquot (q r : ℕ) (hr : r < 2 * p) :
      (r + (2 * p) * q) / (2 * p) = q := by
    rw [Nat.add_mul_div_left _ _ htwo, Nat.div_eq_of_lt hr, zero_add]
  have hidx : a + b = c + d := by
    have hleft := hquot (a + b) ((a * a) % p + (b * b) % p) hσ
    have hright := hquot (c + d) ((c * c) % p + (d * d) % p) hτ
    have hcomm :
        (a * a) % p + (b * b) % p + (2 * p) * (a + b) =
          (c * c) % p + (d * d) % p + (2 * p) * (c + d) := by
      calc
        (a * a) % p + (b * b) % p + (2 * p) * (a + b)
            = (2 * p) * (a + b) + ((a * a) % p + (b * b) % p) := by ac_rfl
        _ = (2 * p) * (c + d) + ((c * c) % p + (d * d) % p) := hsum'
        _ = (c * c) % p + (d * d) % p + (2 * p) * (c + d) := by ac_rfl
    rw [← hleft, ← hright, hcomm]
  have hres :
      (a * a) % p + (b * b) % p = (c * c) % p + (d * d) % p :=
    Nat.add_left_cancel (n := 2 * p * (a + b)) (by simpa [hidx] using hsum')
  have hsq :
      (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
    calc
      (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2
          = (((a * a) % p : ℕ) : ZMod p) + (((b * b) % p : ℕ) : ZMod p) := by
            simp [pow_two, ZMod.natCast_mod]
      _ = ((((a * a) % p + (b * b) % p : ℕ) : ZMod p)) := by
            push_cast
            rfl
      _ = ((((c * c) % p + (d * d) % p : ℕ) : ZMod p)) := by
            exact congr_arg (Nat.cast : ℕ → ZMod p) hres
      _ = (c : ZMod p) ^ 2 + (d : ZMod p) ^ 2 := by
            simp [pow_two, ZMod.natCast_mod]
  have hsumZ : (a : ZMod p) + b = (c : ZMod p) + d := by
    have : ((a + b : ℕ) : ZMod p) = (c + d : ℕ) := congr_arg (Nat.cast : ℕ → ZMod p) hidx
    simpa [Nat.cast_add] using this
  have htwo_mul :
      (2 : ZMod p) * (a : ZMod p) * b = (2 : ZMod p) * (c : ZMod p) * d := by
    have hleft : (2 : ZMod p) * a * b = ((a : ZMod p) + b) ^ 2 - ((a : ZMod p) ^ 2 + b ^ 2) := by
      ring
    have hright : (2 : ZMod p) * c * d = ((c : ZMod p) + d) ^ 2 - ((c : ZMod p) ^ 2 + d ^ 2) := by
      ring
    rw [hleft, hright, hsumZ, hsq]
  have htwo_ne : (2 : ZMod p) ≠ 0 := by
    rw [ne_eq, ← Nat.cast_two, ZMod.natCast_eq_zero_iff]
    intro hdiv
    have : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    have : 2 ≤ p := hp.two_le
    omega
  have hprod : (a : ZMod p) * b = (c : ZMod p) * d := by
    apply mul_left_cancel₀ htwo_ne
    simpa [mul_assoc, mul_left_comm, mul_comm] using htwo_mul
  have hfactor : ((c : ZMod p) - a) * ((c : ZMod p) - b) = 0 := by
    calc
      ((c : ZMod p) - a) * (c - b)
          = (c : ZMod p) ^ 2 - ((a : ZMod p) + b) * c + a * b := by ring
      _ = (c : ZMod p) ^ 2 - ((c : ZMod p) + d) * c + c * d := by rw [hsumZ, hprod]
      _ = 0 := by ring
  have hc_eq : (c : ZMod p) = a ∨ (c : ZMod p) = b := by
    rcases mul_eq_zero.mp hfactor with hca | hcb
    · left
      exact sub_eq_zero.mp hca
    · right
      exact sub_eq_zero.mp hcb
  have lift {x y : ℕ} (hx : x < p) (hy : y < p) (hxy : (x : ZMod p) = y) : x = y := by
    have hmod : x % p = y % p := (ZMod.natCast_eq_natCast_iff' x y p).mp hxy
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hmod
  rcases hc_eq with hca | hcb
  · have hac : a = c := lift ha_lt hc_lt hca.symm
    have hbd : b = d := by omega
    left
    subst hac
    subst hbd
    exact ⟨rfl, rfl⟩
  · have hab : b = c := lift hb_lt hc_lt hcb.symm
    have had : a = d := by omega
    right
    subst hab
    subst had
    exact ⟨rfl, rfl⟩

theorem sidon_range :
    ∀ L : ℕ, 0 < L → ∃ A : Finset ℕ,
      A ⊆ Finset.range L ∧ IsSidon (A : Set ℕ) ∧ L ≤ 4 * A.card ^ 2 := by
  intro L hL
  by_cases h4 : L < 4
  · refine ⟨{0}, ?_, by decide, ?_⟩
    · simp [Finset.subset_iff]; omega
    · simp; omega
  by_cases h16 : L < 16
  · refine ⟨{0, 1}, ?_, by decide, ?_⟩
    · simp [Finset.subset_iff]; omega
    · simp; omega
  have hL16 : 16 ≤ L := by omega
  set s := Nat.sqrt L with hs_def
  have hsL : s * s ≤ L := Nat.sqrt_le L
  have hLs : L < (s + 1) * (s + 1) := Nat.lt_succ_sqrt L
  have hs4 : 4 ≤ s := by
    by_contra h
    have : s + 1 ≤ 4 := by omega
    have : (s + 1) * (s + 1) ≤ 4 * 4 := Nat.mul_le_mul this this
    omega
  set k := s / 2 with hk_def
  have hk2 : 2 ≤ k := by omega
  obtain ⟨p, hp, hklt, hple⟩ := Nat.exists_prime_lt_and_le_two_mul k (by omega : k ≠ 0)
  have hp3 : 3 ≤ p := by omega
  have hp_le : p ≤ 2 * k - 1 := by
    have hpne : p ≠ 2 * k := by
      intro hpk
      have hdiv : 2 ∣ p := ⟨k, hpk⟩
      have := hp.eq_one_or_self_of_dvd 2 hdiv
      omega
    omega
  have hmul_le : p * (2 * k + 1) < L := by
    have h1 : p * (2 * k + 1) ≤ (2 * k - 1) * (2 * k + 1) := Nat.mul_le_mul_right _ hp_le
    have h2 : (2 * k - 1) * (2 * k + 1) < (2 * k) * (2 * k) := by
      obtain ⟨j, hj⟩ : ∃ j, 2 * k - 1 = j ∧ 2 * k = j + 1 := ⟨2 * k - 1, rfl, by omega⟩
      rw [hj.1, hj.2]; nlinarith
    have h3 : (2 * k) * (2 * k) ≤ s * s := Nat.mul_le_mul (by omega) (by omega)
    omega
  let g : ℕ → ℕ := fun a => 2 * p * a + (a * a) % p
  let A : Finset ℕ := (Finset.range (k + 1)).image g
  have hA_sub : A ⊆ Finset.range L := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a, ha, rfl⟩ := hx
    have ha_le : a ≤ k := by rw [Finset.mem_range] at ha; omega
    have hmul : 2 * p * a ≤ 2 * p * k := Nat.mul_le_mul_left _ ha_le
    have hr : (a * a) % p < p := Nat.mod_lt _ hp.pos
    have heq : 2 * p * k + p = p * (2 * k + 1) := by ring
    rw [Finset.mem_range]
    change 2 * p * a + (a * a) % p < L
    omega
  have hsid : IsSidon (A : Set ℕ) := bosePrefix_sidon hp (by omega) (by omega)
  have hinj : Set.InjOn g (Finset.range (k + 1) : Set ℕ) := by
    intro a ha b hb hab
    have ha_lt : a < p := by
      have : a ∈ Finset.range (k + 1) := by simpa using ha
      rw [Finset.mem_range] at this; omega
    have hb_lt : b < p := by
      have : b ∈ Finset.range (k + 1) := by simpa using hb
      rw [Finset.mem_range] at this; omega
    have hga : g a / (2 * p) = a := by
      change (2 * p * a + (a * a) % p) / (2 * p) = a
      rw [show 2 * p * a + (a * a) % p = (a * a) % p + (2 * p) * a by ring,
        Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt (by have := Nat.mod_lt (a * a) hp.pos; omega), zero_add]
    have hgb : g b / (2 * p) = b := by
      change (2 * p * b + (b * b) % p) / (2 * p) = b
      rw [show 2 * p * b + (b * b) % p = (b * b) % p + (2 * p) * b by ring,
        Nat.add_mul_div_left _ _ (by omega),
        Nat.div_eq_of_lt (by have := Nat.mod_lt (b * b) hp.pos; omega), zero_add]
    rw [← hga, ← hgb, hab]
  have hcard : A.card = k + 1 := by
    rw [show A = (Finset.range (k + 1)).image g from rfl, Finset.card_image_of_injOn hinj]
    simp
  refine ⟨A, hA_sub, hsid, ?_⟩
  rw [hcard]
  have : s + 1 ≤ 2 * (k + 1) := by omega
  have : (s + 1) * (s + 1) ≤ (2 * (k + 1)) * (2 * (k + 1)) := Nat.mul_le_mul this this
  nlinarith

end OMA.Green31SidonH1

theorem OMA.solution : OMA.R_Green31_green_31_variants_abelian_R1.H1 :=
  OMA.Green31SidonH1.sidon_range
