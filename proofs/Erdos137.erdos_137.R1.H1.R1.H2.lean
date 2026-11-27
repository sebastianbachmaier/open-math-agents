import OMAReductions.R_Erdos137_erdos_137_R1_H1_R1

-- Step Erdos137.erdos_137.R1.H1.R1.H2: hypothesis H2 of reduction Erdos137.erdos_137.R1.H1.R1
-- Credit: @sebastianbachmaier
-- H2 := ∀ a : ℕ, 0 < a →     ((a*(a+1)*(a+2)).Powerful ↔     (a.Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful) ∨     (4 ∣ a ∧ a.Powerful ∧ (a+1).Powerful ∧ ((a+2)/2).Powerful) ∨     (4 ∣ a+2 ∧ (a/2).Powerful ∧ (a+1).Powerful ∧ (a+2).Powerful))

namespace OMAErdos137H2

theorem pf_iff (n : ℕ) (hn : n ≠ 0) :
    n.Powerful ↔ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n := by
  constructor
  · intro h p hp hpn
    exact h p (Nat.mem_primeFactors.mpr ⟨hp, hpn, hn⟩)
  · intro h p hp
    obtain ⟨hp, hpn, -⟩ := Nat.mem_primeFactors.mp hp
    exact h p hp hpn

theorem pf_of (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) (hP : (x * y).Powerful)
    (h : ∀ p : ℕ, p.Prime → p ∣ x → ¬ p ∣ y ∨ p ^ 2 ∣ x) : x.Powerful := by
  rw [pf_iff _ hx]
  rw [pf_iff _ (Nat.mul_ne_zero hx hy)] at hP
  intro p hp hpx
  rcases h p hp hpx with h1 | h1
  · have h2 := hP p hp (Dvd.dvd.mul_right hpx y)
    have hc : Nat.Coprime (p ^ 2) y :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr h1)
    exact hc.dvd_of_dvd_mul_right h2
  · exact h1

theorem pf_mul (x y : ℕ) (hx : x.Powerful) (hy : y.Powerful) : (x * y).Powerful := by
  rcases Nat.eq_zero_or_pos x with h0 | hx0
  · subst h0; simpa using Nat.Full.zero_right 2
  rcases Nat.eq_zero_or_pos y with h0 | hy0
  · subst h0; simpa using Nat.Full.zero_right 2
  rw [pf_iff _ (by positivity)]
  rw [pf_iff _ (by omega)] at hx
  rw [pf_iff _ (by omega)] at hy
  intro p hp hpd
  rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
  · exact Dvd.dvd.mul_right (hx p hp h) y
  · exact Dvd.dvd.mul_left (hy p hp h) x

theorem pf_mul_of (x y : ℕ) (hx : x.Powerful) (hx0 : x ≠ 0) (hy0 : y ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ y → p ∣ x) : (x * y).Powerful := by
  rw [pf_iff _ (Nat.mul_ne_zero hx0 hy0)]
  rw [pf_iff _ hx0] at hx
  intro p hp hpd
  rcases (Nat.Prime.dvd_mul hp).mp hpd with h1 | h1
  · exact Dvd.dvd.mul_right (hx p hp h1) y
  · exact Dvd.dvd.mul_right (hx p hp (h p hp h1)) y

theorem two_of (p : ℕ) (hp : p.Prime) (h : p ∣ 2) : p = 2 :=
  (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h

theorem dvd_sub' {p m n : ℕ} (h1 : p ∣ m) (h2 : p ∣ n) (hmn : m ≤ n) : p ∣ n - m :=
  Nat.dvd_sub h2 h1

theorem not_both (p a k : ℕ) (hp : p.Prime) (hk : k ∣ 2) (hk2 : p ≠ 2 ∨ k = 1)
    (h1 : p ∣ a) (h2 : p ∣ a + k) : False := by
  have : p ∣ k := by
    have := Nat.dvd_sub h2 h1
    simpa using this
  rcases hk2 with h | h
  · have hk' : k = 1 ∨ k = 2 := by
      have := Nat.le_of_dvd (by norm_num) hk
      interval_cases k <;> simp_all
    rcases hk' with rfl | rfl
    · exact hp.one_lt.ne' (Nat.dvd_one.mp this)
    · exact h (two_of p hp this)
  · subst h; exact hp.one_lt.ne' (Nat.dvd_one.mp this)

end OMAErdos137H2

open OMAErdos137H2 in
theorem OMA.solution : OMA.R_Erdos137_erdos_137_R1_H1_R1.H2 := by
  intro a ha
  constructor
  · intro hP
    -- a+1 is powerful
    have hmid : (a + 1).Powerful := by
      have e : a * (a + 1) * (a + 2) = (a + 1) * (a * (a + 2)) := by ring
      rw [e] at hP
      refine pf_of _ _ (by omega) (by positivity) hP ?_
      intro p hp hpx
      left
      intro hy
      rcases (Nat.Prime.dvd_mul hp).mp hy with h | h
      · exact not_both p a 1 hp (one_dvd 2) (Or.inr rfl) h hpx
      · exact not_both p (a + 1) 1 hp (one_dvd 2) (Or.inr rfl) hpx h
    rcases Nat.even_or_odd a with he | ho
    · obtain ⟨c, hc⟩ := he
      rcases Nat.even_or_odd c with hce | hco
      · -- 4 ∣ a
        obtain ⟨d, hd⟩ := hce
        right; left
        have h4 : 4 ∣ a := ⟨d, by omega⟩
        have hb : (a + 2) / 2 = 2 * d + 1 := by omega
        refine ⟨h4, ?_, hmid, ?_⟩
        · have e : a * (a + 1) * (a + 2) = a * ((a + 1) * (a + 2)) := by ring
          rw [e] at hP
          refine pf_of _ _ (by omega) (by positivity) hP ?_
          intro p hp hpx
          by_cases hp2 : p = 2
          · right; subst hp2; simpa using h4
          · left
            intro hy
            rcases (Nat.Prime.dvd_mul hp).mp hy with h | h
            · exact not_both p a 1 hp (one_dvd 2) (Or.inr rfl) hpx h
            · exact not_both p a 2 hp (dvd_refl 2) (Or.inl hp2) hpx h
        · rw [hb]
          have e : a * (a + 1) * (a + 2) = (2 * d + 1) * (a * (a + 1) * 2) := by
            rw [show a + 2 = 2 * (2 * d + 1) by omega]; ring
          rw [e] at hP
          refine pf_of _ _ (by omega) (by positivity) hP ?_
          intro p hp hpx
          left
          have hp2 : p ≠ 2 := by
            rintro rfl; omega
          intro hy
          rcases (Nat.Prime.dvd_mul hp).mp hy with h | h
          · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
            · exact not_both p a 2 hp (dvd_refl 2) (Or.inl hp2) h
                (by rw [show a + 2 = 2 * (2 * d + 1) by omega]; exact Dvd.dvd.mul_left hpx 2)
            · exact not_both p (a + 1) 1 hp (one_dvd 2) (Or.inr rfl) h
                (by rw [show a + 1 + 1 = 2 * (2 * d + 1) by omega]; exact Dvd.dvd.mul_left hpx 2)
          · exact hp2 (two_of p hp h)
      · -- a ≡ 2 mod 4
        obtain ⟨d, hd⟩ := hco
        right; right
        have h4 : 4 ∣ a + 2 := ⟨d + 1, by omega⟩
        have hb : a / 2 = 2 * d + 1 := by omega
        refine ⟨h4, ?_, hmid, ?_⟩
        · rw [hb]
          have e : a * (a + 1) * (a + 2) = (2 * d + 1) * ((a + 1) * (a + 2) * 2) := by
            rw [show a = 2 * (2 * d + 1) by omega]; ring
          rw [e] at hP
          refine pf_of _ _ (by omega) (by positivity) hP ?_
          intro p hp hpx
          left
          have hp2 : p ≠ 2 := by
            rintro rfl; omega
          have hpa : p ∣ a := by
            rw [show a = 2 * (2 * d + 1) by omega]; exact Dvd.dvd.mul_left hpx 2
          intro hy
          rcases (Nat.Prime.dvd_mul hp).mp hy with h | h
          · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
            · exact not_both p a 1 hp (one_dvd 2) (Or.inr rfl) hpa h
            · exact not_both p a 2 hp (dvd_refl 2) (Or.inl hp2) hpa h
          · exact hp2 (two_of p hp h)
        · have e : a * (a + 1) * (a + 2) = (a + 2) * (a * (a + 1)) := by ring
          rw [e] at hP
          refine pf_of _ _ (by omega) (by positivity) hP ?_
          intro p hp hpx
          by_cases hp2 : p = 2
          · right; subst hp2; simpa using h4
          · left
            intro hy
            rcases (Nat.Prime.dvd_mul hp).mp hy with h | h
            · exact not_both p a 2 hp (dvd_refl 2) (Or.inl hp2) h hpx
            · exact not_both p (a + 1) 1 hp (one_dvd 2) (Or.inr rfl) h (by simpa [add_assoc] using hpx)
    · -- a odd
      left
      have hno2 : ∀ p : ℕ, p.Prime → p ∣ a → p ≠ 2 := by
        rintro p hp hpa rfl
        obtain ⟨c, hc⟩ := ho; omega
      have hno2' : ∀ p : ℕ, p.Prime → p ∣ a + 2 → p ≠ 2 := by
        rintro p hp hpa rfl
        obtain ⟨c, hc⟩ := ho; omega
      refine ⟨?_, hmid, ?_⟩
      · have e : a * (a + 1) * (a + 2) = a * ((a + 1) * (a + 2)) := by ring
        rw [e] at hP
        refine pf_of _ _ (by omega) (by positivity) hP ?_
        intro p hp hpx
        left
        intro hy
        rcases (Nat.Prime.dvd_mul hp).mp hy with h | h
        · exact not_both p a 1 hp (one_dvd 2) (Or.inr rfl) hpx h
        · exact not_both p a 2 hp (dvd_refl 2) (Or.inl (hno2 p hp hpx)) hpx h
      · have e : a * (a + 1) * (a + 2) = (a + 2) * (a * (a + 1)) := by ring
        rw [e] at hP
        refine pf_of _ _ (by omega) (by positivity) hP ?_
        intro p hp hpx
        left
        intro hy
        rcases (Nat.Prime.dvd_mul hp).mp hy with h | h
        · exact not_both p a 2 hp (dvd_refl 2) (Or.inl (hno2' p hp hpx)) h hpx
        · exact not_both p (a + 1) 1 hp (one_dvd 2) (Or.inr rfl) h (by simpa [add_assoc] using hpx)
  · rintro (⟨h1, h2, h3⟩ | ⟨h4, h1, h2, h3⟩ | ⟨h4, h1, h2, h3⟩)
    · exact pf_mul _ _ (pf_mul _ _ h1 h2) h3
    · obtain ⟨d, hd⟩ := h4
      have e : a * (a + 1) * (a + 2) = (a * 2) * ((a + 1) * ((a + 2) / 2)) := by
        rw [show (a + 2) / 2 = 2 * d + 1 by omega, show a + 2 = 2 * (2 * d + 1) by omega]; ring
      rw [e]
      refine pf_mul _ _ ?_ (pf_mul _ _ h2 h3)
      refine pf_mul_of _ _ h1 (by omega) (by norm_num) ?_
      intro p hp hp2
      rw [two_of p hp hp2]
      exact ⟨2 * d, by omega⟩
    · obtain ⟨d, hd⟩ := h4
      have e : a * (a + 1) * (a + 2) = ((a + 2) * 2) * ((a + 1) * (a / 2)) := by
        rw [show a / 2 = 2 * d - 1 by omega, show a = 2 * (2 * d - 1) by omega]
        rw [show 2 * (2 * d - 1) + 2 = 4 * d by omega]
        rw [show 2 * (2 * d - 1) + 1 = 4 * d - 1 by omega]
        ring
      rw [e]
      refine pf_mul _ _ ?_ (pf_mul _ _ h2 h1)
      refine pf_mul_of _ _ h3 (by omega) (by norm_num) ?_
      intro p hp hp2
      rw [two_of p hp hp2]
      exact ⟨2 * d, by omega⟩
