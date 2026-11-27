import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1

-- Step CollatzConjecture.collatz_conjecture.R1.H2.R1.H2: hypothesis H2 of reduction CollatzConjecture.collatz_conjecture.R1.H2.R1

open CollatzConjecture

theorem OMA.solution : OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H2 := by
  intro n hn hmin
  by_contra hne
  rcases Nat.even_or_odd n with he | ho
  · have h1 := hmin 1
    simp only [Function.iterate_one, collatzStep, he, if_true] at h1
    omega
  · have h3 := hmin 3
    have hodd : ¬ Even n := Nat.not_even_iff_odd.mpr ho
    have hn4 : n % 4 = 1 := by
      obtain ⟨r, hr⟩ := ho
      omega
    have e1 : collatzStep n = 3 * n + 1 := by simp [collatzStep, hodd]
    have hev2 : Even (3 * n + 1) := ⟨(3 * n + 1) / 2, by omega⟩
    have e2 : collatzStep (3 * n + 1) = (3 * n + 1) / 2 := by simp [collatzStep, hev2]
    have hev3 : Even ((3 * n + 1) / 2) := ⟨(3 * n + 1) / 4, by omega⟩
    have e3 : collatzStep ((3 * n + 1) / 2) = (3 * n + 1) / 2 / 2 := by
      simp [collatzStep, hev3]
    have : collatzStep^[3] n = (3 * n + 1) / 2 / 2 := by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      rw [e1, e2, e3]
    rw [this] at h3
    omega
