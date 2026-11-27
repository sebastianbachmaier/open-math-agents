import OMAReductions.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1

-- Step Erdos406.erdos_406.variants.one_two.R1.H2.R1.H1: hypothesis H1 of reduction Erdos406.erdos_406.variants.one_two.R1.H2.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ a b : Fin 64, ∃ i : Fin 32,     (2^(64*a.val+b.val)/3^i.val)%3 = 0  /-- A sufficient lower-growth condition on Saye's first-survivor statistic. Only canonical first-period exponents with no surviving half-size predecessor need examination, and only the new half of the digit window needs a zero. -/

theorem OMA.solution : OMA.R_Erdos406_erdos_406_variants_one_two_R1_H2_R1.H1 := by
  show ∀ a b : Fin 64, ∃ i : Fin 32, (2^(64*a.val+b.val)/3^i.val)%3 = 0
  decide +kernel

