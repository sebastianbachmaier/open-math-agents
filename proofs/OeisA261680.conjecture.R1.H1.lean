import OMAReductions.R_OeisA261680_conjecture_R1

-- Step OeisA261680.conjecture.R1.H1: hypothesis H1 of reduction OeisA261680.conjecture.R1
-- Credit: @sebastianbachmaier
-- H1 := ∀ n ∈ Finset.range 30, 0 < a n

set_option maxRecDepth 100000 in
theorem OMA.solution : OMA.R_OeisA261680_conjecture_R1.H1 := by
  intro n hn
  have h : n < 30 := Finset.mem_range.mp hn
  interval_cases n <;> decide
