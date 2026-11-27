import OMAStatements.S_oeis_a105403

-- Reduction oeis-a105403.R1 of A105403: Numbers n such that prime(n)-1 and prime(n+1)-1 have the same largest prime factor.
-- Credit: @sobrien032
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
Jon E. Schoenfield conjectured (OEIS A105403, July 25, 2015) that 2, 30, 53 and 217 are the only
indices n ≥ 1 for which prime(n) - 1 and prime(n + 1) - 1 have the same largest prime factor.
The statement is an equality of sets, so it splits into its two inclusions.
`H1` is the finite check that the four known terms have the property. It needs the primes
prime(2), prime(3), prime(30), prime(31), prime(53), prime(54), prime(217) and prime(218), which
are 3, 5, 113, 127, 241, 251, 1327 and 1361, and the largest prime factors of 2, 4, 112, 126,
240, 250, 1326 and 1360.
`H2` is the open part: no other index has the property.
-/

namespace OMA.R_oeis_a105403_R1

open OMA.S_oeis_a105403

def H1 : Prop :=
  ({2, 30, 53, 217} : Set ℕ) ⊆ {n : ℕ | 1 ≤ n ∧ gpf (prime n - 1) = gpf (prime (n + 1) - 1)}

def H2 : Prop :=
  {n : ℕ | 1 ≤ n ∧ gpf (prime n - 1) = gpf (prime (n + 1) - 1)} ⊆ ({2, 30, 53, 217} : Set ℕ)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a105403.main :=
  fun h1 h2 => Set.Subset.antisymm h2 h1

end OMA.R_oeis_a105403_R1
