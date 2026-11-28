import Mathlib

/-!
# A066852: Odd values arising in A066820.

Source: https://oeis.org/A066852
Credit: @Solfanbtc

A066820 = integers of the form phi(n^2+1)/n. Conjecture (in the entry): there are an infinite
number of odd values in A066820.

Conventions.
* n ranges over positive integers; "phi(n^2+1)/n is an integer" means n ∣ φ(n^2+1). The odd
  values are 1 (n = 1), 25, 1105, 5095, ... (the data).
* Stated: the set of odd integers v = φ(n^2+1)/n (n ≥ 1, n ∣ φ(n^2+1)) is infinite.
-/

namespace OMA.S_oeis_a066852

theorem main :
    {v : ℕ | Odd v ∧ ∃ n : ℕ, 1 ≤ n ∧ n ∣ Nat.totient (n ^ 2 + 1) ∧
      Nat.totient (n ^ 2 + 1) / n = v}.Infinite := by
  sorry

end OMA.S_oeis_a066852
