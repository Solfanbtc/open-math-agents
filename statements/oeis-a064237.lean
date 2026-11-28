import Mathlib

/-!
# A064237: Numbers k such that k! + 1 is divisible by a square.

Source: https://oeis.org/A064237
Credit: @Solfanbtc

"Divisible by a square" means divisible by the square of an integer `> 1`, i.e. `k! + 1` is
not squarefree (the Maple, Mathematica and PARI programs all test squarefreeness). The listed
data are 4, 5, 7, 12, 23 (`4! + 1 = 5^2`, `5! + 1 = 11^2`, `7! + 1 = 71^2`, `13^2 ∣ 12! + 1`,
`47^2 ∣ 23! + 1`). The entry adds that 229 (`613^2 ∣ 229! + 1`) and 562 (`563^2 ∣ 562! + 1`) are
also terms.

Conjecture (F. Brunault, 2008, in the entry): "It is very likely that 229 and 562 are the next
two terms, but this has not yet been proved". Many `k! + 1` with `k ≤ 562` are not completely
factored, the smallest being `k = 103`. `main` states that the terms `≤ 562` are exactly
4, 5, 7, 12, 23, 229, 562. (python3: these are exactly the `k ≤ 562` such that `p^2 ∣ k! + 1` for
some prime `p < 20000`; Brunault checked primes `p < 10^8`.)

The other comment, that A064237 contains `p - 1` for every Wilson prime `p` (A007540, conjectured
infinite), is an immediate consequence of the definitions and is not stated here.
-/

namespace OMA.S_oeis_a064237

theorem main :
    {k : ℕ | 1 ≤ k ∧ k ≤ 562 ∧ ¬ Squarefree (k.factorial + 1)} =
      {4, 5, 7, 12, 23, 229, 562} := by
  sorry

end OMA.S_oeis_a064237
