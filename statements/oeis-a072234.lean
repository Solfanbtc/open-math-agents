import Mathlib

/-!
# A072234: numbers whose digit reversal is the sum of their proper divisors are divisible by 3

Source: https://oeis.org/A072234
Credit: @Solfanbtc

A072234 lists the numbers `k` such that `reverse(k)` (A004086, the decimal digits of `k` read
backwards) equals the sum of the proper divisors of `k` (A001065). Data: 6, 498906, 20671542,
41673714, 73687923, 4158499614, 922964834547 (a(8) > 10^13).

Conjecture (Mark Ganson, in the entry): all terms are divisible by 3.

Conventions. Terms are positive (`k = 0` is excluded; `k = 1` is not a term since its proper
divisor sum is `0`). `reverse(k)` is `Nat.ofDigits 10 (Nat.digits 10 k).reverse`, so trailing
zeros of `k` become leading zeros and disappear, as for A004086. Checked with python3: the
terms below `6·10^5` are exactly 6 and 498906, and all listed terms are divisible by 3.
-/

namespace OMA.S_oeis_a072234

/-- A004086: the decimal digit reversal of `k`. -/
def reverse (k : ℕ) : ℕ := Nat.ofDigits 10 (Nat.digits 10 k).reverse

/-- Ganson's conjecture: every `k ≥ 1` whose reversal equals the sum of its proper divisors is
divisible by 3. -/
theorem main : ∀ k : ℕ, 1 ≤ k → reverse k = ∑ d ∈ k.properDivisors, d → 3 ∣ k := by
  sorry

end OMA.S_oeis_a072234
