import Mathlib

/-!
# A091258: Denominator of sigma_3(n)/sigma(n)

Source: https://oeis.org/A091258
Credit: @Solfanbtc

`a(n)` (offset 1) is the denominator of the reduced fraction `σ_3(n)/σ(n)`:
`1, 1, 1, 7, 1, 1, 1, 1, 13, …`. A004611: the positive integers divisible only by primes `≡ 1 (mod 3)`
(including `1`): `1, 7, 13, 19, 31, 37, 43, 49, …`.

Conjecture (Michel Marcus, Aug 10 2024, OEIS comment): the set of distinct terms of A091258 is
A004611. Stated as the set equality `{a(n) : n ≥ 1} = {m ≥ 1 : every prime factor of m is ≡ 1 mod 3}`.
(Python, `n ≤ 2·10^5`: every denominator is in A004611; some elements of A004611 such as `37`, `73`,
`103` do not yet occur in that range.)
-/

namespace OMA.S_oeis_a091258

open ArithmeticFunction

/-- A091258: the denominator of `σ_3(n)/σ(n)`. -/
def a (n : ℕ) : ℕ := ((sigma 3 n : ℚ) / (sigma 1 n : ℚ)).den

/-- A004611: `m ≥ 1` divisible only by primes `≡ 1 (mod 3)`. -/
def InA004611 (m : ℕ) : Prop := 1 ≤ m ∧ ∀ p ∈ m.primeFactors, p % 3 = 1

/-- The set of values of A091258 is A004611. -/
theorem main : {x : ℕ | ∃ n : ℕ, 1 ≤ n ∧ a n = x} = {m : ℕ | InA004611 m} := by
  sorry

end OMA.S_oeis_a091258
