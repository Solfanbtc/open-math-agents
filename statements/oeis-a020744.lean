import Mathlib

/-!
# A020744: the terms 2n + 8 are exactly the even sums of four primes

Source: https://oeis.org/A020744
Credit: @Solfanbtc

A020744 (offset 0): the Pisot sequences `P(8,10)`, `T(8,10)`; by the entry's formula
`a(n) = 2n + 8`, i.e. 8, 10, 12, 14, … We use this formula as the definition.

Conjecture (C. R. Greathouse IV, Feb 16 2012): "Conjecturally, even sums of four primes", i.e. the
terms of A020744 are exactly the even numbers that are sums of four primes. `main` states this
set equality (primes may repeat).

Remark. This follows from the ternary Goldbach theorem (Helfgott, 2013): the smallest sum of four
primes is `8 = 2 + 2 + 2 + 2`, so every even sum of four primes is a term; conversely, for even
`n ≥ 10`, `n - 3 ≥ 7` is odd, hence a sum of three primes, and `n = 3 + (n - 3)`. The entry still
labels the claim conjectural, so it is stated here as in the source.
-/

namespace OMA.S_oeis_a020744

/-- A020744: `a(n) = 2n + 8`. -/
def a (n : ℕ) : ℕ := 2 * n + 8

/-- `m` is a sum of four primes (not necessarily distinct). -/
def IsSumFourPrimes (m : ℕ) : Prop :=
  ∃ p q r s : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧ s.Prime ∧ m = p + q + r + s

/-- Greathouse's conjecture: the terms of A020744 are exactly the even sums of four primes. -/
theorem main : Set.range a = {m : ℕ | Even m ∧ IsSumFourPrimes m} := by
  sorry

end OMA.S_oeis_a020744
