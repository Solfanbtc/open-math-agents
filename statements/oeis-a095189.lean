import Mathlib

/-!
# A095189: Smallest prime formed by the digit string after decimal point of n^(1/n), or 0 if no such prime exists.

Source: https://oeis.org/A095189
Credit: @Solfanbtc

The numbers "formed by the digit string after the decimal point" of `x = n^(1/n)` are its
decimal prefixes `⌊10^k · frac(x)⌋`, `k ≥ 1` (the entry's Mathematica programs; e.g.
`7^(1/7) = 1.32046…` gives `3`, so `a(7) = 3`; `2^(1/2) = 1.41421…` gives `4, 41`, so
`a(2) = 41`). `a(n) = 0` exactly when no prefix is prime.

Conjecture (Wouter Meeussen, Jun 04 2004): `a(n)` is nonzero for all `n > 1`, i.e. for every
`n > 1` some decimal prefix `⌊10^k · frac(n^(1/n))⌋` with `k ≥ 1` is prime.
(`a(1) = 0`, since `1^(1/1) = 1` has fractional part `0`.)
-/

namespace OMA.S_oeis_a095189

/-- For every `n > 1`, some decimal prefix of the fractional part of `n^(1/n)` is prime. -/
theorem main : ∀ n : ℕ, 1 < n →
    ∃ k : ℕ, 1 ≤ k ∧ ∃ p : ℕ, p.Prime ∧
      (p : ℤ) = ⌊(10 : ℝ) ^ k * Int.fract ((n : ℝ) ^ ((1 : ℝ) / n))⌋ := by
  sorry

end OMA.S_oeis_a095189
