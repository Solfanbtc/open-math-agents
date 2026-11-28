import Mathlib

/-!
# A072868: Numbers k such that sigma(sigma(k) - k) = k.

Source: https://oeis.org/A072868 (see A000668, A000043)
Credit: @Solfanbtc

A072868 lists the `k` with `σ(σ(k) - k) = k`, `σ` the sum of divisors:
4, 8, 32, 128, 8192, 131072, 524288, 2147483648, ...

Conjecture (entry, formula section): `a(n) = 1 + A000668(n)`, where A000668 are the Mersenne
primes 3, 7, 31, 127, ... Both sequences are increasing, so this says that the solutions are
exactly the numbers `M + 1` with `M` a Mersenne prime (that every such `M + 1 = 2^p` is a
solution is elementary: `σ(2^p) - 2^p = 2^p - 1 = M` and `σ(M) = M + 1`).

Range: `k = 1` is excluded. There `σ(k) - k = 0`, and `σ(0)` is not defined in the OEIS
convention (Mathlib's `σ 1 0 = 0` gives `0 ≠ 1` anyway).

Sanity check (python): for `2 ≤ k ≤ 2·10^6` the solutions are exactly 4, 8, 32, 128, 8192,
131072, 524288.
-/

namespace OMA.S_oeis_a072868

/-- The sum of divisors `σ(n)`. -/
def sigma (n : ℕ) : ℕ := ArithmeticFunction.sigma 1 n

/-- The conjecture: for `k ≥ 2`, `σ(σ(k) - k) = k` iff `k - 1` is a Mersenne prime. -/
theorem main : ∀ k : ℕ, 2 ≤ k →
    (sigma (sigma k - k) = k ↔ ∃ p : ℕ, (mersenne p).Prime ∧ k = mersenne p + 1) := by
  sorry

end OMA.S_oeis_a072868
