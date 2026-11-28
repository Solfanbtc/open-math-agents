import Mathlib

/-!
# A049997: Numbers of the form Fibonacci(i)*Fibonacci(j).

Source: https://oeis.org/A049997
Credit: @Solfanbtc

Conjecture (Zhi-Wei Sun, Jan 02 2025): `Fibonacci(m) * Fibonacci(n)` with `2 < m < n` is a perfect
power only for `(m, n) = (3, 6)` (`F(3) F(6) = 2 * 8 = 16 = 4^2`). Sun reports verifying it for
`2 < m < n ≤ 900`.

Conventions: `Nat.fib` has `fib 0 = 0`, `fib 1 = fib 2 = 1`, `fib 3 = 2`, matching the OEIS
`Fibonacci(n)` (A000045). A perfect power is `y ^ k` with natural `y` and `k ≥ 2`. With `2 < m`,
`fib m * fib n ≥ 2 * 3 > 1`, so the trivial powers `0` and `1` cannot occur. The statement is an
iff: `(3, 6)` is one, and it is the only one.

Sanity check (python): for `2 < m < n < 120` the only perfect power is at `(m, n) = (3, 6)`.
-/

namespace OMA.S_oeis_a049997

/-- Sun's conjecture on perfect powers among products of two Fibonacci numbers. -/
theorem main : ∀ m n : ℕ, 2 < m → m < n →
    ((∃ y k : ℕ, 2 ≤ k ∧ Nat.fib m * Nat.fib n = y ^ k) ↔ (m = 3 ∧ n = 6)) := by
  sorry

end OMA.S_oeis_a049997
