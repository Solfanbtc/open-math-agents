import Mathlib

/-!
# A061060: Write product of first n primes as x*y with x<y and x maximal; sequence gives value of y-x.

Source: https://oeis.org/A061060
Credit: @Solfanbtc

For `n ≥ 1` let `P(n) = p_1 p_2 ⋯ p_n` be the product of the first `n` primes. Write
`P(n) = x y` with `x < y` and `x` maximal, and let `a(n) = y - x`; `x` is the largest divisor `d`
of `P(n)` with `d^2 < P(n)` (as `x < y = P(n)/x`). Data: `1, 1, 1, 1, 13, 17, 1, 41, 157, ...`.

Conjecture (Alain Rocchelli, Nov 13 2023, in the entry):
`lim_{N → ∞} (∑_{n=1}^{N} log a(n)) / (∑_{n=1}^{N} prime(n)) = 1/e` (A068985), natural log.

A python3 check: the definition reproduces `a(1..21)` of the data. (The ratio at `N = 21` is
`≈ 0.257`, against `1/e ≈ 0.368`; the limit is not testable at this size.)

Conventions: `prime n = Nat.nth Nat.Prime (n - 1)` is the `n`-th prime (`n ≥ 1`).
-/

namespace OMA.S_oeis_a061060

open Filter Topology

/-- The `n`-th prime, `n ≥ 1`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- `P n = p_1 ⋯ p_n`. -/
noncomputable def P (n : ℕ) : ℕ := ∏ i ∈ Finset.Icc 1 n, prime i

/-- The maximal `x` with `P(n) = x y`, `x < y`: the largest divisor `d` of `P(n)` with `d^2 < P(n)`. -/
noncomputable def x (n : ℕ) : ℕ := ((P n).divisors.filter (fun d => d * d < P n)).sup id

/-- `a(n) = y - x = P(n)/x - x`. -/
noncomputable def a (n : ℕ) : ℕ := P n / x n - x n

/-- Rocchelli's conjecture: `(∑_{n ≤ N} log a(n)) / (∑_{n ≤ N} prime(n)) → 1/e`. -/
theorem main : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, Real.log (a n)) /
    (∑ n ∈ Finset.Icc 1 N, (prime n : ℝ))) atTop (𝓝 (Real.exp (-1))) := by
  sorry

end OMA.S_oeis_a061060
