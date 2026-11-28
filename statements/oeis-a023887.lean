import Mathlib

/-!
# A023887: a(n) = sigma_n(n): sum of n-th powers of divisors of n

Source: https://oeis.org/A023887
Credit: @Solfanbtc

`a(n) = σ_n(n) = ∑_{d ∣ n} d^n` (offset 1): `1, 5, 28, 273, 3126, …`.

The entry records two conjectures; both are stated here, as the two parts of `main`:
1. (Rayhan Ahmed, Jun 19 2026, OEIS comment) 5 is the only prime in this sequence: for `n ≥ 1`,
   `σ_n(n)` is prime iff `n = 2` (`a(2) = 1 + 2^2 = 5`).
2. (Velin Yanev, Aug 24 2017, OEIS formula) `σ_m(n) = σ(n^m rad(n)^(m-1)) / σ(rad(n)^(m-1))` for
   `n > 0` and `m > 0`, where `σ = σ_1` (A000203) and `rad` is the radical (A007947, the product
   of the distinct primes dividing `n`, `rad(1) = 1`). The division is stated multiplied out:
   `σ_m(n) · σ(rad(n)^(m-1)) = σ(n^m rad(n)^(m-1))` (the divisor `σ(rad(n)^(m-1)) ≥ 1`, so the
   two forms are equivalent, including exactness of the division).

Checks (Python): part 2 holds for `n < 40`, `m < 5`. For part 1, `σ_n(n)` is composite for
`n = 1` (it is `1`) and for `3 ≤ n ≤ 13`.
-/

namespace OMA.S_oeis_a023887

open ArithmeticFunction

/-- The radical of `n`: the product of the distinct primes dividing `n` (A007947). -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- A023887: `a(n) = σ_n(n)`. -/
def a (n : ℕ) : ℕ := sigma n n

/-- Ahmed's conjecture (5 is the only prime term) and Yanev's identity for `σ_m(n)`. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ((a n).Prime ↔ n = 2)) ∧
    (∀ n m : ℕ, 0 < n → 0 < m →
      sigma m n * sigma 1 (rad n ^ (m - 1)) = sigma 1 (n ^ m * rad n ^ (m - 1))) := by
  sorry

end OMA.S_oeis_a023887
