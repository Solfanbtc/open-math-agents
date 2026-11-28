import Mathlib

/-!
# A072031: Row sums of A072030

Source: https://oeis.org/A072031
Credit: @Solfanbtc

A072030 is the array `T(n, k)` (`n, k ≥ 1`), read by antidiagonals, of the number of steps of the
simple (subtractive) Euclidean algorithm for `gcd(n, k)`: `T(a, 0) = 0`, `T(a, b) = T(b, a)`,
`T(a + b, b) = T(a, b) + 1` (e.g. `T(11, 3) = 6`). A072031 (offset 1) is its "row sums", i.e. the
sums along the antidiagonals: `a(n) = ∑_{i=1}^{n} T(i, n + 1 - i)`: `1, 4, 7, 14, 15, 28, …` (this
reproduces all 38 data terms).

Conjecture (Peter Bala, Dec 09 2014, OEIS comment): with `A(x) = ∑_{n ≥ 1} x^n/(1 - x^n)` the
Lambert series of the divisor function `τ`, `A(x)^2 = ∑_{n ≥ 2} a(n-1) x^n/(1 - x^n)`. Comparing
coefficients of `x^m` (the coefficient of `x^m` in `A(x)^2` is `∑_{k=1}^{m-1} τ(k) τ(m-k)`, and in
the right side it is `∑_{d ∣ m, d ≥ 2} a(d-1)`), this is: for every `m ≥ 1`,
`∑_{k=1}^{m-1} τ(k) τ(m-k) = ∑_{d ∣ m, d ≥ 2} a(d - 1)`, which is the form stated. (Python: holds
for `m < 300`.)
-/

namespace OMA.S_oeis_a072031

/-- Steps of the subtractive Euclidean algorithm. -/
def T : ℕ → ℕ → ℕ
  | a, b => if h : a = 0 ∨ b = 0 then 0 else if b ≤ a then T (a - b) b + 1 else T a (b - a) + 1
termination_by a b => a + b
decreasing_by all_goals omega

/-- A072031: `a(n) = ∑_{i=1}^{n} T(i, n+1-i)`. -/
def a (n : ℕ) : ℕ := ∑ i ∈ Finset.Icc 1 n, T i (n + 1 - i)

/-- Bala's conjecture: `A(x)^2 = ∑_{n ≥ 2} a(n-1) x^n/(1-x^n)`, coefficientwise. -/
theorem main : ∀ m : ℕ, 1 ≤ m →
    ∑ k ∈ Finset.Ioo 0 m, k.divisors.card * (m - k).divisors.card =
      ∑ d ∈ m.divisors.filter (2 ≤ ·), a (d - 1) := by
  sorry

end OMA.S_oeis_a072031
