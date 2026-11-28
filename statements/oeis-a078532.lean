import Mathlib

/-!
# A078532: power series with A(x)^3 - 9x A(x)^4 = 1

Source: https://oeis.org/A078532
Credit: @Solfanbtc

A078532 is the coefficient sequence of the power series `A` with `A(0) = 1` and
`A(x)^3 - 9x A(x)^4 = 1`: 1, 3, 27, 315, 4158, 59049, ... (`a(2) = 3^3`, `a(5) = 3^10`).

Conjecture (entry comment): "If A(x) = Sum_{k>=1} a(k)x^k satisfies A(x)^n - (n^2)*x*A(x)^(n+1) = 1,
then a(n-1) = n^(2n-3) and a(2n-1) = n^(4n-2)". (The sum must start at `k = 0` with `a(0) = A(0) = 1`,
as for A078532 itself; with `A(0) = 0` the equation has no solution.) For every `n ≥ 1` there
is exactly one power series `A` with constant term 1 satisfying the equation (each coefficient
is determined by the previous ones), so we state the claim for every such `A`. For `n = 1`
(Catalan numbers) the first claim reads `a(0) = 1^(-1) = 1`; we use integer exponents in `ℚ`.

Status: Emeric Deutsch (Dec 10 2002) gives `a(k) = n^(2k) binomial(k/n + 1/n + k - 1, k)/(k + 1)`
"and, consequently, a(n-1) = n^(2n-3) and a(2n-1) = n^(4n-2)"; we state the conjecture
faithfully nevertheless.

Sanity check (python, exact rationals): solving the equation coefficient by coefficient, both
identities hold for `n = 1, ..., 7`, and `n = 3` gives the listed terms.
-/

namespace OMA.S_oeis_a078532

open PowerSeries

/-- The conjecture, for every `n ≥ 1` and the power series `A` with `A(0) = 1` and
`A^n - n^2 x A^(n+1) = 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ A : PowerSeries ℚ, constantCoeff A = 1 →
    A ^ n - (n : PowerSeries ℚ) ^ 2 * X * A ^ (n + 1) = 1 →
    coeff (n - 1) A = (n : ℚ) ^ ((2 * n : ℤ) - 3) ∧
    coeff (2 * n - 1) A = (n : ℚ) ^ (4 * n - 2) := by
  sorry

end OMA.S_oeis_a078532
