import Mathlib

/-!
# A047098: a(n) = 2*binomial(3*n, n) - Sum_{k=0..n} binomial(3*n, k).

Source: https://oeis.org/A047098
Credit: @Solfanbtc

`a(n) = 2 C(3n, n) - ∑_{k=0}^{n} C(3n, k)` (offset 0): `1, 2, 8, 38, 196, 1062, ...`.

Conjecture (R. J. Mathar, Nov 30 2012, in the entry):
`2n(2n-1) a(n) + (-71n² + 112n - 48) a(n-1) + 3(131n² - 391n + 296) a(n-2)
 - 72(3n-7)(3n-8) a(n-3) = 0`,
stated for every `n ≥ 3` (where `a(n-3)` is defined).

Status: SOLVED. The entry records (Robert Israel, Mar 13 2026) that the conjecture was verified
using the differential equation
`6x + 3 + (-144x² + 114x - 7) y + (-1296x³ + 792x² - 101x + 2) y'
 + (-648x⁴ + 393x³ - 71x² + 4x) y'' = 0` satisfied by the g.f. `y(x)`.

A python3 check: the definition reproduces the data and the recurrence holds for all
`3 ≤ n < 400`.

Conventions: the recurrence is stated in `ℤ`.
-/

namespace OMA.S_oeis_a047098

/-- `a n = 2 C(3n, n) - ∑_{k=0}^{n} C(3n, k)`. -/
def a (n : ℕ) : ℤ := 2 * ((3 * n).choose n : ℤ) - ∑ k ∈ Finset.range (n + 1), ((3 * n).choose k : ℤ)

/-- Mathar's recurrence (verified by Israel), for all `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * (n : ℤ) * (2 * n - 1) * a n + (-71 * (n : ℤ) ^ 2 + 112 * n - 48) * a (n - 1)
      + 3 * (131 * (n : ℤ) ^ 2 - 391 * n + 296) * a (n - 2)
      - 72 * (3 * (n : ℤ) - 7) * (3 * n - 8) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a047098
