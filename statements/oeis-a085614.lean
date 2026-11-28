import Mathlib

/-!
# A085614: Mathar's recurrence for the numbers of elementary arches

Source: https://oeis.org/A085614
Credit: @Solfanbtc

A085614 (offset 1): the number of elementary arches of size `n`; data 1, 3, 16, 105, 768, 6006, …
By the entry, the g.f. is the series reversion of `x - 3x^2 + 2x^3`: `y(x) = Sum a(n) x^n` is the
power series with `y(0) = 0` and `y - 3y^2 + 2y^3 = x`. This equation determines `y` uniquely,
and we use it as the definition: `main` quantifies over every such `y` (over `ℚ`).

Conjecture (R. J. Mathar, Oct 18 2013):
`n(n-1) a(n) + (n-1)(n-2) a(n-1) - 12(3n-5)(3n-7) a(n-2) - 12(3n-8)(3n-10) a(n-3) = 0`,
stated for `n ≥ 4` (so that every index is at least the offset 1).

Checked with python3: the reversion reproduces the 11 listed terms, and the recurrence holds for
`4 ≤ n < 80`.
-/

namespace OMA.S_oeis_a085614

open PowerSeries

/-- Mathar's recurrence for the coefficients of the reversion of `x - 3x^2 + 2x^3`. -/
theorem main : ∀ y : PowerSeries ℚ, constantCoeff y = 0 → y - 3 * y ^ 2 + 2 * y ^ 3 = X →
    ∀ n : ℕ, 4 ≤ n →
      (n : ℚ) * (n - 1) * coeff n y + ((n : ℚ) - 1) * (n - 2) * coeff (n - 1) y
        - 12 * (3 * (n : ℚ) - 5) * (3 * n - 7) * coeff (n - 2) y
        - 12 * (3 * (n : ℚ) - 8) * (3 * n - 10) * coeff (n - 3) y = 0 := by
  sorry

end OMA.S_oeis_a085614
