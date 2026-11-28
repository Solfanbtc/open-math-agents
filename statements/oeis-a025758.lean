import Mathlib

/-!
# A025758: Mathar's recurrence for the 5th-order Vatalan numbers

Source: https://oeis.org/A025758
Credit: @Solfanbtc

A025758 (offset 0): the 5th-order Vatalan numbers, with g.f. `5 / (4 + (1 - 25x)^(1/5))`.
Data 1, 1, 11, 171, 3056, 58916, …

Conjecture (R. J. Mathar, Jul 28 2014):
`41n(n-1)(n-2)(n-3) a(n) - 3(1367n - 4100)(n-1)(n-2)(n-3) a(n-1)
 + 50(n-2)(n-3)(3077n^2 - 21533n + 38136) a(n-2)
 - 250(n-3)(10265n^3 - 123135n^2 + 494446n - 664572) a(n-3)
 + 1875(8575n^4 - 154250n^3 + 1039765n^2 - 3112730n + 3491808) a(n-4)
 - 625(5n - 22)(5n - 21)(5n - 24)(5n - 23) a(n-5) = 0`,
stated for `n ≥ 5` (so that every index is at least the offset 0).

Definitions. `(1 - 25x)^(1/5) = Sum_n binomial(1/5, n) (-25)^n x^n` in `ℚ⟦X⟧` (generalized
binomial coefficients, `Ring.choose`); `4 + (1 - 25x)^(1/5)` has constant term `5`, so it is
invertible. Checked with python3 (exact rationals): the g.f. reproduces the 10 listed terms, and
the recurrence holds for `5 ≤ n < 80`.
-/

namespace OMA.S_oeis_a025758

open PowerSeries

/-- `(1 - 25x)^(1/5)` as a power series over `ℚ`. -/
noncomputable def fifthRoot : PowerSeries ℚ :=
  PowerSeries.mk fun n => Ring.choose (1 / 5 : ℚ) n * (-25) ^ n

/-- A025758: the coefficients of `5 / (4 + (1 - 25x)^(1/5))`. -/
noncomputable def a (n : ℕ) : ℚ := coeff n (5 * (4 + fifthRoot)⁻¹)

/-- Mathar's recurrence for A025758, for `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    41 * (n : ℚ) * (n - 1) * (n - 2) * (n - 3) * a n
      - 3 * (1367 * (n : ℚ) - 4100) * (n - 1) * (n - 2) * (n - 3) * a (n - 1)
      + 50 * ((n : ℚ) - 2) * (n - 3) * (3077 * n ^ 2 - 21533 * n + 38136) * a (n - 2)
      - 250 * ((n : ℚ) - 3) * (10265 * n ^ 3 - 123135 * n ^ 2 + 494446 * n - 664572) * a (n - 3)
      + 1875 * (8575 * (n : ℚ) ^ 4 - 154250 * n ^ 3 + 1039765 * n ^ 2 - 3112730 * n + 3491808)
        * a (n - 4)
      - 625 * (5 * (n : ℚ) - 22) * (5 * n - 21) * (5 * n - 24) * (5 * n - 23) * a (n - 5)
      = 0 := by
  sorry

end OMA.S_oeis_a025758
