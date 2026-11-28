import Mathlib

/-!
# A025183: a(n) = T(2n-1,n), where T is the array defined in A025177.

Source: https://oeis.org/A025183
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Feb 25 2015, OEIS A025183): for n >= 4 (offset 1, so that a(n-3)
is defined),
  9n(10833n - 26779)(3n - 4)(3n - 2) a(n)
  - 3(n - 1)(749757n^3 + 509641n^2 - 11324756n + 13648560) a(n-1)
  - 2(2n - 5)(4152209n^3 - 25903434n^2 + 56589136n - 40818816) a(n-2)
  - 36(n - 3)(85207n - 129510)(2n - 5)(2n - 7) a(n-3) = 0.
(The coefficients 509641 and 56589136 are split across lines in the entry.)

Definitions. A025177 is the triangle T(n, k), 0 <= k <= 2n, with g.f. (1 - yz)/(1 - z(1 + y + y^2))
(entry A025177), i.e. T(n, k) = [y^k] (1 + y + y^2)^n - [y^(k-1)] (1 + y + y^2)^(n-1) for n >= 1
(rows [1], [1, 0, 1], [1, 1, 2, 1, 1], ...). For n >= 1 both indices 2n - 1 and n are >= 1, so
a(n) = [y^n] (1 + y + y^2)^(2n-1) - [y^(n-1)] (1 + y + y^2)^(2n-2).
Checked numerically: this reproduces all 20 listed terms 0, 4, 20, 111, ..., and the recurrence
holds for 4 <= n < 60.
-/

namespace OMA.S_oeis_a025183

open Polynomial

/-- Trinomial coefficient: `[y^k] (1 + y + y^2)^n` (A027907). -/
noncomputable def trin (n k : ℕ) : ℤ := ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k

/-- a(n) = T(2n-1, n) for n ≥ 1, with T the array A025177. -/
noncomputable def a (n : ℕ) : ℤ := trin (2 * n - 1) n - trin (2 * n - 2) (n - 1)

theorem main : ∀ n : ℕ, 4 ≤ n →
    9 * (n : ℤ) * (10833 * n - 26779) * (3 * n - 4) * (3 * n - 2) * a n
      - 3 * ((n : ℤ) - 1) * (749757 * n ^ 3 + 509641 * n ^ 2 - 11324756 * n + 13648560) * a (n - 1)
      - 2 * (2 * (n : ℤ) - 5) * (4152209 * n ^ 3 - 25903434 * n ^ 2 + 56589136 * n - 40818816)
          * a (n - 2)
      - 36 * ((n : ℤ) - 3) * (85207 * n - 129510) * (2 * n - 5) * (2 * n - 7) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a025183
