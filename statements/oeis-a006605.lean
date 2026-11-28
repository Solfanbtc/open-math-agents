import Mathlib

/-!
# A006605: Number of modes of connections of 2n points.

Source: https://oeis.org/A006605
Credit: @Solfanbtc

Conjecture (OEIS A006605, formula section, R. J. Mathar, May 30 2014):
3*n*(3*n+2)*(3*n+1)*a(n) + (-275*n^3 + 475*n^2 - 328*n + 68)*a(n-1)
  + 2*(2*n-3)*(139*n^2 - 507*n + 398)*a(n-2) + 180*(2*n-5)*(n-2)*(2*n-3)*a(n-3) = 0.

Conventions:
* a(n) is given by the explicit formula of the entry (Vladimir Kruchinin, Dec 24 2010):
  a(n) = (1/(2n+1)) * Sum_{j=0..2n+1} binomial(j, 2j-2-3n) * binomial(2n+1, j), where a
  binomial coefficient with negative lower index is 0. It is computed in `ℚ`. Evaluated in
  Python, it gives 1, 1, 3, 11, 46, 207, 979, 4797, 24138, 123998, 647615, 3428493 for
  n = 0..11, matching the data (and is an integer for n < 60).
* The recurrence involves a(n-3), so it is stated for n >= 3, where all four terms are
  defined (offset 0). It holds for 3 <= n < 60 (Python check with exact arithmetic).
-/

namespace OMA.S_oeis_a006605

/-- A006605(n) by Kruchinin's formula. -/
def a (n : ℕ) : ℚ :=
  (1 / (2 * n + 1 : ℚ)) * ∑ j ∈ Finset.range (2 * n + 2),
    if 3 * n + 2 ≤ 2 * j then
      ((Nat.choose j (2 * j - 2 - 3 * n) * Nat.choose (2 * n + 1) j : ℕ) : ℚ)
    else 0

/-- Mathar's conjectured recurrence, for every `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    let m : ℚ := n
    3 * m * (3 * m + 2) * (3 * m + 1) * a n +
      (-275 * m ^ 3 + 475 * m ^ 2 - 328 * m + 68) * a (n - 1) +
      2 * (2 * m - 3) * (139 * m ^ 2 - 507 * m + 398) * a (n - 2) +
      180 * (2 * m - 5) * (m - 2) * (2 * m - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a006605
