import Mathlib

/-!
# A081181: Staircase on Pascal's triangle.

Source: https://oeis.org/A081181
Credit: @Solfanbtc

a(n) = binomial(floor((n + 1)/2) + (n + 1), n), n ≥ 0 (FORMULA section; data 1, 3, 6, 20, 35, ...).

Conjecture (R. J. Mathar, Oct 29 2014):
8*n*(n+3)*(1845*n-2882)*a(n) + 4*(-5097*n^3+11143*n^2+42110*n-27416)*a(n-1)
  + 6*(-16605*n^3-7272*n^2-16701*n+9490)*a(n-2) + 3*(3*n-5)*(5097*n-949)*(3*n-4)*a(n-3) = 0.

The recurrence involves a(n-3), so it is stated for n ≥ 3 (offset 0); it is stated in `ℤ`.
Checked numerically for 3 ≤ n < 400.
-/

namespace OMA.S_oeis_a081181

/-- A081181. -/
def a (n : ℕ) : ℕ := Nat.choose ((n + 1) / 2 + (n + 1)) n

theorem main : ∀ n : ℕ, 3 ≤ n →
    8 * (n : ℤ) * (n + 3) * (1845 * n - 2882) * a n
      + 4 * (-5097 * (n : ℤ) ^ 3 + 11143 * n ^ 2 + 42110 * n - 27416) * a (n - 1)
      + 6 * (-16605 * (n : ℤ) ^ 3 - 7272 * n ^ 2 - 16701 * n + 9490) * a (n - 2)
      + 3 * (3 * (n : ℤ) - 5) * (5097 * n - 949) * (3 * n - 4) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a081181
