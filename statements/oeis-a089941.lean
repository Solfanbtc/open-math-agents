import Mathlib

/-!
# A089941: Row sums of triangle A089940.

Source: https://oeis.org/A089941
Credit: @Solfanbtc

A089940 is the triangle T(n,k) = binomial(n+k, floor((n-k)/2)), 0 ≤ k ≤ n, so
a(n) = Sum_{k=0..n} binomial(n+k, floor((n-k)/2)) (offset 0). This reproduces all 31 data terms
1, 2, 4, 9, 19, 42, ... (checked with python3 and `#eval`).

Conjecture (R. J. Mathar, Dec 10 2014):
  +n*(n+6)*(n-5)*a(n) -(n+6)*(n^2-3*n-6)*a(n-1) -2*(n+6)*(3*n^2-20*n+27)*a(n-2)
  +(n+6)*(3*n^2-19*n+36)*a(n-3) +2*(4*n-15)*(n-3)*(n+6)*a(n-4) +4*(n-3)*(n-4)*(n+6)*a(n-5) = 0.

The recurrence involves a(n-5), so it is stated for n ≥ 5 (the range where all terms are
defined with offset 0); arithmetic is in `ℤ`. Checked numerically with python3 for 5 ≤ n < 400.
-/

namespace OMA.S_oeis_a089941

/-- A089941(n) = Sum_{k=0..n} binomial(n+k, floor((n-k)/2)). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n + k).choose ((n - k) / 2)

theorem main :
    ∀ n : ℕ, 5 ≤ n →
      let m : ℤ := n
      m * (m + 6) * (m - 5) * a n - (m + 6) * (m ^ 2 - 3 * m - 6) * a (n - 1)
        - 2 * (m + 6) * (3 * m ^ 2 - 20 * m + 27) * a (n - 2)
        + (m + 6) * (3 * m ^ 2 - 19 * m + 36) * a (n - 3)
        + 2 * (4 * m - 15) * (m - 3) * (m + 6) * a (n - 4)
        + 4 * (m - 3) * (m - 4) * (m + 6) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a089941
