import Mathlib

/-!
# A065942: Central column of triangle A065941.

Source: https://oeis.org/A065942
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Jun 13 2014):
8*n*(n-1)*a(n) - 36*(n-1)*(n-3)*a(n-1) + 6*(-9*n^2+18*n-14)*a(n-2) + 27*(3*n-7)*(3*n-8)*a(n-3) = 0.

Conventions.
* A065941 is the triangle T(n,k) = binomial(n - floor((k+1)/2), floor(k/2)), 0 ≤ k ≤ n; its
  central column is a(n) = T(2n, n) = binomial(2n - floor((n+1)/2), floor(n/2)) (offset 0),
  the defining formula given in the entry. Values: 1, 1, 3, 4, 15, 21, 84, 120, 495, 715, ...
* The recurrence involves a(n-3), so it is stated for n ≥ 3 (written as n = t + 3, t : ℕ),
  over ℤ since some coefficients are negative. Checked numerically for 3 ≤ n < 60.
-/

namespace OMA.S_oeis_a065942

/-- Triangle A065941: T(n,k) = binomial(n - floor((k+1)/2), floor(k/2)). -/
def T (n k : ℕ) : ℕ := (n - (k + 1) / 2).choose (k / 2)

/-- A065942: the central column of A065941, a(n) = T(2n, n). -/
def a (n : ℕ) : ℕ := T (2 * n) n

theorem main : ∀ t : ℕ, let n : ℤ := (t : ℤ) + 3
    8 * n * (n - 1) * (a (t + 3) : ℤ) - 36 * (n - 1) * (n - 3) * (a (t + 2) : ℤ) +
      6 * (-9 * n ^ 2 + 18 * n - 14) * (a (t + 1) : ℤ) +
      27 * (3 * n - 7) * (3 * n - 8) * (a t : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a065942
