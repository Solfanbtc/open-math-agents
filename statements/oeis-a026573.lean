import Mathlib

/-!
# A026573: a(n) = T(n,n-4), T given by A026568: strings counted by A026568 with s(n) = 4.

Source: https://oeis.org/A026573
Credit: @Solfanbtc

a(n) = A026568(n, n-4) = number of integer strings s(0), ..., s(n) counted by A026568 such that
s(n) = 4 (offset 4).

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
-2(n-4)(n+4) a(n) + (5n^2-5n-46) a(n-1) + (4n^2+n+18) a(n-2) + (-11n^2+24n-16) a(n-3)
  + 2(n-2)(2n-5) a(n-4) = 0.

Conventions.
* By the comment in A026568, the strings are s(0..n) with s(0) = 0 and, for 1 ≤ i ≤ n,
  |s(i) - s(i-1)| ≤ 1 if s(i-1) is even, |s(i) - s(i-1)| = 1 if s(i-1) is odd (integers, no
  sign restriction). `count n v` counts those with s(n) = v; a(n) = count n 4. Checked with
  python3: all 26 listed terms (n = 4..29). (Same string model as statements/oeis-a026570.lean.)
* With offset 4 the recurrence involves a(n-4), so it is stated for n ≥ 8 (all indices ≥ 4);
  checked for 8 ≤ n < 80 (it also holds for n = 4..7 with count n 4 = 0 for n < 4).
-/

namespace OMA.S_oeis_a026573

/-- Number of admissible strings s(0..n) with s(n) = v. -/
def count : ℕ → ℤ → ℕ
  | 0, v => if v = 0 then 1 else 0
  | n + 1, v => count n (v - 1) + count n (v + 1) + if Even v then count n v else 0

/-- A026573 (offset 4). -/
def a (n : ℕ) : ℕ := count n 4

theorem main : ∀ n : ℕ, 8 ≤ n →
    -2 * ((n : ℤ) - 4) * ((n : ℤ) + 4) * a n + (5 * (n : ℤ) ^ 2 - 5 * n - 46) * a (n - 1)
      + (4 * (n : ℤ) ^ 2 + n + 18) * a (n - 2) + (-11 * (n : ℤ) ^ 2 + 24 * n - 16) * a (n - 3)
      + 2 * ((n : ℤ) - 2) * (2 * (n : ℤ) - 5) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026573
