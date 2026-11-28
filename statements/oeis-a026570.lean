import Mathlib

/-!
# A026570: a(n) = A026568(n,n-1): strings counted by A026568 with s(n) = 1.

Source: https://oeis.org/A026570
Credit: @Solfanbtc

a(n) = A026568(n, n-1) = number of integer strings s(0), ..., s(n) counted by A026568 such that
s(n) = 1 (offset 1).

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
(n+1) a(n) - 2n a(n-1) + (-3n-1) a(n-2) + 2(2n-3) a(n-3) = 0.

Conventions.
* By the comment in A026568, the strings are s(0..n) with s(0) = 0 and, for 1 ≤ i ≤ n,
  |s(i) - s(i-1)| ≤ 1 if s(i-1) is even, |s(i) - s(i-1)| = 1 if s(i-1) is odd (integers, no
  sign restriction). `count n v` counts those with s(n) = v; a(n) = count n 1. Checked with
  python3: all 29 listed terms (n = 1..29).
* With offset 1 the recurrence involves a(n-3), so it is stated for n ≥ 4 (all indices ≥ 1);
  checked for 4 ≤ n < 80.
-/

namespace OMA.S_oeis_a026570

/-- Number of admissible strings s(0..n) with s(n) = v. -/
def count : ℕ → ℤ → ℕ
  | 0, v => if v = 0 then 1 else 0
  | n + 1, v => count n (v - 1) + count n (v + 1) + if Even v then count n v else 0

/-- A026570 (offset 1). -/
def a (n : ℕ) : ℕ := count n 1

theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n - 2 * (n : ℤ) * a (n - 1) + (-3 * (n : ℤ) - 1) * a (n - 2)
      + 2 * (2 * (n : ℤ) - 3) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026570
