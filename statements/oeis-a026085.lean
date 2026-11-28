import Mathlib

/-!
# A026085: Integer paths from 0 to 2, first three steps ±1, later steps in {-1, 0, 1}.

Source: https://oeis.org/A026085
Credit: @Solfanbtc

a(n) = number of (s(0), s(1), ..., s(n)) such that every s(i) is an integer, s(0) = 0,
|s(i) - s(i-1)| = 1 for i = 1,2,3; |s(i) - s(i-1)| <= 1 for i >= 4, s(n) = 2 (offset 4).

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
(n+2) a(n) + (-5n-1) a(n-1) + 4(n-4) a(n-2) + 8(n-1) a(n-3) + (-5n+34) a(n-4)
  + 3(-n+7) a(n-5) = 0.

Conventions.
* `count n v` = number of such strings s(0..n) (no sign restriction) with s(n) = v, and
  a(n) = count n 2. Checked with python3: this reproduces all 26 listed terms (n = 4..29).
* With offset 4 the recurrence involves a(n-5), so it is stated for n ≥ 9 (all indices ≥ 4);
  checked for 9 ≤ n < 80. (Using the same count below the offset, count 2 2 = 1, the identity
  would fail at n = 5 and 6, so the in-domain range is needed.)
-/

namespace OMA.S_oeis_a026085

/-- Number of admissible strings s(0..n) with s(n) = v. -/
def count : ℕ → ℤ → ℕ
  | 0, v => if v = 0 then 1 else 0
  | n + 1, v =>
    if n + 1 ≤ 3 then count n (v - 1) + count n (v + 1)
    else count n (v - 1) + count n v + count n (v + 1)

/-- A026085 (offset 4). -/
def a (n : ℕ) : ℕ := count n 2

theorem main : ∀ n : ℕ, 9 ≤ n →
    ((n : ℤ) + 2) * a n + (-5 * (n : ℤ) - 1) * a (n - 1) + 4 * ((n : ℤ) - 4) * a (n - 2)
      + 8 * ((n : ℤ) - 1) * a (n - 3) + (-5 * (n : ℤ) + 34) * a (n - 4)
      + 3 * (-(n : ℤ) + 7) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026085
