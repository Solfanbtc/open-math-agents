import Mathlib

/-!
# A026589: a(n) = T(n,n-4), T given by A026584.

Source: https://oeis.org/A026589
Credit: @Solfanbtc

a(n) = T(n, n-4), T given by A026584; also a(n) = number of integer strings s(0), ..., s(n)
counted by T such that s(n) = 4 (offset 4).

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
-(n+4)(65n-269) a(n) + (-65n^2+140n+1933) a(n-1) + (809n^2-2431n-4514) a(n-2)
  + (-123n^2+2496n-205) a(n-3) + 2(-726n^2+3737n-4395) a(n-4) + 8(56n-215)(2n-9) a(n-5) = 0.

Conventions.
* By the comment in A026584, T(n, k) is the number of integer strings s(0..n) with s(0) = 0,
  s(n) = n-k, and for i = 1..n: |s(i) - s(i-1)| ≤ 1 if s(i-1) is odd, |s(i) - s(i-1)| = 1 if
  s(i-1) is even. `count n v` is the number of such strings with s(n) = v, and a(n) = count n 4.
  Checked with python3: this reproduces all 27 listed terms (n = 4..30).
* With offset 4 the recurrence involves a(n-5), so it is stated for n ≥ 9 (all indices ≥ 4).
  Checked for 9 ≤ n < 70 (it also holds from n = 5 on with a(n) = count n 4 = 0 for n < 4).
-/

namespace OMA.S_oeis_a026589

/-- Number of strings s(0..n), s(0) = 0, with the parity-dependent step rule, ending at `v`. -/
def count : ℕ → ℤ → ℕ
  | 0, v => if v = 0 then 1 else 0
  | n + 1, v => count n (v - 1) + count n (v + 1) + if Odd v then count n v else 0

/-- A026589 (offset 4). -/
def a (n : ℕ) : ℕ := count n 4

theorem main : ∀ n : ℕ, 9 ≤ n →
    let m : ℤ := n;
    -(m + 4) * (65 * m - 269) * a n + (-65 * m ^ 2 + 140 * m + 1933) * a (n - 1)
      + (809 * m ^ 2 - 2431 * m - 4514) * a (n - 2)
      + (-123 * m ^ 2 + 2496 * m - 205) * a (n - 3)
      + 2 * (-726 * m ^ 2 + 3737 * m - 4395) * a (n - 4)
      + 8 * (56 * m - 215) * (2 * m - 9) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026589
