import Mathlib

/-!
# A026389: a(n) = T(2n, n-2), T given by A026386.

Source: https://oeis.org/A026389
Credit: @Solfanbtc

a(n) = number of integer strings counted by the array T in A026386 that end at 4; also
a(n) = T(2n, n-2) (offset 2).

Conjecture (R. J. Mathar, May 29 2013, in the entry):
(n+2) a(n) + 4(-3n-2) a(n-1) + 2(24n-19) a(n-2) + 4(-18n+43) a(n-3) + 35(n-4) a(n-4) = 0.

Conventions.
* T = A026386 by its defining recurrence: T(n,0) = T(n,n) = 1; for 1 ≤ k ≤ n-1,
  T(n,k) = T(n-1,k-1) + T(n-1,k) for even n and T(n,k) = T(n-1,k-1) + T(n-1,k) + T(n-2,k-1)
  for odd n (T(n,k) = 0 for k > n). This reproduces the displayed rows of A026386.
* a(n) = T(2n, n-2) is used (the string description in the name says s(0..n), but the strings
  counted by T(2n, ·) have length 2n; the formula T(2n, n-2) is unambiguous). python3: all 22
  listed terms (n = 2..23).
* With offset 2 the recurrence involves a(n-4), so it is stated for n ≥ 6 (all indices ≥ 2);
  checked for 6 ≤ n < 80.
-/

namespace OMA.S_oeis_a026389

/-- The triangle A026386 (0 for k > n). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if n + 2 < k then 0
    else if k = 0 ∨ k = n + 2 then 1
    else T (n + 1) (k - 1) + T (n + 1) k + if (n + 2) % 2 = 1 then T n (k - 1) else 0

/-- A026389 (offset 2). -/
def a (n : ℕ) : ℕ := T (2 * n) (n - 2)

theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) + 2) * a n + 4 * (-3 * (n : ℤ) - 2) * a (n - 1) + 2 * (24 * (n : ℤ) - 19) * a (n - 2)
      + 4 * (-18 * (n : ℤ) + 43) * a (n - 3) + 35 * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026389
