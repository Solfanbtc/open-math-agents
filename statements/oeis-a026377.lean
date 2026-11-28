import Mathlib

/-!
# A026377: a(n) = number of integer strings s(0),...,s(n) counted by array T in A026374 that have s(n)=4; also a(n) = T(2n,n-2).

Source: https://oeis.org/A026377
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Nov 24 2012, OEIS A026377):
  n(n+4) a(n) - 3(n+2)(2n+3) a(n-1) + 5(n+2)(n+1) a(n-2) = 0.

Index convention (minimal fix). The entry has offset 2 (a(2) = 1, a(3) = 9, ...), but with that
indexing the recurrence is false (at n = 4: 32 * 58 - 3 * 6 * 11 * 9 + 5 * 6 * 5 * 1 = 224, not 0).
It holds when the terms are indexed from 0, b(m) = a(m + 2) (the convention also used in
Luschny's formula in the entry, "assuming offset 0"): m(m+4) b(m) - 3(m+2)(2m+3) b(m-1)
+ 5(m+2)(m+1) b(m-2) = 0 for m >= 2. That is what `main` states, with b(m) = a(m + 2).

Definitions. T is the triangle A026374, as defined in its name: T(n, 0) = T(n, n) = 1,
T(n, k) = T(n-1, k-1) + T(n-1, k) for odd n and 1 <= k <= n-1, and
T(n, k) = T(n-1, k-1) + T(n-1, k) + T(n-2, k-1) for even n and 1 <= k <= n-1 (T(n, k) = 0 for
k > n, never used inside the triangle). a(n) = T(2n, n-2) for n >= 2.
Checked numerically: reproduces all 24 listed terms 1, 9, 58, 330, ..., and the shifted
recurrence holds for 2 <= m < 130.
-/

namespace OMA.S_oeis_a026377

/-- The triangle A026374. -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if k = 0 ∨ k = n + 2 then 1
    else if n + 2 < k then 0
    else if Odd (n + 2) then T (n + 1) (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k + T n (k - 1)

/-- a(n) = T(2n, n - 2), for n ≥ 2. -/
def a (n : ℕ) : ℕ := T (2 * n) (n - 2)

theorem main : ∀ m : ℕ, 2 ≤ m →
    (m : ℤ) * (m + 4) * a (m + 2) - 3 * ((m : ℤ) + 2) * (2 * m + 3) * a (m + 1)
      + 5 * ((m : ℤ) + 2) * (m + 1) * a m = 0 := by
  sorry

end OMA.S_oeis_a026377
