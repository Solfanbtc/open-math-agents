import Mathlib

/-!
# A026733: a(n) = Sum_{k=0..floor(n/2)} T(n,k), T given by A026725.

Source: https://oeis.org/A026733
Credit: @Solfanbtc

Conjecture (R. J. Mathar, Oct 26 2019, OEIS A026733): for n >= 7 (offset 0, so that a(n-7) is a
term),
  (-n+2) a(n) + (n-2) a(n-1) + 2(4n-13) a(n-2) + 8(-n+4) a(n-3) + 5(-3n+14) a(n-4)
  + (15n-94) a(n-5) + 2(-2n+9) a(n-6) + 4(n-6) a(n-7) = 0.

T is the triangle A026725, as defined in its name: T(n, 0) = T(n, n) = 1; for n >= 2 and
1 <= k <= n-1, T(n, k) = T(n-1, k-1) + T(n-2, k-1) + T(n-1, k) if n is odd and k = (n-1)/2,
otherwise T(n, k) = T(n-1, k-1) + T(n-1, k) (and T(n, k) = 0 for k > n, outside the triangle).
Checked numerically: the rows 1; 1 1; 1 2 1; 1 4 3 1; ... of A026725 and all 31 listed terms of
A026733 are reproduced, and the recurrence holds for 7 <= n < 200.
-/

namespace OMA.S_oeis_a026733

/-- The triangle A026725. -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k ≤ 1 then 1 else 0
  | n + 2, k =>
    if k = 0 ∨ k = n + 2 then 1
    else if n + 2 < k then 0
    else if Odd (n + 2) ∧ k = (n + 1) / 2 then T (n + 1) (k - 1) + T n (k - 1) + T (n + 1) k
    else T (n + 1) (k - 1) + T (n + 1) k

/-- a(n) = Σ_{k=0..⌊n/2⌋} T(n, k). -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n / 2 + 1), T n k

theorem main : ∀ n : ℕ, 7 ≤ n →
    (-(n : ℤ) + 2) * a n + ((n : ℤ) - 2) * a (n - 1) + 2 * (4 * (n : ℤ) - 13) * a (n - 2)
      + 8 * (-(n : ℤ) + 4) * a (n - 3) + 5 * (-3 * (n : ℤ) + 14) * a (n - 4)
      + (15 * (n : ℤ) - 94) * a (n - 5) + 2 * (-2 * (n : ℤ) + 9) * a (n - 6)
      + 4 * ((n : ℤ) - 6) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a026733
