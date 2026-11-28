import Mathlib

/-!
# A026732: Mathar's recurrence for the row sums of the triangle A026725

Source: https://oeis.org/A026732
Credit: @Solfanbtc

A026725: the triangle `T(n, k)`, `0 ≤ k ≤ n`, with `T(n, 0) = T(n, n) = 1`, and for `n ≥ 2`,
`1 ≤ k ≤ n - 1`: `T(n, k) = T(n-1, k-1) + T(n-2, k-1) + T(n-1, k)` if `n` is odd and
`k = (n-1)/2`, otherwise `T(n, k) = T(n-1, k-1) + T(n-1, k)`.
A026732 (offset 0): `a(n) = Sum_{k=0..n} T(n, k)`; data 1, 2, 4, 9, 18, 40, 80, 176, …

Conjecture (R. J. Mathar, Oct 26 2019):
`(-n+1) a(n) + 2 a(n-1) + 3(3n-7) a(n-2) - 10 a(n-3) + (-23n+95) a(n-4) + 6 a(n-5)
 + (11n-95) a(n-6) + 2 a(n-7) + 4(n-7) a(n-8) = 0`,
stated for `n ≥ 8` (so that every index is at least the offset 0).

Lean details. `T` is defined by recursion on the row, with value `0` outside the triangle; the
clause for row `n + 2`, column `k + 1` is the rule above for row `n + 2` (the extra term
`T(n, k)` is `T(n_row - 2, k_col - 1)`). Checked with python3: this reproduces the rows of
A026725 shown in its example, the 17 listed terms of A026732, and the recurrence for
`8 ≤ n < 120`.
-/

namespace OMA.S_oeis_a026732

/-- A026725, with `T n k = 0` for `k > n`. -/
def T : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | 1, k => if k ≤ 1 then 1 else 0
  | _ + 2, 0 => 1
  | n + 2, k + 1 =>
    if n + 2 < k + 1 then 0
    else if k + 1 = n + 2 then 1
    else T (n + 1) k + T (n + 1) (k + 1) +
      (if (n + 2) % 2 = 1 ∧ k + 1 = (n + 1) / 2 then T n k else 0)

/-- A026732: the row sums of A026725. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

/-- Mathar's recurrence for A026732, for `n ≥ 8`. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    (-(n : ℤ) + 1) * a n + 2 * a (n - 1) + 3 * (3 * (n : ℤ) - 7) * a (n - 2) - 10 * a (n - 3)
      + (-23 * (n : ℤ) + 95) * a (n - 4) + 6 * a (n - 5) + (11 * (n : ℤ) - 95) * a (n - 6)
      + 2 * a (n - 7) + 4 * ((n : ℤ) - 7) * a (n - 8) = 0 := by
  sorry

end OMA.S_oeis_a026732
