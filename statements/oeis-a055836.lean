import Mathlib

/-!
# A055836: T(2n+2, n), where T is the array in A055830.

Source: https://oeis.org/A055836
Credit: @Solfanbtc

`T` is the triangle A055830 (diagonal differences of A037027), given in that entry by
`T(n, k) = 0` for `k > n` or `k < 0`, `T(0, 0) = 1`, `T(1, 1) = 0`, `T(n, 0) = F(n+1)` and
`T(n, k) = T(n-1, k-1) + T(n-1, k) + T(n-2, k)` (Philippe Deléham, as in the entry's Maple
program, which generates its data). `a(n) = T(2n+2, n)` for `n ≥ 0`: `2, 7, 31, 145, 701, ...`.

Conjecture (R. J. Mathar, Mar 13 2016, in the entry): for `n ≥ 2`,
`5 n (n+1) (7n-5) a(n) - n (154 n^2 + 2n - 77) a(n-1) - 3 (3n-4) (7n+2) (3n-2) a(n-2) = 0`.
(At `n = 1` the recurrence would involve `a(-1)`; it is stated from `n = 2`, the first index
where all terms are defined.)

A python3 check: `T` reproduces the rows of A055830 and the data of A055836, and the recurrence
holds for `2 ≤ n ≤ 299`.

Conventions: `T` on `ℕ × ℕ`; the case `k = 0` of the recurrence is the Fibonacci recurrence, so
`T(n+2, 0) = T(n+1, 0) + T(n, 0)` with `T(0, 0) = T(1, 0) = 1`, and `T(0, k+1) = T(1, k+1) = 0`.
The recurrence is stated in `ℤ`.
-/

namespace OMA.S_oeis_a055836

/-- The triangle A055830. -/
def T : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | 1, 0 => 1
  | 1, _ + 1 => 0
  | n + 2, 0 => T (n + 1) 0 + T n 0
  | n + 2, k + 1 => T (n + 1) k + T (n + 1) (k + 1) + T n (k + 1)

/-- `a n = T(2n+2, n)`. -/
def a (n : ℕ) : ℕ := T (2 * n + 2) n

/-- Mathar's conjectured P-recurrence for A055836. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    5 * (n : ℤ) * (n + 1) * (7 * n - 5) * a n - n * (154 * n ^ 2 + 2 * n - 77) * a (n - 1)
      - 3 * (3 * (n : ℤ) - 4) * (7 * n + 2) * (3 * n - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a055836
