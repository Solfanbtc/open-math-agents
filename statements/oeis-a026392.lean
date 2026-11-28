import Mathlib

/-!
# A026392: T(n,[ n/2 ]), where T is the array in A026386.

Source: https://oeis.org/A026392
Credit: @Solfanbtc

A026386 is the triangle `T(n, k)`, `0 ≤ k ≤ n`: `T(n, 0) = T(n, n) = 1`; for `1 ≤ k ≤ n-1`,
`T(n, k) = T(n-1, k-1) + T(n-1, k)` if `n` is even, and
`T(n, k) = T(n-1, k-1) + T(n-1, k) + T(n-2, k-1)` if `n` is odd (`T = 0` outside `0 ≤ k ≤ n`, as
in R. J. Mathar's Maple program). A026392 (offset 1) is `a(n) = T(n, ⌊n/2⌋)`:
`1, 2, 4, 8, 17, 34, 75, 150, ...`.

Conjecture (R. J. Mathar, Feb 10 2015, in the entry):
`(n+1) a(n) + 2(n-1) a(n-1) + 2(-3n+1) a(n-2) + 4(-3n+7) a(n-3) + 5(n-3) a(n-4)
 + 10(n-5) a(n-5) = 0`,
stated for all `n ≥ 6` (where `a(n-5)` is in the sequence's range).

A python3 check: the definition reproduces the data of A026386 and A026392, and the recurrence
holds for all `6 ≤ n < 400`. The Lean kernel (`decide`) confirms `a 1, ..., a 12` against the
data.

Conventions:
* `tri m n k = T(n, k)` for rows `n ≤ m` (`0` beyond), built row by row; `T n k = tri n n k`.
* The recurrence is stated in `ℤ`.
-/

namespace OMA.S_oeis_a026392

/-- `tri m n k = T(n, k)` for `n ≤ m`, `0` for `n > m`. -/
def tri : ℕ → ℕ → ℕ → ℕ
  | 0 => fun n k => if n = 0 ∧ k = 0 then 1 else 0
  | m + 1 => fun n k =>
      if n ≤ m then tri m n k
      else if n = m + 1 then
        (if k = 0 ∨ k = n then 1
         else if n < k then 0
         else if n % 2 = 0 then tri m (n - 1) (k - 1) + tri m (n - 1) k
         else tri m (n - 1) (k - 1) + tri m (n - 1) k + tri m (n - 2) (k - 1))
      else 0

/-- `T n k = A026386(n, k)`. -/
def T (n k : ℕ) : ℕ := tri n n k

/-- `a n = A026392(n) = T(n, ⌊n/2⌋)`. -/
def a (n : ℕ) : ℤ := T n (n / 2)

/-- Mathar's conjectured recurrence, for all `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    ((n : ℤ) + 1) * a n + 2 * ((n : ℤ) - 1) * a (n - 1) + 2 * (-3 * (n : ℤ) + 1) * a (n - 2)
      + 4 * (-3 * (n : ℤ) + 7) * a (n - 3) + 5 * ((n : ℤ) - 3) * a (n - 4)
      + 10 * ((n : ℤ) - 5) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a026392
