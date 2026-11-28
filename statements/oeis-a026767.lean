import Mathlib

/-!
# A026767: a(n) = Sum{i=0..n} Sum{j=0..n} T(i,j), T given by A026758.

Source: https://oeis.org/A026767
Credit: @Solfanbtc

A026758 is the triangle `T(n, k)`, `0 ≤ k ≤ n`: `T(n, 0) = T(n, n) = 1`; for `n ≥ 2` and
`1 ≤ k ≤ n-1`, `T(n, k) = T(n-1, k-1) + T(n-2, k-1) + T(n-1, k)` if `n` is odd and
`k ≤ (n-1)/2`, else `T(n, k) = T(n-1, k-1) + T(n-1, k)`; `T(n, k) = 0` for `k > n` (as the
entry's Maple/Mathematica recursions give). A026767 (offset 0) is
`a(n) = ∑_{i=0}^{n} ∑_{j=0}^{n} T(i, j)`: `1, 3, 7, 16, 34, 75, 157, ...`.

Conjecture (R. J. Mathar, Jun 30 2013, in the entry):
`(n+1) a(n) + (-n-3) a(n-1) + 2(-5n+4) a(n-2) + 2(5n+3) a(n-3) + (29n-83) a(n-4)
 + (-29n+61) a(n-5) + 10(-2n+11) a(n-6) + 20(n-5) a(n-7) = 0`,
stated for all `n ≥ 7` (where `a(n-7)` is defined).

A python3 check: the definition reproduces the data of A026758 and A026767, `T(i, j) = 0` for
`j > i` under the entry's recursion, and the recurrence holds for all `7 ≤ n < 250`. The Lean
kernel (`decide`) confirms `a 0, ..., a 11` against the data.

Conventions:
* `tri m n k = T(n, k)` for rows `n ≤ m` (`0` beyond and for `k > n`), built row by row;
  `T n k = tri n n k`.
* The recurrence is stated in `ℤ`.
-/

namespace OMA.S_oeis_a026767

/-- `tri m n k = T(n, k)` for `n ≤ m`, `0` for `n > m`. -/
def tri : ℕ → ℕ → ℕ → ℕ
  | 0 => fun n k => if n = 0 ∧ k = 0 then 1 else 0
  | m + 1 => fun n k =>
      if n ≤ m then tri m n k
      else if n = m + 1 then
        (if k = 0 ∨ k = n then 1
         else if n < k then 0
         else if n % 2 = 1 ∧ k ≤ (n - 1) / 2 then
           tri m (n - 1) (k - 1) + tri m (n - 2) (k - 1) + tri m (n - 1) k
         else tri m (n - 1) (k - 1) + tri m (n - 1) k)
      else 0

/-- `T n k = A026758(n, k)`. -/
def T (n k : ℕ) : ℕ := tri n n k

/-- `a n = A026767(n) = ∑_{i ≤ n} ∑_{j ≤ n} T(i, j)`. -/
def a (n : ℕ) : ℤ := ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), (T i j : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 7`. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℤ) + 1) * a n + (-(n : ℤ) - 3) * a (n - 1) + 2 * (-5 * (n : ℤ) + 4) * a (n - 2)
      + 2 * (5 * (n : ℤ) + 3) * a (n - 3) + (29 * (n : ℤ) - 83) * a (n - 4)
      + (-29 * (n : ℤ) + 61) * a (n - 5) + 10 * (-2 * (n : ℤ) + 11) * a (n - 6)
      + 20 * ((n : ℤ) - 5) * a (n - 7) = 0 := by
  sorry

end OMA.S_oeis_a026767
