import Mathlib

/-!
# A014176: Decimal expansion of the silver mean, 1+sqrt(2).

Source: https://oeis.org/A014176
Credit: @Solfanbtc

Conjecture (in the entry's formulas): `1 + √2 = lim_{n → ∞} A179807(n+1) / A179807(n)`.
(A179807 itself states "the ratio a(n+1)/a(n) tends to 1 + sqrt(2)" without proof.)

A179807 (offset 1) is the sequence of antidiagonal sums of the triangle A175105:
`T(n, 1) = 1` (`n ≥ 1`), `T(n, k) = ∑_{i=1}^{k-1} (T(n-i, k-1) + T(n-i, k))` for `1 < k ≤ n`,
and `T(n, k) = 0` for `k > n` or `k < 1` (as in the entry's Maple and Mathematica programs).
The `m`-th antidiagonal sum is `A179807(m) = ∑_{n + k = m + 1} T(n, k)`:
`1, 1, 2, 3, 5, 9, 17, 34, 71, 153, ...`.

A python3 check: this reproduces the 32 data terms of A179807, and
`a(m+1)/a(m) = 2.41234, 2.41420, 2.4142135602, 2.4142135623728` at `m = 50, 100, 200, 300`.

Conventions:
* `tri m n k` is `T(n, k)` for rows `n ≤ m` (and `0` beyond), built row by row so that each row
  only uses earlier rows; `T n k = tri n n k`. The Lean kernel (`decide`) confirms
  `a 1, ..., a 12 = 1, 1, 2, 3, 5, 9, 17, 34, 71, 153, 337, 755`.
* `a 0 = 0` (empty sum) is irrelevant for the limit.
-/

namespace OMA.S_oeis_a014176

open Filter Topology

/-- `tri m n k = T(n, k)` for `n ≤ m`, `0` for `n > m`. -/
def tri : ℕ → ℕ → ℕ → ℕ
  | 0 => fun _ _ => 0
  | m + 1 => fun n k =>
      if n ≤ m then tri m n k
      else if n = m + 1 then
        (if k = 1 then 1
         else if n < k ∨ k < 1 then 0
         else ∑ i ∈ Finset.Icc 1 (k - 1), (tri m (n - i) (k - 1) + tri m (n - i) k))
      else 0

/-- `T n k = A175105(n, k)`. -/
def T (n k : ℕ) : ℕ := tri n n k

/-- `a m = A179807(m)`: the `m`-th antidiagonal sum `∑_{n + k = m + 1} T(n, k)`. -/
def a (m : ℕ) : ℕ := ∑ n ∈ Finset.Icc 1 m, T n (m + 1 - n)

/-- Conjecture: `A179807(n+1)/A179807(n) → 1 + √2`. -/
theorem main :
    Tendsto (fun n : ℕ => (a (n + 1) : ℝ) / (a n : ℝ)) atTop (𝓝 (1 + Real.sqrt 2)) := by
  sorry

end OMA.S_oeis_a014176
