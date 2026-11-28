import Mathlib

/-!
# A103910: Triangle T read by rows: inverse of fibonomial triangle (A010048).

Source: https://oeis.org/A103910
Credit: @Solfanbtc

A010048 is the triangle of Fibonomial coefficients
`((n, k)) = F(n) F(n-1) ⋯ F(n-k+1) / (F(k) F(k-1) ⋯ F(1))` (`0` for `k > n`). It is lower
triangular with ones on the diagonal, so it has a unique lower triangular inverse `T`, given here
(row and column indices from 0) by `T(i, i) = 1`, `T(i, j) = 0` for `i < j`, and
`T(i, j) = - ∑_{l < i} ((i, l)) T(l, j)` for `j < i` (this is `A010048 · T = I`). Rows:
`1; -1, 1; 0, -1, 1; 1, 0, -2, 1; -1, 3, 0, -3, 1; ...` (python3 reproduces all the data).

The entry states two conjectures (R. Stephan, 2005), the indices of the entry running from 1:
1. "all rows except the first add to zero";
2. "T(n+k, n) = A010048(n+k-1, k) * T(k, 1), n > 1".

Minimal fix for 2: read literally (any choice of 0- or 1-based rows and columns) it already fails
at `n = 2`, `k = 1` (`T(3, 2) = -1` with 1-based indices, while `A010048(2, 1) * T(1, 1) = 1`).
With 1-based indices the identity that holds is `T(n+k, n) = A010048(n+k-1, k) * T(k+1, 1)`
(the factor is the `(k+1)`-th entry of the first column), which with 0-based indices and `m = n - 1`
reads `T(m+k, m) = ((m+k, k)) T(k, 0)` for `m ≥ 1`. python3 checks this, and the row sums, for all
rows `< 14`.

Status: both are derived by P. Bala (in the entry, June 2026), who identifies `T` as the
generalized Riordan array `(1/E(x), x)` with respect to `P(n) = F(1) ⋯ F(n)`,
`E(x) = ∑ x^n / P(n)`: the `n`-th row polynomial is `∑_k T(k, 0) ((n, k)) x^(n-k)` and the row sums
vanish for `n > 0`.
-/

namespace OMA.S_oeis_a103910

/-- The Fibonomial coefficient `((n, k))` (A010048); it is `0` for `k > n`. -/
def fibonomial (n k : ℕ) : ℕ :=
  (∏ i ∈ Finset.range k, Nat.fib (n - i)) / ∏ i ∈ Finset.range k, Nat.fib (i + 1)

/-- The inverse `T` of the Fibonomial triangle, indices from 0. -/
def T (i j : ℕ) : ℤ :=
  if i < j then 0 else if i = j then 1 else
    -∑ l : Fin i, (fibonomial i l : ℤ) * T l j
termination_by i
decreasing_by exact l.isLt

/-- Stephan's two conjectures: every row but the first sums to zero, and (as corrected above)
`T(m+k, m) = ((m+k, k)) T(k, 0)` for `m ≥ 1` (0-based indices). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → ∑ j ∈ Finset.range (n + 1), T n j = 0) ∧
    (∀ m k : ℕ, 1 ≤ m → T (m + k) m = (fibonomial (m + k) k : ℤ) * T k 0) := by
  sorry

end OMA.S_oeis_a103910
