import Mathlib

/-!
# A055356: Triangle of increasing mobiles (circular rooted trees) with n nodes and k leaves.

Source: https://oeis.org/A055356
Credit: @Solfanbtc

The row polynomials `p(n, x)` (`n ≥ 1`, coefficients of row `n` in ascending powers of `x`;
`p(4, x) = 1 + 4x + 2x²`) satisfy `p(1, x) = 1` and
`p(n+1, x) = (1 + (n-1) x) p(n, x) + x p'(n, x)` (Ben Whitmore, May 12 2021; equivalently the
entry's Maple/Mathematica programs, which generate the data). These recurrences are used as the
definition of the rows: `1; 1; 1 + x; 1 + 4x + 2x²; 1 + 11x + 18x² + 6x³; ...`.

Conjecture (Mikhail Kurkov, Apr 11 2025, in the entry): the row polynomials are `R(n-2, 0)` for
`n > 1`, where `R(0, k) = 1` for `k ≥ 0` and, for `n > 0`, `k ≥ 0`,
`R(n, k) = R(n-1, k+1) + x ∑_{i=0}^{n-1} ∑_{j=0}^{k} C(n-1, i) R(n-i-1, j) R(i, k-j)`.

A python3 check (exact polynomial arithmetic): `p(n, x) = R(n-2, 0)` for all `2 ≤ n ≤ 13`.

Conventions:
* Polynomials over `ℕ`. `row m = p(m + 1, x)`, so the claim is `row m = R(m - 1, 0)` for `m ≥ 1`.
* `Rs M n k = R(n, k)` for `n ≤ M` (`0` beyond), built by recursion on `M`, since `R(n, ·)` uses
  `R(m, ·)` for all `m < n`; `R n k = Rs n n k`.
-/

namespace OMA.S_oeis_a055356

open Polynomial

/-- `row m = p(m + 1, x)`: `row 0 = 1`, `row (m+1) = (1 + m x) row m + x row m'`. -/
noncomputable def row : ℕ → ℕ[X]
  | 0 => 1
  | m + 1 => (1 + C m * X) * row m + X * derivative (row m)

/-- `Rs M n k = R(n, k)` for `n ≤ M`. -/
noncomputable def Rs : ℕ → ℕ → ℕ → ℕ[X]
  | 0 => fun n _ => if n = 0 then 1 else 0
  | M + 1 => fun n k =>
      if n ≤ M then Rs M n k
      else if n = M + 1 then
        Rs M M (k + 1) + X * ∑ i ∈ Finset.range (M + 1), ∑ j ∈ Finset.range (k + 1),
          C (M.choose i) * Rs M (M - i) j * Rs M i (k - j)
      else 0

/-- Kurkov's `R(n, k)`. -/
noncomputable def R (n k : ℕ) : ℕ[X] := Rs n n k

/-- Kurkov's conjecture: the row polynomials of A055356 are `R(n-2, 0)` for `n > 1`. -/
theorem main : ∀ m : ℕ, 1 ≤ m → row m = R (m - 1) 0 := by
  sorry

end OMA.S_oeis_a055356
