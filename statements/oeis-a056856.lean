import Mathlib

/-!
# A056856: Triangle of numbers related to rooted trees and unrooted planar trees.

Source: https://oeis.org/A056856
Credit: @Solfanbtc

`T(n, k)`, `n ≥ 1`, `1 ≤ k ≤ n` (offset 1): `1; 1, 2; 2, 9, 9; 6, 44, 96, 64; ...`. The values
are taken from the entry's row formula (Peter Bala; the entry's Maple program):
`∑_{k} T(n, k) y^{k-1} = ∏_{j=1}^{n-1} (j + n y)`.

A130534 is the triangle `A(m, i)`, `0 ≤ i ≤ m` (offset 0), of coefficients of
`(x+1)(x+2)...(x+m) = ∑_i A(m, i) xⁱ` (unsigned Stirling numbers `|s(m+1, i+1)|`).

Conjecture (R. J. Mathar, Mar 31 2023, in the entry): `T(n, k) = A130534(n, k) · n^{k-1}`.

Minimal fix of the indexing: with A130534 at its own offset 0 the formula fails at once
(`T(3, 1) = 2`, but `A130534(3, 1) · 3⁰ = 11`). It matches the data when A130534 is read with
1-based indices like A056856, i.e. `T(n, k) = A(n-1, k-1) · n^{k-1}`; this is the form stated.
A python3 check: the product formula reproduces all 36 data terms, and the shifted identity holds
for all `1 ≤ k ≤ n < 30`.

Conventions: polynomials over `ℕ`; `T n k = coeff (k-1)` of `∏_{j=1}^{n-1} (j + n X)` and
`A m i = coeff i` of `∏_{j=1}^{m} (X + j)`.
-/

namespace OMA.S_oeis_a056856

open Polynomial

/-- `T(n, k) = A056856(n, k)`: coefficient of `y^{k-1}` in `∏_{j=1}^{n-1} (j + n y)`. -/
noncomputable def T (n k : ℕ) : ℕ :=
  (∏ j ∈ Finset.Icc 1 (n - 1), (C (j : ℕ) + C n * X)).coeff (k - 1)

/-- `A(m, i) = A130534(m, i)`: coefficient of `xⁱ` in `(x+1)(x+2)...(x+m)`. -/
noncomputable def A (m i : ℕ) : ℕ := (∏ j ∈ Finset.Icc 1 m, (X + C (j : ℕ))).coeff i

/-- Mathar's conjecture, with A130534 read 1-based: `T(n, k) = A130534(n-1, k-1) · n^{k-1}`. -/
theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n → T n k = A (n - 1) (k - 1) * n ^ (k - 1) := by
  sorry

end OMA.S_oeis_a056856
