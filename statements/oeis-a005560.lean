import Mathlib

/-!
# A005560: Number of walks on square lattice. Column y=2 of A052174

Source: https://oeis.org/A005560
Credit: @Solfanbtc

`a(n) = T(n, 2)` for `n ≥ 2` (offset 2), where `T` is the triangle A052174. We use the explicit
formula for `T` given in A052174 (Michel Marcus): with `n - y = 2k`,
`T(n, y) = C(n+1, k) C(n, k) - C(n+1, k) C(n, k-1)`, and with `n - y = 2k + 1`,
`T(n, y) = C(n+1, k) C(n, k+1) - C(n+1, k+1) C(n, k-1)`, where `C(m, j) = 0` for `j < 0`.
For `y = 2` this reproduces all 27 data terms `1, 3, 15, 45, 189, 588, …` at the OEIS offset.
(Hanna's formula in A005560 gives the same values but is indexed from 0.)

Conjecture (R. J. Mathar, Apr 02 2017, OEIS formula):
`(n-1)(n-2)(2n+1)(n+5)(n+4) a(n) - 4n(n+1)(2n^2+4n+19) a(n-1)
 - 16 n^2 (n-1)(2n+3)(n+1) a(n-2) = 0`.
Range: `n ≥ 4`, the indices for which `a(n)`, `a(n-1)`, `a(n-2)` are all terms of the sequence
(offset 2). Checked with Python for `n < 80`.
-/

namespace OMA.S_oeis_a005560

/-- Binomial coefficient with integer lower index, `0` when the lower index is negative. -/
def C (m : ℕ) (j : ℤ) : ℤ := if j < 0 then 0 else (Nat.choose m j.toNat : ℤ)

/-- A005560: `a(n) = T(n, 2)`, column `y = 2` of A052174, by Marcus's formula. -/
def a (n : ℕ) : ℤ :=
  let k : ℤ := ((n - 2 : ℕ) / 2 : ℕ)
  if (n - 2) % 2 = 0 then C (n + 1) k * C n k - C (n + 1) k * C n (k - 1)
  else C (n + 1) k * C n (k + 1) - C (n + 1) (k + 1) * C n (k - 1)

/-- Mathar's conjectured recurrence for A005560. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) - 1) * ((n : ℤ) - 2) * (2 * n + 1) * (n + 5) * (n + 4) * a n
      - 4 * n * (n + 1) * (2 * n ^ 2 + 4 * n + 19) * a (n - 1)
      - 16 * n ^ 2 * ((n : ℤ) - 1) * (2 * n + 3) * (n + 1) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a005560
