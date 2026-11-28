import Mathlib

/-!
# A025187: Mathar's recurrence for T(2n, n-1) of the array A025177

Source: https://oeis.org/A025187
Credit: @Solfanbtc

A025177: the triangular array `T(n, k)`, `0 ≤ k ≤ 2n`, of first differences in the `n,n`
direction of the trinomial array A027907, with g.f. `(1 - y z)/(1 - z(1 + y + y^2))`; so
`T(n, k) = [y^k](1 + y + y^2)^n - [y^(k-1)](1 + y + y^2)^(n-1)` (the second term is `0` when
`n = 0` or `k = 0`). Rows: [1], [1, 0, 1], [1, 1, 2, 1, 1], …
A025187 (offset 1): `a(n) = T(2n, n-1)`; data 1, 3, 16, 84, 459, 2552, …

Conjecture (R. J. Mathar, Feb 25 2015):
`12n(1573n - 2085)(3n - 1)(3n + 1) a(n)
 + (259519n^4 - 6550685n^3 + 19840883n^2 - 20466403n + 6720078) a(n-1)
 - 54(2n - 3)(63141n^3 - 343882n^2 + 645379n - 388606) a(n-2)
 - 324(n - 3)(4693n - 5417)(2n - 3)(2n - 5) a(n-3) = 0`,
stated for `n ≥ 4` (so that every index is at least the offset 1).

Checked with python3 (exact integers): the definition reproduces the 12 listed terms and the
recurrence holds for `4 ≤ n < 80`.
-/

namespace OMA.S_oeis_a025187

open Polynomial

/-- The trinomial coefficient `[y^k](1 + y + y^2)^n` (A027907). -/
noncomputable def trinom (n k : ℕ) : ℤ := ((1 + X + X ^ 2 : ℤ[X]) ^ n).coeff k

/-- A025177: `T(n, k) = trinom(n, k) - trinom(n-1, k-1)` (from the g.f.). -/
noncomputable def T (n k : ℕ) : ℤ :=
  trinom n k - if n = 0 ∨ k = 0 then 0 else trinom (n - 1) (k - 1)

/-- A025187: `a(n) = T(2n, n-1)`. -/
noncomputable def a (n : ℕ) : ℤ := T (2 * n) (n - 1)

/-- Mathar's recurrence for A025187, for `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    12 * (n : ℤ) * (1573 * n - 2085) * (3 * n - 1) * (3 * n + 1) * a n
      + (259519 * (n : ℤ) ^ 4 - 6550685 * n ^ 3 + 19840883 * n ^ 2 - 20466403 * n + 6720078)
        * a (n - 1)
      - 54 * (2 * (n : ℤ) - 3) * (63141 * n ^ 3 - 343882 * n ^ 2 + 645379 * n - 388606) * a (n - 2)
      - 324 * ((n : ℤ) - 3) * (4693 * n - 5417) * (2 * n - 3) * (2 * n - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a025187
