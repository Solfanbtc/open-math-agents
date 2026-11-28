import Mathlib

/-!
# A055837: T(2n+3, n), where T is the array in A055830

Source: https://oeis.org/A055837
Credit: @Solfanbtc

A055830 is the triangle `T(n, k)` (`0 ≤ k ≤ n`, the diagonal differences of A037027), with g.f.
`(1 - y z)/(1 - y (1 + y + z))`. Below `T` is defined by the recurrence in that entry (Philippe
Deléham): `T(0, 0) = 1`, `T(1, 1) = 0`, `T(n, k) = T(n-1, k-1) + T(n-1, k) + T(n-2, k)`, with
`T(n, k) = 0` for `k < 0` or `k > n` (this gives `T(1, 0) = 1`). Python: it agrees with the g.f.
for `n < 60` and reproduces the data `1; 1, 0; 2, 1, 0; 3, 3, 1, 0; …`.

A055837 (offset 0): `a(n) = T(2n+3, n)`: `3, 15, 73, 361, 1806, …` (all 21 data terms agree).

Conjecture (R. J. Mathar, Mar 13 2016, OEIS formula):
`5n(n+2)(11n-4) a(n) + (-242n^3 - 330n^2 + 29n + 42) a(n-1) - 3(3n-1)(11n+7)(3n-2) a(n-2) = 0`,
for `n ≥ 2` (so that `a(n-2)` is a term, offset 0). Python: holds for `2 ≤ n < 40`.
-/

namespace OMA.S_oeis_a055837

/-- The triangle A055830 (zero outside `0 ≤ k ≤ n`). -/
def T : ℕ → ℕ → ℕ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 then 1 else 0
  | n + 2, k => (if k = 0 then 0 else T (n + 1) (k - 1)) + T (n + 1) k + T n k

/-- A055837: `a(n) = T(2n+3, n)`. -/
def a (n : ℕ) : ℕ := T (2 * n + 3) n

/-- Mathar's conjectured recurrence for A055837. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    5 * (n : ℤ) * (n + 2) * (11 * n - 4) * a n
      + (-242 * (n : ℤ) ^ 3 - 330 * n ^ 2 + 29 * n + 42) * a (n - 1)
      - 3 * (3 * (n : ℤ) - 1) * (11 * n + 7) * (3 * n - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a055837
