import Mathlib

/-!
# A081204: Staircase on Pascal's triangle.

Source: https://oeis.org/A081204
Credit: @Solfanbtc

The entry gives `a(n) = binomial(ceiling(n/2) + n, n)` (offset 0); with `ceiling(n/2) = (n+1)/2`
(natural-number division) this reproduces the listed terms `1, 2, 3, 10, 15, 56, 84, 330, …`.

Conjectures (R. J. Mathar, Nov 07 2014, in the %F lines):
1. `4n(n+1)(6n^2 - 15n + 8) a(n) + 6n(9n-7) a(n-1) - 3(3n-4)(3n-2)(6n^2-3n-1) a(n-2) = 0`,
2. `8n^2(n+1) a(n) - 12n(83n^2 - 313n + 232) a(n-1) + 6(-9n^3 - 377n + 384) a(n-2)
     + 9(3n-5)(83n-64)(3n-7) a(n-3) = 0`.
The terms `a(n-2)`, resp. `a(n-3)`, must exist, so the first is stated for `n ≥ 2` and the second
for `n ≥ 3`; we write `n + 2`, resp. `n + 3`, for `n`. Both are stated together, in `ℤ`. Both
were checked numerically for all `n < 80`.
-/

namespace OMA.S_oeis_a081204

/-- A081204: `a(n) = binomial(ceiling(n/2) + n, n)`. -/
def a (n : ℕ) : ℕ := Nat.choose ((n + 1) / 2 + n) n

/-- Mathar's two conjectured recurrences. -/
theorem main :
    (∀ m : ℕ, let n : ℤ := (m : ℤ) + 2
      4 * n * (n + 1) * (6 * n ^ 2 - 15 * n + 8) * (a (m + 2) : ℤ)
        + 6 * n * (9 * n - 7) * (a (m + 1) : ℤ)
        - 3 * (3 * n - 4) * (3 * n - 2) * (6 * n ^ 2 - 3 * n - 1) * (a m : ℤ) = 0) ∧
    (∀ m : ℕ, let n : ℤ := (m : ℤ) + 3
      8 * n ^ 2 * (n + 1) * (a (m + 3) : ℤ)
        - 12 * n * (83 * n ^ 2 - 313 * n + 232) * (a (m + 2) : ℤ)
        + 6 * (-9 * n ^ 3 - 377 * n + 384) * (a (m + 1) : ℤ)
        + 9 * (3 * n - 5) * (83 * n - 64) * (3 * n - 7) * (a m : ℤ) = 0) := by
  sorry

end OMA.S_oeis_a081204
