import Mathlib

/-!
# A081205: Staircase on Pascal's triangle.

Source: https://oeis.org/A081205
Credit: @Solfanbtc

The entry gives `a(n) = binomial(ceiling((n+1)/2) + (n+1), n)` (offset 0); with
`ceiling((n+1)/2) = (n+2)/2` (natural-number division) this reproduces the listed terms
`1, 3, 10, 20, 70, 126, 462, 792, …`.

Conjecture (R. J. Mathar, Nov 19 2014, in the %F lines):
  `4n(n-1)(n+4)(6n^2-9n-1) a(n) + 6(n-1)(27n^2+29n+4) a(n-1)
     - 3n(3n-1)(3n+1)(6n^2+3n-4) a(n-2) = 0`.
The term `a(n-2)` must exist, so it is stated for `n ≥ 2` (we write `n + 2` for `n`), in `ℤ`.
It was checked numerically for all `2 ≤ n < 100`.
-/

namespace OMA.S_oeis_a081205

/-- A081205: `a(n) = binomial(ceiling((n+1)/2) + (n+1), n)`. -/
def a (n : ℕ) : ℕ := Nat.choose ((n + 2) / 2 + (n + 1)) n

/-- Mathar's conjectured recurrence, for `n ≥ 2`. -/
theorem main : ∀ m : ℕ, let n : ℤ := (m : ℤ) + 2
    4 * n * (n - 1) * (n + 4) * (6 * n ^ 2 - 9 * n - 1) * (a (m + 2) : ℤ)
      + 6 * (n - 1) * (27 * n ^ 2 + 29 * n + 4) * (a (m + 1) : ℤ)
      - 3 * n * (3 * n - 1) * (3 * n + 1) * (6 * n ^ 2 + 3 * n - 4) * (a m : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a081205
