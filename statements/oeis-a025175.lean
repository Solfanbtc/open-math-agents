import Mathlib

/-!
# A025175: Jacobi polynomial P((1, 1), n, (1/2)).

Source: https://oeis.org/A025175
Credit: @Solfanbtc

The terms `1, 4, 3, -40, -190, -168, 2023, ...` (offset 0) are `4^n * P_n^(1,1)(1/2)`, where
`P_n^(α,β)` is the Jacobi polynomial (the scaling `4^n` makes the values integers; e.g.
`P_1^(1,1)(1/2) = 1` while `a(1) = 4`). We use the standard explicit formula
`P_n^(α,β)(x) = Sum_{s=0..n} binomial(n+α, n-s) * binomial(n+β, s) * ((x-1)/2)^s * ((x+1)/2)^(n-s)`
with `α = β = 1`, `x = 1/2`; in python3 this reproduces all 22 listed terms.

Conjecture (R. J. Mathar, Mar 03 2013):
`(n+2) a(n) + 6 (-n-1) a(n-1) + 12 (2n+1) a(n-2) + 32 (-n+1) a(n-3) = 0`.
It involves `a(n-3)` and the offset is 0, so it is stated for `n ≥ 3` (checked for `3 ≤ n < 300`).
-/

namespace OMA.S_oeis_a025175

/-- The Jacobi polynomial `P_n^(1,1)` evaluated at `x`. -/
def jacobi11 (n : ℕ) (x : ℚ) : ℚ :=
  ∑ s ∈ Finset.range (n + 1),
    ((n + 1).choose (n - s) : ℚ) * ((n + 1).choose s : ℚ) * ((x - 1) / 2) ^ s * ((x + 1) / 2) ^ (n - s)

/-- A025175(n) = `4^n * P_n^(1,1)(1/2)`. -/
def a (n : ℕ) : ℚ := 4 ^ n * jacobi11 n (1 / 2)

/-- Mathar's recurrence for A025175. -/
theorem main :
    ∀ n : ℕ, 3 ≤ n →
      ((n : ℚ) + 2) * a n + 6 * (-(n : ℚ) - 1) * a (n - 1) + 12 * (2 * (n : ℚ) + 1) * a (n - 2)
        + 32 * (-(n : ℚ) + 1) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a025175
