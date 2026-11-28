import Mathlib

/-!
# A074359: Coefficient of q^2 in nu(n), (b, lambda) = (2, 2)

Source: https://oeis.org/A074359
Credit: @Solfanbtc

`ν(0) = 1`, `ν(1) = b`, and for `n ≥ 2`, `ν(n) = b ν(n-1) + λ (1 + q + ⋯ + q^(n-2)) ν(n-2)`, with
`(b, λ) = (2, 2)`; `a(n)` (offset 0) is the coefficient of `q^2` in `ν(n)`:
`0, 0, 0, 0, 12, 64, 280, …` (e.g. `ν(4) = 44 + 20q + 12q^2`). `ν` is defined below in `ℤ[q]`; this
reproduces all 26 data terms and `ν(5) = 120 + 80q + 64q^2 + 40q^3 + 8q^4`.

Conjecture (R. J. Mathar, Jul 22 2009, OEIS formula): the o.g.f. is
`4x^4(-3 + 2x + 8x^2 + 4x^3)/(2x^2 + 2x - 1)^3`. Stated with the denominator cleared (it is a unit
in `ℚ⟦x⟧`): `(∑ a(n) x^n)(2x^2 + 2x - 1)^3 = 4x^4(-3 + 2x + 8x^2 + 4x^3)`. (Python: the identity
holds for the coefficients of `x^0, …, x^39`.)
-/

namespace OMA.S_oeis_a074359

open Polynomial

/-- `ν(n)` with `(b, λ) = (2, 2)`. -/
noncomputable def nu : ℕ → ℤ[X]
  | 0 => 1
  | 1 => 2
  | n + 2 => 2 * nu (n + 1) + 2 * (∑ i ∈ Finset.range (n + 1), X ^ i) * nu n

/-- A074359: the coefficient of `q^2` in `ν(n)`. -/
noncomputable def a (n : ℕ) : ℤ := (nu n).coeff 2

/-- Mathar's conjectured generating function. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * (2 * PowerSeries.X ^ 2 + 2 * PowerSeries.X - 1) ^ 3 =
      4 * PowerSeries.X ^ 4 *
        (-3 + 2 * PowerSeries.X + 8 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3) := by
  sorry

end OMA.S_oeis_a074359
