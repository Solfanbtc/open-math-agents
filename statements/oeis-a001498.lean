import Mathlib

/-!
# A001498: Triangle a(n,k) (n >= 0, 0 <= k <= n) of coefficients of Bessel polynomials y_n(x) (exponents in increasing order).

Source: https://oeis.org/A001498
Credit: @Solfanbtc

Conjecture (Sergei N. Gladkovskii, Nov 13 2013): the g.f. `Σ_{n,k} a(n,k) x^n y^k` is
`T(0)/(1-x)`, where `T(k) = 1 - x*y*(k+1)/(x*y*(k+1) - (1-x)^2/T(k+1))` (continued fraction).

Conventions.
* Bessel polynomials (Grosswald, p. 18): `y_0 = 1`, `y_1 = 1 + Y`,
  `y_(n+2) = (2n+3) Y y_(n+1) + y_n`; `a(n,k)` is the coefficient of `Y^k` in `y_n`.
* The g.f. is a power series in `x` whose coefficients are polynomials in `y`; it is taken in
  `K⟦x⟧` with `K = RatFunc ℚ` and `y = RatFunc.X`, so that `⁻¹` is the power series inverse.
* The infinite continued fraction is read as a limit of truncations: `cfT d k` is `T(k)` cut
  after `d` levels (`T = 1` at depth `0`). Every `T` has constant term `1`, every denominator
  `x y (k+1) - (1-x)^2/T` has constant term `-1`, and replacing `T(k+1)` by a series that
  agrees up to `x^m` changes `T(k)` only from `x^(m+1)` on (the numerator carries a factor
  `x`); so the truncations converge `x`-adically and coefficient `x^n` of the limit is the
  coefficient of `x^n` at depth `n + 1`. `main` states: for all `n`, the coefficient of `x^n`
  of `cfT (n+1) 0 / (1 - x)` is the row polynomial `y_n(y)`.
Checked (python3, exact rational series arithmetic): true for `n < 8`.
-/

namespace OMA.S_oeis_a001498

open Polynomial

/-- Bessel polynomials `y_n`. -/
noncomputable def bessel : ℕ → ℚ[X]
  | 0 => 1
  | 1 => 1 + X
  | n + 2 => C (2 * (n : ℚ) + 3) * X * bessel (n + 1) + bessel n

/-- The field in which the coefficients (polynomials in `y`) live. -/
abbrev K := RatFunc ℚ

/-- `x * y * (k+1)` as a power series in `x` over `K`. -/
noncomputable def u (k : ℕ) : PowerSeries K :=
  PowerSeries.C (RatFunc.X * ((k : K) + 1)) * PowerSeries.X

/-- `T(k)` truncated after `d` levels. -/
noncomputable def cfT : ℕ → ℕ → PowerSeries K
  | 0, _ => 1
  | d + 1, k => 1 - u k * (u k - (1 - PowerSeries.X) ^ 2 * (cfT d (k + 1))⁻¹)⁻¹

/-- Gladkovskii's conjecture: the g.f. of A001498 is `T(0)/(1-x)`. -/
theorem main : ∀ n : ℕ,
    PowerSeries.coeff n (cfT (n + 1) 0 * (1 - PowerSeries.X)⁻¹) =
      algebraMap ℚ[X] K (bessel n) := by
  sorry

end OMA.S_oeis_a001498
