import Mathlib

/-!
# A117972: Numerator of zeta'(-2n), n >= 0.

Source: https://oeis.org/A117972
Credit: @Solfanbtc

Claim (Daniel Forgues, Oct 16 2011, comment in A117972): `a(n)`, `n ≥ 2`, are the denominators
of the Maclaurin series of `1 - ((sin x)/x)^2`, the correlation function in Montgomery's pair
correlation conjecture (A048896 gives the numerators).

Definitions.
* As in the entry (Mathematica program, %F line; Zabolotskii's comment explains that
  `zeta'(-2n)` itself is irrational and that the sequence is the numerator of this rational),
  `a(n) = numerator(f(n))` with `f(n) = (-1)^n (2n)! / 2^(2n+1)`:
  `1, -1, 3, -45, 315, -14175, ...`.
* The Maclaurin series of `1 - (sin x / x)^2` is taken as a formal power series over `ℚ`:
  `sin x / x = Σ_k coeff_{k+1}(sin) x^k` (Mathlib's `PowerSeries.sin`). Its coefficients are
  `0` in odd degrees and in degree `0`, so the series is `x^2/3 - 2x^4/45 + x^6/315 - ...`; its
  `n`-th nonzero term, `n ≥ 2`, is the one of degree `2n - 2` (`n = 2` gives `1/3`). The claim
  pairs `a(n)` with that coefficient.
* "Denominator": the (positive) reduced denominator, compared with `|a(n)|` since the `a(n)`
  carry the signs `(-1)^n`.

Status: a short computation. `(sin x / x)^2 = (1 - cos 2x)/(2x^2)` gives the coefficient
`(-1)^n 2^(2n-1)/(2n)! = 1/(4 f(n))` in degree `2n - 2`, and `f(n)` has 2-adic valuation
`-(s_2(n) + 1) ≤ -2`, so the reduced denominator is `|numerator(f(n))|`. It is stated as written.

Checked with python3 (exact fractions): the denominators of the degree `2n - 2` coefficients are
`3, 45, 315, 14175, 467775, ...`, equal to `|a(n)|` for `2 ≤ n ≤ 15`, and `a(n)` reproduces all
listed %S/%T/%U terms.
-/

namespace OMA.S_oeis_a117972

open PowerSeries

/-- `f(n) = (-1)^n (2n)! / 2^(2n+1)`. -/
def f (n : ℕ) : ℚ := (-1) ^ n * (2 * n).factorial / 2 ^ (2 * n + 1)

/-- A117972: the numerator of `f(n)`. -/
def a (n : ℕ) : ℤ := (f n).num

/-- The formal power series of `sin x / x` over `ℚ`. -/
noncomputable def sinc : PowerSeries ℚ := PowerSeries.mk fun k => coeff (k + 1) (sin ℚ)

/-- The Maclaurin series of `1 - (sin x / x)^2`. -/
noncomputable def corr : PowerSeries ℚ := 1 - sinc ^ 2

/-- For `n ≥ 2`, `|a(n)|` is the denominator of the degree `2n - 2` coefficient of
`1 - (sin x / x)^2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → (coeff (2 * n - 2) corr).den = (a n).natAbs := by
  sorry

end OMA.S_oeis_a117972
