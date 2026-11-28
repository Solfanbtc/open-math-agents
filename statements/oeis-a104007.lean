import Mathlib

/-!
# A104007: Denominators of coefficients in expansion of x^2*(1-exp(-2*x))^(-2).

Source: https://oeis.org/A104007
Credit: @Solfanbtc

`a(m)` (offset 0) is the denominator of the coefficient of `x^m` in
`x^2 (1 - e^{-2x})^{-2} = (x / (1 - e^{-2x}))^2`. In Lean, `(1 - e^{-2x})/x` is the power series
`f = Σ_{k ≥ 0} -(-2)^{k+1}/(k+1)! x^k` (constant term 2, so invertible over `ℚ`), and the
expansion is `(f⁻¹)^2`.

Claim (T. D. Grant, Sep 24 2016, OEIS %C): it appears that `a(2n+2) = A002432(n)`, where
`A002432(n)` is the denominator of `ζ(2n)/π^(2n)`. By A002432 %F,
`ζ(2n)/π^(2n) = (-1)^(n-1) B_{2n} 2^(2n-1)/(2n)!`, which also gives `ζ(0) = -1/2` at `n = 0`.

Index fix: with the OEIS offset 0 the identity fails as written. `a(2) = 12` but `A002432(0) = 2`,
`a(4) = 60` but `A002432(1) = 6`. It holds for the odd-indexed terms: `a(1) = 2, a(3) = 6,
a(5) = 90, a(7) = 945, a(9) = 9450, ...`. So the comment uses 1-based positions, as in
Mathematica's `CoefficientList`, and the intended claim is `a(2n+1) = A002432(n)`, stated
here. Checked with exact rational arithmetic in Python for `n ≤ 13`. A. Mitin (Aug 16 2020)
indicates that this follows from the Bernoulli-number expansion.
-/

namespace OMA.S_oeis_a104007

open PowerSeries

/-- `(1 - e^{-2x}) / x` as a power series over `ℚ`. -/
noncomputable def f : PowerSeries ℚ :=
  PowerSeries.mk fun k => -(-2 : ℚ) ^ (k + 1) / (k + 1).factorial

/-- A104007(m): the denominator of `[x^m] x^2 (1 - e^{-2x})^{-2}`. -/
noncomputable def a (m : ℕ) : ℕ := (coeff m (f⁻¹ ^ 2)).den

/-- `ζ(2n)/π^(2n) = (-1)^(n-1) B_{2n} 2^(2n-1)/(2n)!` (Mathlib's `bernoulli`). -/
def zetaOverPiPow (n : ℕ) : ℚ :=
  (-1) ^ (n + 1) * bernoulli (2 * n) * 2 ^ (2 * n) / (2 * (2 * n).factorial)

theorem main : ∀ n : ℕ, a (2 * n + 1) = (zetaOverPiPow n).den := by
  sorry

end OMA.S_oeis_a104007
