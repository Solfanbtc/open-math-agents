import Mathlib

/-!
# A099617: Denominators of the coefficients in the Taylor expansion of sec(x) + tan(x) around x=0.

Source: https://oeis.org/A099617
Credit: @Solfanbtc

Over `ℚ`, `sec x + tan x = (1 + sin x) / cos x` and `1/(1 + sin x)` are formal power series (the
constant terms of `cos x` and `1 + sin x` are 1, so they are invertible). `c n` is the coefficient
of `x^n` in `sec x + tan x`: 1, 1, 1/2, 1/3, 5/24, 2/15, 61/720, ... (`= A000111(n)/n!`).
`a(n) = den (c n)` is A099617 (offset 0). `d n` is the coefficient of `x^n` in `1/(1 + sin x)`.

Conjecture (P. Hadjicostas, 2019, as corrected by J. Yuen, 2026): for `n ≥ 0`, `a(n+1)/(n+1)` is
the denominator of the `n`-th coefficient of the Taylor expansion of `1/(1 + sin x)` around 0.
`main` states this in multiplicative form: `(n + 1) · den (d n) = a(n + 1)`, which also says that
`n + 1` divides `a(n+1)`. (Since `(sec x + tan x)' = 1/(1 - sin x)`, `d n = ± (n+1) c (n+1)`,
so the conjecture says that `n + 1` is coprime to the reduced numerator of `c (n+1)`. python3,
with the Euler zigzag numbers: true for `0 ≤ n < 399`.)
-/

namespace OMA.S_oeis_a099617

open PowerSeries

/-- Coefficients of `sec x + tan x = (1 + sin x) / cos x`. -/
noncomputable def c (n : ℕ) : ℚ := coeff n ((1 + sin ℚ) * (cos ℚ)⁻¹)

/-- Coefficients of `1 / (1 + sin x)`. -/
noncomputable def d (n : ℕ) : ℚ := coeff n ((1 + sin ℚ)⁻¹)

/-- A099617(n): the denominator of the `n`-th coefficient of `sec x + tan x`. -/
noncomputable def a (n : ℕ) : ℕ := (c n).den

theorem main : ∀ n : ℕ, (n + 1) * (d n).den = a (n + 1) := by
  sorry

end OMA.S_oeis_a099617
