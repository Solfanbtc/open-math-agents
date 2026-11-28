import Mathlib

/-!
# A004735: Denominator of average distance traveled by n-dimensional fly

Source: https://oeis.org/A004735
Credit: @Solfanbtc

A004735 (offset 1) and A004734 are the denominators and numerators of the average distance
traveled by an `n`-dimensional fly. Following the comment in both entries (Michel Marcus,
May 24 2013), that average is `d(n) = 2 n!!/(n+1)!!` for odd `n` and `d(n) = 4 n!!/((n+1)!! π)`
for even `n`, and `A004735(n)` is the denominator of `d(n)` (`n` odd) or of `π d(n)` (`n` even),
i.e. the denominator of the rational number
`q(n) = 2 n!!/(n+1)!!` (`n` odd), `q(n) = 4 n!!/(n+1)!!` (`n` even).
With this, `den q(n)` reproduces all 29 data terms `1, 3, 4, 15, 8, 35, 64, 315, …` of A004735
(and `num q(n)` all 31 data terms of A004734).

A001803 (offset 0): numerators in the expansion of `(1 - x)^(-3/2) = ∑ (2n+1) C(2n, n)/4^n x^n`
(formula in the entry, J. W. Meijer), i.e. `A001803(n) = num((2n+1) C(2n, n)/4^n)`
= `1, 3, 15, 35, 315, …` (all 23 data terms agree).

Conjecture (Ralf Stephan, Mar 10 2004, OEIS formula): `A004735(2n) = A001803(n)`, for every
`n ≥ 1` (`2n` must lie in the range `n ≥ 1` of A004735). Checked with Python for `n ≤ 13`.
-/

namespace OMA.S_oeis_a004735

/-- The rational `q(n)` whose denominator is A004735(n). -/
def q (n : ℕ) : ℚ :=
  if n % 2 = 1 then 2 * (n.doubleFactorial : ℚ) / ((n + 1).doubleFactorial : ℚ)
  else 4 * (n.doubleFactorial : ℚ) / ((n + 1).doubleFactorial : ℚ)

/-- A004735 (offset 1). -/
def A004735 (n : ℕ) : ℕ := (q n).den

/-- A001803: numerator of `(2n+1) C(2n, n) / 4^n`, the coefficient of `x^n` in `(1-x)^(-3/2)`. -/
def A001803 (n : ℕ) : ℤ := (((2 * n + 1) * (Nat.choose (2 * n) n) : ℚ) / 4 ^ n).num

/-- Stephan's conjecture: `A004735(2n) = A001803(n)` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (A004735 (2 * n) : ℤ) = A001803 n := by
  sorry

end OMA.S_oeis_a004735
