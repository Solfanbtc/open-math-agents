import Mathlib

/-!
# A061164: a(n) = (20*n)!*n!/((10*n)!*(7*n)!*(4*n)!).

Source: https://oeis.org/A061164
Credit: @Solfanbtc

Conjecture (Peter Bala, OEIS A061164, comment, Jul 31 2026): for n >= 0,
a(n/2) = (10*n)!*(n/2)! / ((5*n)!*(7*n/2)!*(2*n)!) is an integer, where fractional factorials
are defined using the Gamma function, x! := Gamma(x + 1).

Conventions:
* Every factorial is written as `Real.Gamma (x + 1)` with `x` the real number `10n`, `n/2`,
  `5n`, `7n/2`, `2n`; for even `n` the value is the integer a(n/2), for odd `n` the factors
  `√π` of the two half-integer Gamma values cancel and the value is rational.
* "is an integer" is stated as: equal to the cast of some `m : ℤ`.
* Checked in Python with exact rational arithmetic (Gamma(k + 1/2) = (2k)! √π / (4^k k!)):
  the value is an integer for 0 ≤ n < 400; for n = 1 it is 1152.
-/

namespace OMA.S_oeis_a061164

/-- Bala's ratio `(10n)! (n/2)! / ((5n)! (7n/2)! (2n)!)`, factorials via `Gamma`. -/
noncomputable def ratio (n : ℕ) : ℝ :=
  Real.Gamma (10 * n + 1) * Real.Gamma ((n : ℝ) / 2 + 1) /
    (Real.Gamma (5 * n + 1) * Real.Gamma (7 * (n : ℝ) / 2 + 1) * Real.Gamma (2 * n + 1))

/-- Bala's conjecture: the ratio is an integer for every `n ≥ 0`. -/
theorem main : ∀ n : ℕ, ∃ m : ℤ, ratio n = m := by
  sorry

end OMA.S_oeis_a061164
