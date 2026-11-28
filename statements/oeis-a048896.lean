import Mathlib

/-!
# A048896: a(n) = 2^(A000120(n+1) - 1), n >= 0.

Source: https://oeis.org/A048896
Credit: @Solfanbtc

Claim (Daniel Forgues, OEIS A048896 and A117972, comments, Oct 16 2011): a(n), n >= 1, are
the numerators and A117972(n), n >= 2, the denominators of the Maclaurin series of
1 - ((sin x)/x)^2, the correlation function in Montgomery's pair correlation conjecture.
This is an identity about a power series (it follows from sin(x)^2 = (1 - cos 2x)/2), not an
open problem; it is stated as the entry gives it.

Conventions:
* a(n) = 2^(A000120(n+1) - 1), where A000120(m) is the number of 1's in the binary expansion
  of m (the sum of the binary digits).
* A117972(n) is computed by its formula (from the Mathematica code of that entry): the
  numerator of f(n) = (-1)^n (2n)! / 2^(2n+1): 1, -1, 3, -45, 315, -14175, ... (equal to the
  data of A117972).
* The Maclaurin series of 1 - ((sin x)/x)^2 is formed in `ℚ⟦X⟧` from Mathlib's
  `PowerSeries.sin`: (sin x)/x is the series with coefficients [x^k] = [x^(k+1)] sin x. It has
  only even powers; "the numerators" are those of the coefficients c(n) of x^(2n) in lowest
  terms, taken up to sign (the coefficients alternate in sign: 1/3, -2/45, 1/315, ...). The
  pairing is a(n) with A117972(n+1), n ≥ 1, as the stated ranges n ≥ 1 and n ≥ 2 say:
  |num c(n)| = a(n) and den c(n) = |A117972(n+1)|. Checked in Python for 1 ≤ n < 60 (in fact
  c(n) = a(n)/A117972(n+1) exactly).
-/

namespace OMA.S_oeis_a048896

open PowerSeries

/-- A048896: `2^(A000120(n+1) - 1)`. -/
def a (n : ℕ) : ℕ := 2 ^ ((Nat.digits 2 (n + 1)).sum - 1)

/-- A117972, by its formula: the numerator of `(-1)^n (2n)! / 2^(2n+1)`. -/
def A117972 (n : ℕ) : ℤ :=
  ((-1 : ℚ) ^ n * (Nat.factorial (2 * n) : ℚ) / 2 ^ (2 * n + 1)).num

/-- The Maclaurin series of `1 - ((sin x)/x)^2` in `ℚ⟦X⟧`. -/
noncomputable def corr : PowerSeries ℚ :=
  1 - (PowerSeries.mk fun k => coeff (k + 1) (sin ℚ)) ^ 2

/-- Forgues' claim: for `n ≥ 1` the coefficient of `x^(2n)` in `1 - ((sin x)/x)^2` has
numerator `± a(n)` and denominator `|A117972(n+1)|`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (coeff (2 * n) corr).num.natAbs = a n ∧
      (coeff (2 * n) corr).den = (A117972 (n + 1)).natAbs := by
  sorry

end OMA.S_oeis_a048896
