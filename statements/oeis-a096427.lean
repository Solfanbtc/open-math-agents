import Mathlib

/-!
# A096427: Decimal expansion of 1/(sqrt(2)*G), where G is Gauss's constant A014549.

Source: https://oeis.org/A096427
Credit: @Solfanbtc

Conjecture (Simon Plouffe, OEIS A096427, %F, Sep 09 2025): C = 1/(sqrt(2)*G) equals
Sum_{k>=0} A004403(k) / exp(k*Pi), where A004403 is the expansion of 1/theta_3(q)^2.
Status: this follows from Bala's formula C = 1/(Sum_{n in Z} exp(-Pi n^2))^2 = 1/theta_3(e^-Pi)^2
(listed in the entry without the word conjecture), provided the q-expansion of 1/theta_3(q)^2
converges at q = e^-Pi. It is stated here as recorded in the entry.

Not restated: Bala's conjecture C = (1/sqrt(2)) / (Sum_{n in Z} exp(-Pi (n+1/2)^2))^2 (which,
per a comment of Eric W. Weisstein, follows from the Jacobi imaginary transformation) is,
multiplied by sqrt(2), the first part of `statements/oeis-a053004.lean`, since
sqrt(2) * C = AGM(1, sqrt(2)).

Conventions:
* Gauss's constant is G = 1/AGM(1, sqrt(2)) (A014549), so C = AGM(1, sqrt(2))/sqrt(2), with
  Mathlib's `NNReal.agm`.
* theta_3(q) = Sum_{n in Z} q^(n^2) = 1 + 2 Sum_{r>=1} q^(r^2) as a formal power series over ℚ;
  A004403(k) is the coefficient of q^k in its inverse squared (1, -4, 12, -32, 76, ...).
* "Equals Sum_{k>=0}" is stated with `HasSum` (the series converges absolutely).
* Checked in Python: A004403(0..13) reproduces the data of A004403, and the partial sum up to
  k = 59 equals AGM(1, sqrt(2))/sqrt(2) = 0.847213084793979086606499123482... to 49 digits.
-/

namespace OMA.S_oeis_a096427

/-- `θ₃(q) = 1 + 2 ∑_{r ≥ 1} q^{r²}` as a formal power series over `ℚ`. -/
def theta3 : PowerSeries ℚ :=
  PowerSeries.mk fun m => if m = 0 then 1 else if Nat.sqrt m * Nat.sqrt m = m then 2 else 0

/-- A004403: coefficients of `1/θ₃(q)²`. -/
noncomputable def A004403 (k : ℕ) : ℚ := PowerSeries.coeff k ((theta3⁻¹) ^ 2)

/-- The constant `C = 1/(√2 G) = AGM(1, √2)/√2`. -/
noncomputable def C : ℝ := (NNReal.agm 1 (NNReal.sqrt 2) : ℝ) / Real.sqrt 2

/-- Plouffe's conjecture: `C = ∑_{k ≥ 0} A004403(k) / e^{kπ}`. -/
theorem main : HasSum (fun k : ℕ => (A004403 k : ℝ) / Real.exp (k * Real.pi)) C := by
  sorry

end OMA.S_oeis_a096427
