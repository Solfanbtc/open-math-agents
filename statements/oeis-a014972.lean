import Mathlib

/-!
# A014972: Expansion of (theta_3(q) / theta_4(q))^4 in powers of q; also of 1 / (1 - lambda(z)).

Source: https://oeis.org/A014972
Credit: @Solfanbtc

Conjecture (Simon Plouffe, OEIS A014972, formula section, Sep 09 2025):
Sum_{k>=0} a(k) / exp(k*Pi) = 2.

Conventions:
* theta_3(q) = Sum_{n ∈ ℤ} q^(n^2) and theta_4(q) = Sum_{n ∈ ℤ} (-1)^n q^(n^2), as formal power
  series over ℚ: the coefficient of q^m is the number of n ∈ ℤ with n^2 = m (resp. the sum of
  (-1)^n over them), and every such n satisfies |n| ≤ m. theta_4 has constant term 1, so it is
  invertible, and a(k) is the coefficient of q^k in (theta_3 * theta_4⁻¹)^4. Checked in Python:
  this gives all 25 listed terms of %S/%T/%U (1, 16, 128, 704, ...).
* The series Sum_k a(k) e^(-kπ) has nonnegative terms and converges (a(k) ~ e^(2π√k)/(32 k^(3/4)),
  formula section); it is stated with `HasSum`. Numerically (200 terms) it is 2 to 58 digits.
* The entry also has an "empirical" formula of Plouffe (Feb 20 2011),
  Sum_{n>=1} exp(-2π)^(n-1) (-1)^(n+1) a(n) = -16 + 12√2; it is not the conjecture stated here
  (numerically that sum is about 15.763, not -16 + 12√2 ≈ 0.971).
-/

namespace OMA.S_oeis_a014972

open PowerSeries

/-- theta_3 as a formal power series: the coefficient of `q^m` is `#{n ∈ ℤ | n^2 = m}`. -/
noncomputable def theta3 : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    (((Finset.Icc (-(m : ℤ)) m).filter fun n : ℤ => n ^ 2 = (m : ℤ)).card : ℚ)

/-- theta_4 as a formal power series: the coefficient of `q^m` is `Σ_{n ∈ ℤ, n^2 = m} (-1)^n`. -/
noncomputable def theta4 : PowerSeries ℚ :=
  PowerSeries.mk fun m =>
    ∑ n ∈ (Finset.Icc (-(m : ℤ)) m).filter (fun n : ℤ => n ^ 2 = (m : ℤ)), ((-1 : ℚ) ^ n.natAbs)

/-- A014972: the coefficients of `(theta_3(q) / theta_4(q))^4`. -/
noncomputable def a (k : ℕ) : ℚ :=
  coeff k ((theta3 * theta4⁻¹) ^ 4)

/-- Plouffe's conjecture: `Σ_{k ≥ 0} a(k) / exp(kπ) = 2`. -/
theorem main : HasSum (fun k : ℕ => (a k : ℝ) / Real.exp (k * Real.pi)) 2 := by
  sorry

end OMA.S_oeis_a014972
