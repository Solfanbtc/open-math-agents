import Mathlib

/-!
# A010767: Decimal expansion of 4th root of 2

Source: https://oeis.org/A010767
Credit: @Solfanbtc

Claim (Simon Plouffe, Sep 09 2025, OEIS formula, conjectured): the constant `2^(1/4)` equals
`∑_{k ≥ 0} A007096(k) / exp(k π)`, where A007096 (offset 0) is the expansion of
`theta_3 / theta_4`, `theta_3(q) = ∑_{n ∈ ℤ} q^(n^2)`, `theta_4(q) = ∑_{n ∈ ℤ} (-q)^(n^2)`:
`1, 4, 8, 16, 32, 56, 96, …` (the definition below, the power-series quotient, reproduces all 38
data terms of A007096).

Status: SOLVED. Peter Bala (Oct 20 2026, OEIS formula) proved it: the sum is
`eta(q^2)^6 / (eta(q)^4 eta(q^4)^2)` at `q = exp(-π)`, i.e.
`eta(i)^6 / (eta(i/2)^4 eta(2i)^2) = 2^(1/4)` from the known special values of the Dedekind eta
function; equivalently `(∑ exp(-π n^2)) / (∑ (-1)^n exp(-π n^2)) = 2^(1/4)`.
Stated here faithfully, as convergence of the series to `2^(1/4)` (`HasSum`). A numerical check
with 60 terms gives `1.189207115002721` on both sides.
-/

namespace OMA.S_oeis_a010767

open PowerSeries

/-- `r(n)`: the number of integers `m` with `m^2 = n` (the coefficient of `q^n` in `theta_3`). -/
def r (n : ℕ) : ℚ := if n = 0 then 1 else if IsSquare n then 2 else 0

/-- `theta_3(q) = ∑_{m ∈ ℤ} q^(m^2)`. -/
def theta3 : PowerSeries ℚ := PowerSeries.mk r

/-- `theta_4(q) = ∑_{m ∈ ℤ} (-q)^(m^2)`. -/
def theta4 : PowerSeries ℚ := PowerSeries.mk fun n => (-1) ^ n * r n

/-- A007096: the coefficients of `theta_3 / theta_4` (`theta_4` has constant term `1`). -/
noncomputable def A007096 (k : ℕ) : ℚ := PowerSeries.coeff k (theta3 * theta4⁻¹)

/-- Plouffe's identity (proved by Bala): `∑_{k ≥ 0} A007096(k) e^(-kπ) = 2^(1/4)`. -/
theorem main :
    HasSum (fun k : ℕ => (A007096 k : ℝ) * Real.exp (-(k * Real.pi))) ((2 : ℝ) ^ ((1 : ℝ) / 4)) := by
  sorry

end OMA.S_oeis_a010767
