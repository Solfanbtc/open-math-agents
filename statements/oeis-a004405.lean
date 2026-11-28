import Mathlib

/-!
# A004405: Sum_{k ≥ 0} a(k) e^{-kπ} = Γ(3/4)^4 / π for the coefficients of 1/θ_3(x)^4

Source: https://oeis.org/A004405
Credit: @Solfanbtc

A004405 (offset 0): the expansion of `1 / (Sum_{n=-oo..oo} x^(n^2))^4 = 1/θ_3(x)^4`.
Data 1, -8, 40, -160, 552, -1712, …

Conjecture (S. Plouffe, Sep 09 2025): `Sum_{k>=0} a(k) / exp(k*Pi) = (1/Pi)*Gamma(3/4)^4`
(A293238).

Remark. This looks provable from known results: `θ_3` has no zeros in the open unit disc (Jacobi
triple product), so the series `1/θ_3(q)^4` converges at `q = e^{-π}`, and the classical value
`θ_3(e^{-π}) = π^{1/4} / Γ(3/4)` gives the conjectured sum. The entry does not record a proof, so
it is stated here as in the source. `main` asserts that the series converges (absolutely,
`HasSum` in `ℝ`) to `Γ(3/4)^4/π`.

Definitions. `θ_3(x) = Sum_{n ∈ ℤ} x^(n^2)` has coefficient `1` at `0`, `2` at each positive
square and `0` elsewhere; its fourth power has constant term `1`, so it is invertible in `ℚ⟦X⟧`.
Checked with python3: the coefficients match the data, and the partial sum up to `k = 59` agrees
with `Γ(3/4)^4/π = 0.71777001104613…` to about `10^-15`.
-/

namespace OMA.S_oeis_a004405

open PowerSeries

/-- `θ_3(x) = Sum_{n ∈ ℤ} x^(n^2)` as a power series over `ℚ`. -/
def theta3 : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k = 0 then 1 else if IsSquare k then 2 else 0

/-- A004405: the coefficients of `1/θ_3(x)^4`. -/
noncomputable def a (k : ℕ) : ℚ := coeff k ((theta3 ^ 4)⁻¹)

/-- Plouffe's conjecture: `Sum_{k ≥ 0} a(k) e^{-kπ} = Γ(3/4)^4/π`. -/
theorem main :
    HasSum (fun k : ℕ => (a k : ℝ) * Real.exp (-(k * Real.pi)))
      (Real.Gamma (3 / 4) ^ 4 / Real.pi) := by
  sorry

end OMA.S_oeis_a004405
