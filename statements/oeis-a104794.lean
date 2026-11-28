import Mathlib

/-!
# A104794: Sum_{k ≥ 0} a(k) e^{-kπ} = √π √2 / (2 Γ(3/4)^2) for the coefficients of θ_4(q)^2

Source: https://oeis.org/A104794
Credit: @Solfanbtc

A104794 (offset 0): the expansion of `θ_4(q)^2` in powers of `q`, where
`θ_4(q) = Sum_{n ∈ ℤ} (-1)^n q^(n^2)`. Data 1, -4, 4, 0, 4, -8, 0, 0, 4, -4, 8, …

Conjecture (in the entry): `Sum_{k>=0} a(k) / exp(k*Pi) = (1/2)*Pi^(1/2)*sqrt(2)/Gamma(3/4)^2`
(A014549).

Remark. This looks provable from known results: the series is `θ_4(e^{-π})^2`, which converges
absolutely (`|a(k)| ≤ 4 d(k)`), and the classical value `θ_4(e^{-π}) = 2^{-1/4} π^{1/4} / Γ(3/4)`
gives the conjectured sum. The entry does not record a proof, so it is stated here as in the
source. `main` asserts convergence (`HasSum` in `ℝ`) to the stated constant.

Definitions. `θ_4` has coefficient `1` at `0`, `2 (-1)^m` at `m^2` for `m ≥ 1`, and `0` elsewhere.
Checked with python3: the coefficients of `θ_4^2` match the data, and the partial sum up to
`k = 59` agrees with `0.8346268416740…` to about `10^-15`.
-/

namespace OMA.S_oeis_a104794

open PowerSeries

/-- `θ_4(q) = Sum_{n ∈ ℤ} (-1)^n q^(n^2)` as a power series over `ℚ`. -/
noncomputable def theta4 : PowerSeries ℚ :=
  PowerSeries.mk fun k =>
    if k = 0 then 1 else if IsSquare k then 2 * (-1) ^ (Nat.sqrt k) else 0

/-- A104794: the coefficients of `θ_4(q)^2`. -/
noncomputable def a (k : ℕ) : ℚ := coeff k (theta4 ^ 2)

/-- The conjecture: `Sum_{k ≥ 0} a(k) e^{-kπ} = √π √2 / (2 Γ(3/4)^2)`. -/
theorem main :
    HasSum (fun k : ℕ => (a k : ℝ) * Real.exp (-(k * Real.pi)))
      (1 / 2 * Real.sqrt Real.pi * Real.sqrt 2 / Real.Gamma (3 / 4) ^ 2) := by
  sorry

end OMA.S_oeis_a104794
