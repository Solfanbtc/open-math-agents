import Mathlib

/-!
# A079006: Expansion of `q^(-1/4) (eta(q) eta(q^4)^2 / eta(q^2)^3)^2` in powers of `q`

Source: https://oeis.org/A079006
Credit: @Solfanbtc

Ramanujan theta functions: `phi(q) = ∑_{k ∈ ℤ} q^(k^2)`, `psi(q) = ∑_{k ≥ 0} q^(k(k+1)/2)`.
The three sequences, each defined by a theta-quotient expression given in its entry (all as
formal power series over `ℚ`, the denominators having constant term `1`):
* A079006 (offset 0): expansion of `psi(x^2) / phi(x)` (OEIS formula, equal to the eta quotient
  of the name): `1, -2, 5, -10, 18, …` (all 38 data terms agree);
* A208933 (offset 0): expansion of `phi(q^4) / phi(-q)`: `1, 2, 4, 8, 16, 28, …` (41 terms agree);
* A215348 (offset 1): expansion of `q phi(q) psi(q^8) / (phi(-q) phi(q^4))`:
  `1, 4, 8, 16, 30, …` for `q^1, q^2, …` (40 terms agree).

Conjecture (Thomas Baruchel, May 14 2018, OEIS formula):
`a(n) = A208933(4n+1) - A215348(4n+1)` for all `n ≥ 0`. (Python: holds for `n < 99`.)
-/

namespace OMA.S_oeis_a079006

open PowerSeries

/-- Coefficient of `q^n` in `phi(q)`: the number of `k ∈ ℤ` with `k^2 = n`. -/
def phiC (n : ℕ) : ℚ := if n = 0 then 1 else if IsSquare n then 2 else 0

/-- Coefficient of `q^n` in `psi(q)`: `1` if `n` is a triangular number `k(k+1)/2`, else `0`. -/
def psiC (n : ℕ) : ℚ :=
  if ((Finset.range (n + 1)).filter fun k => k * (k + 1) / 2 = n) ≠ ∅ then 1 else 0

/-- `phi(s q^m)` for `s = ±1`. -/
def phi (m : ℕ) (s : ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if m ∣ n then s ^ n * phiC (n / m) else 0

/-- `psi(q^m)`. -/
def psi (m : ℕ) : PowerSeries ℚ := PowerSeries.mk fun n => if m ∣ n then psiC (n / m) else 0

/-- A079006: coefficients of `psi(x^2) / phi(x)`. -/
noncomputable def A079006 (n : ℕ) : ℚ := coeff n (psi 2 * (phi 1 1)⁻¹)

/-- A208933: coefficients of `phi(q^4) / phi(-q)`. -/
noncomputable def A208933 (n : ℕ) : ℚ := coeff n (phi 4 1 * (phi 1 (-1))⁻¹)

/-- A215348: coefficients of `q phi(q) psi(q^8) / (phi(-q) phi(q^4))`. -/
noncomputable def A215348 (n : ℕ) : ℚ :=
  coeff n (X * phi 1 1 * psi 8 * (phi 1 (-1) * phi 4 1)⁻¹)

/-- Baruchel's conjecture: `A079006(n) = A208933(4n+1) - A215348(4n+1)`. -/
theorem main : ∀ n : ℕ, A079006 n = A208933 (4 * n + 1) - A215348 (4 * n + 1) := by
  sorry

end OMA.S_oeis_a079006
