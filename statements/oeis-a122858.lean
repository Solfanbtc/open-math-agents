import Mathlib

/-!
# A122858: Expansion of E(k) * K(k) * (2/Pi)^2 in powers of q^2 where E(), K() are complete elliptic integrals and the nome q = exp( -Pi * K(k') / K(k)).

Source: https://oeis.org/A122858
Credit: @Solfanbtc

Conjecture (Thomas Baruchel, Jun 23 2018, %F line of A122858, also in A229616 and A282031):
`-3 A122858(n) - A229616(n) + 4 A282031(n) = 0` for all `n`.

Definitions (offset 0 for all three).
* A122858: `a(0) = 1`, `a(n) = -8 Sum_{d | n} (-1)^d d` for `n ≥ 1` (the PARI program and the
  %F line `a(n) = 8 A002129(n)`; equivalently `1 - 8 Sum_k k (-x)^k / (1 - x^k)`).
* A229616: the expansion of `(φ(-q)^3 / φ(-q^3))^2`, with Ramanujan's theta function
  `φ(q) = Sum_{m ∈ ℤ} q^(m^2)`, so `φ(-q) = 1 + 2 Sum_{m ≥ 1} (-1)^m q^(m^2)`. Formal power series
  over `ℚ`; `φ(-q^3)` has constant term 1, hence is invertible.
* A282031: the `q`-expansion of `(9 E_2(q^3) - E_2(q)) / 8` with
  `E_2(q) = 1 - 24 Sum_{n ≥ 1} σ(n) q^n`, i.e. `1` at `n = 0` and `3 σ(n) - 27 σ(n/3)` for
  `n ≥ 1` (`σ(n/3) = 0` unless `3 ∣ n`).

Checked with python3 (exact series): the three definitions reproduce the listed terms of
A122858, A229616 and A282031, and the identity holds for `0 ≤ n < 120`.
-/

namespace OMA.S_oeis_a122858

open PowerSeries

/-- A122858. -/
def A122858 (n : ℕ) : ℤ :=
  if n = 0 then 1 else -8 * ∑ d ∈ n.divisors, (-1 : ℤ) ^ d * d

/-- Coefficients of `φ(-q) = 1 + 2 Sum_{m ≥ 1} (-1)^m q^(m^2)`. -/
def phiNegCoeff (k : ℕ) : ℚ :=
  if k = 0 then 1 else if Nat.sqrt k * Nat.sqrt k = k then 2 * (-1) ^ Nat.sqrt k else 0

/-- `φ(-q)`. -/
noncomputable def phiNeg : PowerSeries ℚ := PowerSeries.mk phiNegCoeff

/-- `φ(-q^3)`. -/
noncomputable def phiNeg3 : PowerSeries ℚ :=
  PowerSeries.mk fun k => if 3 ∣ k then phiNegCoeff (k / 3) else 0

/-- A229616: coefficients of `(φ(-q)^3 / φ(-q^3))^2`. -/
noncomputable def A229616 (n : ℕ) : ℚ := coeff n ((phiNeg ^ 3 * phiNeg3⁻¹) ^ 2)

/-- `σ(m)` for natural `m`, and `σ(n/3)` read as `0` unless `3 ∣ n`. -/
def sigma1 (m : ℕ) : ℤ := (ArithmeticFunction.sigma 1 m : ℤ)

/-- A282031: coefficients of `(9 E_2(q^3) - E_2(q)) / 8`. -/
def A282031 (n : ℕ) : ℤ :=
  if n = 0 then 1 else 3 * sigma1 n - (if 3 ∣ n then 27 * sigma1 (n / 3) else 0)

/-- Baruchel's conjectured linear relation. -/
theorem main : ∀ n : ℕ, -3 * (A122858 n : ℚ) - A229616 n + 4 * (A282031 n : ℚ) = 0 := by
  sorry

end OMA.S_oeis_a122858
