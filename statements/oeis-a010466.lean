import Mathlib

/-!
# A010466: Decimal expansion of square root of 8.

Source: https://oeis.org/A010466
Credit: @Solfanbtc

Conjecture (Simon Plouffe, Sep 09 2025), recorded twice:
* in A010466: "Equals `∑_{k ≥ 0} A210067(k) / exp(kπ)`" (i.e. equals the constant `√8`);
* in A210067 ("Empirical"): `∑_{n ≥ 0} A210067(n) / exp(nπ) = (2 - √2)·√2 = A010466`.
A210067 is the expansion of `(φ(-q) / φ(q²))²` in powers of `q`, with `φ(q) = ∑_{m ∈ ℤ} q^{m²}`
the Ramanujan theta function: `1, -4, 0, 16, 0, -56, 0, 160, ...` (offset 0).

The two readings differ: `(2 - √2)√2 = 2√2 - 2 = 0.8284...`, while `√8 = 2.8284...`; they have the
same decimal digits after the integer part (which is why A010466, a decimal expansion, is cited).
A python3 computation (exact coefficients, 50-digit arithmetic, 200 terms) gives the sum
`0.82842712474619009760337744841939615713934375075...`, which agrees with `(2 - √2)√2` to 49
digits and is NOT `√8`. So the claim is stated with the precise value written in A210067,
`(2 - √2)·√2`; the literal "equals √8" of A010466 is off by exactly 2.

Conventions:
* `r(n) = #{m ∈ ℤ : m² = n}` (`1` for `n = 0`, `2` for a positive square, else `0`), so
  `φ(-q) = ∑ (-1)ⁿ r(n) qⁿ` and `φ(q²) = ∑ r(n) q^{2n}`. The quotient is taken in `ℚ⟦X⟧`
  (`φ(q²)` has constant coefficient 1). The python3 computation with these definitions
  reproduces the data of A210067.
* The coefficients grow subexponentially, so the series converges absolutely at `q = e^{-π}` and
  the sum is an honest `HasSum`.
-/

namespace OMA.S_oeis_a010466

open PowerSeries

/-- `r(n) = #{m ∈ ℤ : m² = n}`. -/
def r (n : ℕ) : ℕ := if n = 0 then 1 else if Nat.sqrt n * Nat.sqrt n = n then 2 else 0

/-- `φ(-q)`. -/
noncomputable def phiNeg : ℚ⟦X⟧ := mk fun n => (-1 : ℚ) ^ n * r n

/-- `φ(q²)`. -/
noncomputable def phiSq : ℚ⟦X⟧ := mk fun n => if Even n then (r (n / 2) : ℚ) else 0

/-- `A210067(n)`: coefficients of `(φ(-q) / φ(q²))²`. -/
noncomputable def A210067 (n : ℕ) : ℚ := coeff n ((phiNeg * phiSq⁻¹) ^ 2)

/-- Plouffe's conjecture: `∑_{n ≥ 0} A210067(n) / exp(nπ) = (2 - √2)·√2`. -/
theorem main :
    HasSum (fun n : ℕ => (A210067 n : ℝ) / Real.exp (n * Real.pi))
      ((2 - Real.sqrt 2) * Real.sqrt 2) := by
  sorry

end OMA.S_oeis_a010466
