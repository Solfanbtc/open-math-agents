import Mathlib

/-!
# A113424: a(n) = (6*n)!/((3*n)!*(2*n)!*n!).

Source: https://oeis.org/A113424
Credit: @Solfanbtc

`a(n) = (6n)! / ((3n)! (2n)! n!) = C(6n, 2n) C(4n, n)`.

From Peter Bala, Feb 28 2020 (in the entry): `a(n) = [xⁿ] F(x)^{60n}`, where
`F(x) = 1 + x + 56x² + 7355x³ + 1290319x⁴ + ...` *appears to have integer coefficients*; and
*we conjecture* that for `k ≥ 1` the sequence `b_k(n) = [xⁿ] F(x)^{kn}` satisfies the
supercongruences `b_k(m pʳ) ≡ b_k(m p^{r-1}) (mod p^{3r})` for primes `p ≥ 7` and positive
integers `m`, `r`. (For `a = b_60` itself the entry states these congruences for `p ≥ 5`, via
Mestrovic's equation 39.) Both conjectural claims are stated, as a conjunction.

`F` is characterized by `[xⁿ] F^{60n} = a(n)` for all `n` and constant coefficient 1 (this
determines its coefficients one by one, since `[xⁿ] F^{60n} = 60n [xⁿ]F + (lower terms)`); the
statement quantifies over any such `F` (it exists and is unique).

A python3 check (exact rationals): `F` has the printed coefficients and integer coefficients up
to `x¹⁵`; the congruence (mod `p³`, `r = 1`) holds for `k ∈ {1, 2, 3, 5, 60}` and
`(p, m) ∈ {(7,1), (11,1), (13,1), (7,2)}`.

Conventions: series in `ℚ⟦X⟧`; a congruence between rationals `x ≡ y (mod N)` is written
`∃ z : ℤ, x - y = N * z`.
-/

namespace OMA.S_oeis_a113424

open PowerSeries

/-- `a n = (6n)! / ((3n)! (2n)! n!)`. -/
def a (n : ℕ) : ℕ := (6 * n).factorial / ((3 * n).factorial * (2 * n).factorial * n.factorial)

/-- Bala's conjectures: `F` has integer coefficients, and the supercongruences for `b_k`. -/
theorem main : ∀ F : ℚ⟦X⟧, constantCoeff F = 1 →
    (∀ n : ℕ, 1 ≤ n → coeff n (F ^ (60 * n)) = (a n : ℚ)) →
    (∀ n : ℕ, ∃ z : ℤ, coeff n F = z) ∧
    ∀ k : ℕ, 1 ≤ k → ∀ p : ℕ, p.Prime → 7 ≤ p → ∀ m r : ℕ, 1 ≤ m → 1 ≤ r →
      ∃ z : ℤ, coeff (m * p ^ r) (F ^ (k * (m * p ^ r)))
          - coeff (m * p ^ (r - 1)) (F ^ (k * (m * p ^ (r - 1)))) = (p : ℚ) ^ (3 * r) * z := by
  sorry

end OMA.S_oeis_a113424
