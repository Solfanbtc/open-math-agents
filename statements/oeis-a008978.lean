import Mathlib

/-!
# A008978: a(n) = (5*n)!/(n!)^5.

Source: https://oeis.org/A008978
Credit: @Solfanbtc

`a(n) = (5n)! / (n!)^5`: `1, 120, 113400, ...`.

Conjecture (Peter Bala, Sep 19 2025, in the entry's formulas):
* the series `E(x) = exp(∑_{n ≥ 1} (1/120) a(n) xⁿ / n) = 1 + x + 473x² + 467606x³ + ...` has
  integer coefficients;
* for every positive integer `r`, with `u(n) = [xⁿ] E(x)^{rn}` and `v(n) = [xⁿ] F(x)^{rn}`, the
  supercongruences `u(m pᵏ) ≡ u(m p^{k-1}) (mod p^{3k})` and `v(m pᵏ) ≡ v(m p^{k-1})
  (mod p^{3k})` hold for all primes `p ≥ 5` and positive integers `m`, `k`.
Here `F(x) = 1 + x + 353x² + 318986x³ + ...` is the series of Bala's Jul 12 2016 formula,
characterized by `a(n) = [xⁿ] F(x)^{120n}` for all `n` (the coefficients of `F` are determined
one by one by this, since `[xⁿ] F^{120n} = 120n · [xⁿ]F + (terms in lower coefficients)`).

Not included: Bala's separate Jul 2016 observation that `F` appears to have integer
coefficients, and the Beukers–Vlasenko Dwork-crystal congruence (Conjecture 7.5 of "Dwork
crystals III", via the canonical coordinate and the excellent Frobenius lift), which needs
infrastructure beyond a faithful elementary statement.

A python3 check (exact rationals): `E` and `F` have the printed coefficients, the coefficients of
`E` are integers up to `x⁵¹`, and the supercongruences hold for `r = 1, 2, 3` and
`(p, m, k) ∈ {(5,1,1), (7,1,1), (5,2,1), (11,1,1)}` (also `(5,1,2)` for `u`).

Conventions:
* Series are in `ℚ⟦X⟧`; `E = exp(G)` is `(PowerSeries.exp ℚ).subst G` with
  `G = ∑_{n ≥ 1} a(n) xⁿ / (120 n)` (zero constant term).
* `F` is given by hypothesis: any `F` with constant coefficient `1` and `[xⁿ] F^{120n} = a(n)` for
  all `n ≥ 1` (it exists and is unique).
* A congruence `x ≡ y (mod N)` between the rational numbers `u(·)`, `v(·)` is written
  `∃ z : ℤ, x - y = N * z`.
-/

namespace OMA.S_oeis_a008978

open PowerSeries

/-- `a n = (5n)! / (n!)^5`. -/
def a (n : ℕ) : ℕ := (5 * n).factorial / (n.factorial) ^ 5

/-- `G = ∑_{n ≥ 1} a(n) xⁿ / (120 n)`. -/
noncomputable def G : ℚ⟦X⟧ := mk fun n => if n = 0 then 0 else (a n : ℚ) / (120 * n)

/-- `E = exp(G)`. -/
noncomputable def E : ℚ⟦X⟧ := (exp ℚ).subst G

/-- Bala's conjecture (Sep 19 2025): `E` has integer coefficients, and the supercongruences for
`u(n) = [xⁿ] E^{rn}` and `v(n) = [xⁿ] F^{rn}`. -/
theorem main : ∀ F : ℚ⟦X⟧, constantCoeff F = 1 →
    (∀ n : ℕ, 1 ≤ n → coeff n (F ^ (120 * n)) = (a n : ℚ)) →
    (∀ n : ℕ, ∃ z : ℤ, coeff n E = z) ∧
    ∀ r : ℕ, 1 ≤ r → ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ m k : ℕ, 1 ≤ m → 1 ≤ k →
      (∃ z : ℤ, coeff (m * p ^ k) (E ^ (r * (m * p ^ k)))
          - coeff (m * p ^ (k - 1)) (E ^ (r * (m * p ^ (k - 1)))) = (p : ℚ) ^ (3 * k) * z) ∧
      (∃ z : ℤ, coeff (m * p ^ k) (F ^ (r * (m * p ^ k)))
          - coeff (m * p ^ (k - 1)) (F ^ (r * (m * p ^ (k - 1)))) = (p : ℚ) ^ (3 * k) * z) := by
  sorry

end OMA.S_oeis_a008978
