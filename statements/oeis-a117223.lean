import Mathlib

/-!
# A117223: Numbers n such that Phi(n,x) is a flat cyclotomic polynomial of order three.

Source: https://oeis.org/A117223
Credit: @Solfanbtc

A flat polynomial has all coefficients in {-1, 0, 1}; order three means n = pqr with odd primes
p < q < r. The entry (M. F. Hasler, 2009): "Kaplan shows that the sequence also includes pqr if
r = +-1 (mod pq)" (further cases are covered by David Broadhurst's conjectures, given only in an
external link and not stated here).

Status: this is a theorem: N. Kaplan, "Flat cyclotomic polynomials of order three",
J. Number Theory 127 (2007), 118-126. We state it as quoted in the entry.

Conventions.
* Φ_n = `Polynomial.cyclotomic n ℤ`; flat = every coefficient c satisfies |c| ≤ 1.
* r ≡ ±1 (mod pq) is `r % (p*q) = 1 ∨ r % (p*q) = p*q - 1`.
* python3 sanity check: Φ_n is flat for n = 3·5·29, 3·5·31, 3·7·43, 5·7·71, while Φ_105
  (r = 7, not ±1 mod 15) has a coefficient -2.
-/

namespace OMA.S_oeis_a117223

/-- All coefficients of f lie in {-1, 0, 1}. -/
def IsFlat (f : Polynomial ℤ) : Prop := ∀ k : ℕ, |f.coeff k| ≤ 1

theorem main : ∀ p q r : ℕ, p.Prime → q.Prime → r.Prime → 2 < p → p < q → q < r →
    (r % (p * q) = 1 ∨ r % (p * q) = p * q - 1) →
    IsFlat (Polynomial.cyclotomic (p * q * r) ℤ) := by
  sorry

end OMA.S_oeis_a117223
