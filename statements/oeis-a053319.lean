import Mathlib

/-!
# A053319: Distance between the smaller members of successive twin prime pairs.

Source: https://oeis.org/A053319
Credit: @Solfanbtc

`a(n) = A001359(n+1) - A001359(n)` (offset 1), where `A001359 = 3, 5, 11, 17, 29, ...` lists
the lesser twin primes (`p` and `p + 2` both prime); data `2, 6, 6, 12, 12, 18, ...`.
`A014574(n) = A001359(n) + 1` are the averages of twin prime pairs (`4, 6, 12, 18, ...`).

Conjecture (Thomas Ordowski, Jul 21 2012, in the entry): `a(n) < log(A014574(n))^3` for `n > 2`
(natural logarithm).

Index-free form: if `p < q` are consecutive lesser twin primes (no lesser twin prime strictly
between them) and `p` is at least the third lesser twin prime, `11`, then
`q - p < log(p + 1)^3`. This is the conjecture for every `n > 2` for which `a(n)` is defined,
without assuming that there are infinitely many twin primes.

A python3 check (sieve to `3·10^8`, all 1166480 lesser twin primes there): the inequality holds
for every `n > 2`; it fails at `n = 2` (`a(2) = 6 > log(6)^3 ≈ 5.75`), whence the range `n > 2`.
-/

namespace OMA.S_oeis_a053319

/-- `p` is the lesser member of a twin prime pair. -/
def IsLesserTwin (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

/-- Ordowski's conjecture: `a(n) < log(A014574(n))^3` for `n > 2`. -/
theorem main : ∀ p q : ℕ, IsLesserTwin p → IsLesserTwin q → p < q →
    (∀ r, p < r → r < q → ¬ IsLesserTwin r) → 11 ≤ p →
    ((q : ℝ) - p) < Real.log ((p : ℝ) + 1) ^ 3 := by
  sorry

end OMA.S_oeis_a053319
