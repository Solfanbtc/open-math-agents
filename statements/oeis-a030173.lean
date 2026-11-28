import Mathlib

/-!
# A030173: Differences p(i)-p(j) between primes, sorted in numerical order.

Source: https://oeis.org/A030173
Credit: @Solfanbtc

The sequence lists the positive differences `p - q` of primes `q < p`:
`1, 2, 3, 4, 5, 6, 8, 9, …`.

Conjecture (Polignac 1849, as recorded in the entry): this set is the union of the (positive)
even numbers and the numbers `p - 2` with `p` an odd prime.

(The inclusion `⊆` is elementary: an odd difference must involve the prime `2`. The content of
the conjecture is that every positive even number is a difference of two primes. This is weaker
than, and distinct from, de Polignac's conjecture on infinitely many prime gaps of each even
size.) Checked numerically for differences up to 90 against the listed data.
-/

namespace OMA.S_oeis_a030173

/-- The positive differences of two primes (the terms of A030173). -/
def primeDifferences : Set ℕ := {d | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ q < p ∧ d = p - q}

/-- Conjecture (Polignac 1849, OEIS A030173): the differences of primes are exactly the positive
even numbers together with the numbers `p - 2`, `p` an odd prime. -/
theorem main :
    primeDifferences = {d | 0 < d ∧ Even d} ∪ {d | ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ d = p - 2} := by
  sorry

end OMA.S_oeis_a030173
