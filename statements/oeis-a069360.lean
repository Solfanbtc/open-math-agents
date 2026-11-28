import Mathlib

/-!
# A069360: Number of prime pairs (p,q), p <= q, such that (p+q)/2 = 2*n.

Source: https://oeis.org/A069360
Credit: @Solfanbtc

Claim (comment in the entry): "The Goldbach conjecture, if true, would imply a(n) > 0." The open
statement recorded here is a(n) > 0 for every n ≥ 1 (offset 1), i.e. every multiple of 4 is a
sum of two primes. It is implied by, and weaker than, Goldbach's conjecture
(`goldbach` in FormalConjectures/Wikipedia/GoldbachConjecture.lean), and is itself open.

Conventions.
* a(n) = #{(p, q) : p, q prime, p ≤ q, p + q = 4n}; (p+q)/2 = 2n means p + q = 4n exactly.
  Checked with `#eval` against the first 34 listed terms.
-/

namespace OMA.S_oeis_a069360

/-- A069360: the number of prime pairs `p ≤ q` with `p + q = 4 n`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.range (4 * n + 1)).filter fun p =>
    p.Prime ∧ (4 * n - p).Prime ∧ p ≤ 4 * n - p).card

theorem main : ∀ n : ℕ, 1 ≤ n → 0 < a n := by
  sorry

end OMA.S_oeis_a069360
