import Mathlib

/-!
# A139092: a(n) = number of distinct prime divisors of (9+prime(n)!)/9.

Source: https://oeis.org/A139092
Credit: @Solfanbtc

A139089(n) = prime(n)!/9 + 1 = (9 + prime(n)!)/9 for `n ≥ 4` (offset 4, so `prime(n) ≥ 7`
and `9 ∣ prime(n)!`); A139092(n) is its number of distinct prime divisors.

Conjecture (A. Jasinski, OEIS A139092): "all prime divisors in A139089 are distinct".
Reading: in each term of A139089 the prime divisors are all distinct, i.e. every term is
squarefree (so its numbers of prime divisors with and without multiplicity agree). The other
conceivable reading, that no prime divides two different terms, is false: 31 divides both
11!/9 + 1 = 4435201 and 13!/9 + 1 = 691891201. A python3 factorization
confirms squarefreeness for every prime `7 ≤ p ≤ 79` with a complete factorization
(and reproduces the listed values of A139092 there).

`prime(n)` (1-indexed, `prime(1) = 2`) is `Nat.nth Nat.Prime (n - 1)`.
-/

namespace OMA.S_oeis_a139092

/-- A139089(n) = prime(n)!/9 + 1. -/
noncomputable def A139089 (n : ℕ) : ℕ := (Nat.nth Nat.Prime (n - 1)).factorial / 9 + 1

/-- Conjecture: every term of A139089 (`n ≥ 4`) has only distinct prime divisors,
i.e. is squarefree. -/
theorem main : ∀ n : ℕ, 4 ≤ n → Squarefree (A139089 n) := by
  sorry

end OMA.S_oeis_a139092
