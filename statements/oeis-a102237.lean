import Mathlib

/-!
# A102237: smallest product of n primes that is a sum of n distinct primes

Source: https://oeis.org/A102237
`a(n)` (offset 1) is the smallest number that is the product of `n` primes (counted with
multiplicity, e.g. `a(4) = 36 = 2*2*3*3`) and also the sum of `n` distinct primes
(`36 = 3+5+11+17`). Data: 2, 9, 12, 36, 48, 64, 128, 256, ...
Conjecture (Ray Chandler, Feb 25 2005): `a(n) = 2^n` for `n > 5`.

We state: for every `n > 5`, `2^n` is the least element of the set of numbers `m` with
`Ω(m) = n` that are the sum of a set of `n` distinct primes.
Checked with python3 (subset-sum over distinct primes): this definition gives the 20 listed
terms `a(1..20)`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a102237

/-- `m` is the product of `n` primes and the sum of `n` distinct primes. -/
def P (n m : ℕ) : Prop :=
  ArithmeticFunction.cardFactors m = n ∧
    ∃ S : Finset ℕ, S.card = n ∧ (∀ p ∈ S, p.Prime) ∧ ∑ p ∈ S, p = m

theorem main : ∀ n : ℕ, 5 < n → IsLeast {m : ℕ | P n m} (2 ^ n) := by
  sorry

end OMA.S_oeis_a102237
