import Mathlib

/-!
# A081391: C(2k, k) has only one prime divisor whose exponent exceeds one

Source: https://oeis.org/A081391
Credit: @Solfanbtc

Numbers `k` such that the central binomial coefficient `C(2k, k)` has exactly one prime divisor `p`
with `p^2 ∣ C(2k, k)`: `3, 6, 7, 8, 9, 10, 11, 12, 16, 21, …, 171, 784, 786` (a computation of the
`p`-adic valuations by Kummer's theorem reproduces all 25 data terms; e.g.
`C(1572, 786) = 2^4 · m` with `m` squarefree).

Conjecture (Jon E. Schoenfield, Jul 29 2017, OEIS comment): "No more terms through `10^6`;
conjecture: no terms after 786." Stated as: every term is `≤ 786`.
-/

namespace OMA.S_oeis_a081391

/-- `C(2k, k)` has exactly one prime divisor whose exponent exceeds one. -/
def IsTerm (k : ℕ) : Prop :=
  ((Nat.centralBinom k).primeFactors.filter fun p => p ^ 2 ∣ Nat.centralBinom k).card = 1

/-- There are no terms after 786. -/
theorem main : ∀ k : ℕ, IsTerm k → k ≤ 786 := by
  sorry

end OMA.S_oeis_a081391
