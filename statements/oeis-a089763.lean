import Mathlib

/-!
# A089763: a(1) = 1, then the least n-digit prime such that the k-th digit from the Most significant side is prime if k is prime else is composite. The most significant digit is always a 1. 0 if no such prime exists.

Source: https://oeis.org/A089763
Credit: @Solfanbtc

Conjecture (OEIS A089763): no term is zero, i.e. for every n >= 2 there is an n-digit prime whose
first (most significant) digit is 1 and whose k-th digit from the most significant side, for
2 <= k <= n, is a prime digit (2, 3, 5, 7) if k is prime and a "composite" digit otherwise.

Convention for "composite digit": {0, 4, 6, 8, 9}. The digit 0 is included, as in the example of
the entry (a(8) = 12202429 has 0 as its 4th digit), and 1 is excluded: with {0, 4, 6, 8, 9} the
least such primes for n = 2..10 are exactly the listed 13, 127, 1229, 12203, 122029, 1220203,
12202429, 122024299, 1220202089, while allowing 1 would give 122021 for n = 6 instead of 122029,
and excluding 0 would give 12263 for n = 5 instead of 12203 (checked numerically).
Digits are read from `(Nat.digits 10 p).reverse`, position k = index + 1.
-/

namespace OMA.S_oeis_a089763

/-- The digit pattern of the entry for the digit list `L` (most significant first). -/
def Pattern (L : List ℕ) : Prop :=
  L.head? = some 1 ∧
    ∀ i : ℕ, 1 ≤ i → i < L.length →
      (((i + 1).Prime → L.getD i 0 ∈ ({2, 3, 5, 7} : Finset ℕ)) ∧
       (¬ (i + 1).Prime → L.getD i 0 ∈ ({0, 4, 6, 8, 9} : Finset ℕ)))

theorem main : ∀ n : ℕ, 2 ≤ n → ∃ p : ℕ, p.Prime ∧
    ((Nat.digits 10 p).reverse).length = n ∧ Pattern (Nat.digits 10 p).reverse := by
  sorry

end OMA.S_oeis_a089763
