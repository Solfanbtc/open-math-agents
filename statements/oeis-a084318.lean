import Mathlib

/-!
# A084318: Iterate function described in A084317 if started at initial value n until reaching a fixed point.

Source: https://oeis.org/A084318
Credit: @Solfanbtc

Conjecture (OEIS A084318): a fixed point always exists, i.e. for every starting value n the
iteration of the map g of A084317 reaches some x with g(x) = x.

Definitions: g = A084317 is the concatenation, in decimal, of the distinct prime factors of n in
increasing order (g(2520) = 2357; g(1) = 0 by the entry's convention, and g(0) = 0, no prime
factors). Concatenating p after acc means acc * 10^(number of digits of p) + p. The fixed points
include all primes and 0. Examples: 95 → 519 → 3173 → 19167 → 36389 (prime), so a(95) = 36389.
`main` is stated for all n >= 1 (n = 0 is itself a fixed point).
-/

namespace OMA.S_oeis_a084318

/-- A084317: concatenation of the distinct prime factors of `n`, in increasing order. -/
def g (n : ℕ) : ℕ :=
  ((n.primeFactors.sort (· ≤ ·)).foldl
    (fun acc p => acc * 10 ^ (Nat.digits 10 p).length + p) 0)

theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, g (g^[k] n) = g^[k] n := by
  sorry

end OMA.S_oeis_a084318
