import Mathlib

/-!
# A092925: Smallest prime of the form n(n-1)(n-2)...(n-k)-1, or 0 if no such prime exists.

Source: https://oeis.org/A092925
Credit: @Solfanbtc

Conjecture (OEIS A092925): no term is zero, i.e. for every n >= 3 (offset 3) some number
n(n-1)...(n-k) - 1 with 0 <= k <= n-1 is prime.

The product n(n-1)...(n-k) of k+1 consecutive factors is `Nat.descFactorial n (k + 1)`; k ranges
over 0..n-1 (for k >= n the product contains the factor 0). Checked numerically: the least such
primes for n = 3..22 are 2, 3, 19, 5, 41, 7, 71, 89, 109, 11, 17159, ..., as listed.
-/

namespace OMA.S_oeis_a092925

theorem main : ∀ n : ℕ, 3 ≤ n → ∃ k : ℕ, k < n ∧ (Nat.descFactorial n (k + 1) - 1).Prime := by
  sorry

end OMA.S_oeis_a092925
