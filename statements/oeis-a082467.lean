import Mathlib

/-!
# A082467: Least k>0 such that n-k and n+k are both primes.

Source: https://oeis.org/A082467
Credit: @Solfanbtc

Conjecture (OEIS A082467): "The existence of k > 0 for all n >= 4 is equivalent to the strong
Goldbach Conjecture that every even number >= 8 is the sum of two distinct primes." The entry thus
records the (conjectural) existence of a(n) for every n >= 4: there is k > 0 with n - k and n + k
both prime. `main` states this existence (k < n is automatic, since n - k must be a prime, hence
positive; it is written out so that the natural subtraction is exact).
(The upstream statement `goldbach` allows p = q, so it does not cover this distinct-primes form.
The remark that the twin prime conjecture implies infinitely many a(n) = 1 is an implication and
is not stated.)
-/

namespace OMA.S_oeis_a082467

theorem main : ∀ n : ℕ, 4 ≤ n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (n - k).Prime ∧ (n + k).Prime := by
  sorry

end OMA.S_oeis_a082467
