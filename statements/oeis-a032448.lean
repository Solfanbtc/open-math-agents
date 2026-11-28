import Mathlib

/-!
# A032448: Smallest prime == -1 modulo prime(n).

Source: https://oeis.org/A032448
Credit: @Solfanbtc

`a(n)` (offset 1) is the smallest prime `q` with `q ≡ -1 (mod prime(n))`:
`3, 2, 19, 13, 43, 103, 67, 37, 137, ...` (it exists by Dirichlet's theorem).

Conjecture (the entry): `a(n) ≤ prime(n)² - 1`. (The entry adds that this would imply
`A006530(a(n) + 1) = prime(n)` and hence that the sequence has no repeated values; these
consequences are not part of the statement.)

Stated as: for every prime `p`, some prime `q ≡ -1 (mod p)` satisfies `q ≤ p² - 1`; this is
equivalent to `a(n) ≤ prime(n)² - 1` for all `n` (the least such prime is at most any such prime,
and conversely `a(n)` itself is one), and avoids defining the minimum.

A python3 check: the bound holds for all 430 primes `p < 3000`, and the first data terms are
reproduced.

Conventions: `q ≡ -1 (mod p)` is written `p ∣ q + 1`.
-/

namespace OMA.S_oeis_a032448

/-- Conjecture: for every prime `p`, the smallest prime `q ≡ -1 (mod p)` is at most `p² - 1`. -/
theorem main : ∀ p : ℕ, p.Prime → ∃ q : ℕ, q.Prime ∧ p ∣ q + 1 ∧ q ≤ p ^ 2 - 1 := by
  sorry

end OMA.S_oeis_a032448
