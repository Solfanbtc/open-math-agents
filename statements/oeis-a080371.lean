import Mathlib

/-!
# A080371: a(n) is the smallest x such that the quotient d(x+1)/d(x) equals n, where d = A000005.

Source: https://oeis.org/A080371
Credit: @Solfanbtc

`a(n)` is the least positive `x` with `d(x+1) = n * d(x)`, `d` the number of divisors.

Conjecture (David A. Corneth, 2021): for every prime `p`, `a(p) = 2^(p-1) * k - 1` for some
`k > 0`, i.e. `2^(p-1)` divides `a(p) + 1` (then `k = (a(p) + 1) / 2^(p-1) > 0` automatically).
The statement only concerns primes `p` for which `a(p)` exists (it is the least element of the
set below); the existence of `a(p)` is not part of the conjecture.
Checked against the data: for the primes p = 2, 3, 5, ..., 37 of %S, %T, %U,
`a(p) + 1` = 2, 12, 48, 192, 5120, 20480, 983040, 786432, 62914560, 13690208256,
22548578304, 1168231104512 are divisible by `2^(p-1)`.
-/

namespace OMA.S_oeis_a080371

/-- The positive `x` with `d(x+1)/d(x) = n`. -/
def S (n : ℕ) : Set ℕ := {x | 0 < x ∧ (x + 1).divisors.card = n * x.divisors.card}

/-- Corneth's conjecture: if `x = a(p)` for a prime `p`, then `x = 2^(p-1) * k - 1`, `k > 0`. -/
theorem main : ∀ p x : ℕ, p.Prime → IsLeast (S p) x →
    ∃ k : ℕ, 0 < k ∧ x + 1 = 2 ^ (p - 1) * k := by
  sorry

end OMA.S_oeis_a080371
