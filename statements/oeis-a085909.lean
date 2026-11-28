import Mathlib

/-!
# A085909: next occurrence of the prime gap prime(n+1) - prime(n)

Source: https://oeis.org/A085909
Credit: @Solfanbtc

`a(n)` (offset 1) is the smallest prime `p > prime(n)` such that `p + (prime(n+1) - prime(n))` is
the next prime after `p`, or `0` if no such prime exists; i.e. the start of the next occurrence of
the gap `g(n) = prime(n+1) - prime(n)` among consecutive primes.

Conjecture (OEIS comment): `a(n) > 0` for `n > 1` ("implies the twin prime conjecture"): every gap
between consecutive primes other than `3 - 2` occurs again later. With Mathlib's 0-indexed
`p j = Nat.nth Nat.Prime j` (so OEIS `prime(n) = p (n-1)`, and `n > 1` means `j ≥ 1`), and since a
prime `q` whose next prime is `q + g` is `q = p m` with `p (m+1) - p m = g`: for every `j ≥ 1` there
is `m > j` with `p (m+1) - p m = p (j+1) - p j`.
-/

namespace OMA.S_oeis_a085909

/-- The `j`-th prime, 0-indexed (`p 0 = 2`). -/
noncomputable def p (j : ℕ) : ℕ := Nat.nth Nat.Prime j

/-- Every prime gap after the first occurs again later. -/
theorem main : ∀ j : ℕ, 1 ≤ j → ∃ m : ℕ, j < m ∧ p (m + 1) - p m = p (j + 1) - p j := by
  sorry

end OMA.S_oeis_a085909
