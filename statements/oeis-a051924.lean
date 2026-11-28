import Mathlib

/-!
# A051924: binomial(2n,n) - binomial(2n-2,n-1) ≡ n + 2 (mod n^2) iff n is an odd prime

Source: https://oeis.org/A051924
Credit: @Solfanbtc

A051924 (offset 1): `a(n) = binomial(2n, n) - binomial(2n-2, n-1)` (data 1, 4, 14, 50, 182, …).

Conjecture (G. Detlefs, Feb 19 2013, in the entry): `a(n) mod n^2 = n + 2` iff `n` is an odd
prime.

`main` states it for every `n ≥ 1` (the offset). The subtraction is in `ℕ` and does not
truncate, since `binomial(2n-2, n-1) ≤ binomial(2n, n)`. Checked exactly with python3 for
`1 ≤ n ≤ 20000`: no counterexample in either direction.
-/

namespace OMA.S_oeis_a051924

/-- A051924: `binomial(2n, n) - binomial(2n-2, n-1)`. -/
def a (n : ℕ) : ℕ := (2 * n).choose n - (2 * n - 2).choose (n - 1)

/-- Detlefs' conjecture: for `n ≥ 1`, `a(n) mod n^2 = n + 2` iff `n` is an odd prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (a n % n ^ 2 = n + 2 ↔ n.Prime ∧ Odd n) := by
  sorry

end OMA.S_oeis_a051924
