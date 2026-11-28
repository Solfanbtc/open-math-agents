import Mathlib

/-!
# A093538: Number of primes between 10^n and 10^n+100.

Source: https://oeis.org/A093538
Credit: @Solfanbtc

`a(n)` (`n ≥ 0`) is the number of primes `p` with `10^n < p ≤ 10^n + 100`. The upper endpoint
counts: `a(0) = 26 = π(101)`. For `n ≥ 1` both endpoints are composite. E.g. `a(7) = 2`
(`10000019`, `10000079`).

Conjecture (Robert Israel, 2020): `a(n) = 1` for infinitely many `n`, but `a(n) ≥ 2` for only
finitely many `n`. (The entry adds, hedged, "it may be that `a(n) ≤ 1` for `n > 775`". That is
not stated here.)
-/

namespace OMA.S_oeis_a093538

/-- A093538(n): the number of primes in `(10^n, 10^n + 100]`. -/
def a (n : ℕ) : ℕ := ((Finset.Ioc (10 ^ n) (10 ^ n + 100)).filter Nat.Prime).card

/-- The conjecture: `a(n) = 1` infinitely often, `a(n) ≥ 2` only finitely often. -/
theorem main : {n : ℕ | a n = 1}.Infinite ∧ {n : ℕ | 2 ≤ a n}.Finite := by
  sorry

end OMA.S_oeis_a093538
