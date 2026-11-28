import Mathlib

/-!
# A066888: Number of primes p between triangular numbers T(n) < p <= T(n+1).

Source: https://oeis.org/A066888
Credit: @Solfanbtc

`a(n)` (offset 0) is the number of primes `p` with `T(n) < p ≤ T(n+1)`, where
`T(n) = n(n+1)/2` (A000217). Data: 0, 2, 1, 1, 2, 2, 1, 2, 3, ...
(the definition reproduces every term of %S, %T, %U, n = 0..96).
The %F formula `pi(n(n+1)/2) - pi(n(n-1)/2)` uses the older offset 1; the name and the data
use offset 0, which is what is stated here.

Conjecture (J. W. Nicholson, 2011): for `n > 0`, `a(n) > 0`. The second comment of the entry
(Kamenetsky) is a consequence of this conjecture, not a separate claim.
-/

namespace OMA.S_oeis_a066888

/-- The triangular number `T(n) = n(n+1)/2`. -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- A066888: the number of primes in `(T(n), T(n+1)]`. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ioc (T n) (T (n + 1))).filter Nat.Prime).card

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a066888
