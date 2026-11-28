import Mathlib

/-!
# A116997: Length of chain starting 2n, iterating f(m) = m - (number of distinct representations of m as the sum of two primes).

Source: https://oeis.org/A116997
Credit: @Solfanbtc

Claim (Jonathan Vos Post, OEIS A116997, %C line): there is no upper bound for `a(n)`.

Definitions.
* `r(m)` is the number of ways of writing `m` as `p + q` with primes `p ≤ q` (A045917 for even
  `m`); `f(m) = m - r(m)`.
* The chain starting at `2n` (`n ≥ 2`) is `2n, f(2n), f(f(2n)), ...`, stopped at the first odd
  value (an odd number is a halting state: `f(3) = 3` in the entry); `a(n)` is its number of
  elements, start and end included (e.g. `(10, 8, 7)` gives `a(5) = 3`).

Formalization. `a(n) ≥ L + 2` says that `f^[i](2n)` is even for every `i ≤ L`; "no upper
bound" is: for every `L` some `n ≥ 2` has `f^[i](2n)` even for all `i ≤ L`. (Were some even
`m ≥ 4` not a sum of two primes, the chain through `m` would never end; such an infinite chain
also has no bound, consistently with this formulation.)

Checked with python3: this definition reproduces all listed %S/%T/%U terms; the record values
are `a(n) = 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12` at `n = 2, 5, 8, 9, 10, 23, 25, 467, 1203,
1223, 1713` (`n < 5000`).
-/

namespace OMA.S_oeis_a116997

/-- The number of representations `m = p + q` with primes `p ≤ q`. -/
def r (m : ℕ) : ℕ := ((Finset.range (m / 2 + 1)).filter fun p => p.Prime ∧ (m - p).Prime).card

/-- `f(m) = m - r(m)`. -/
def f (m : ℕ) : ℕ := m - r m

/-- The chain lengths `a(n)` are unbounded. -/
theorem main : ∀ L : ℕ, ∃ n : ℕ, 2 ≤ n ∧ ∀ i ≤ L, Even (f^[i] (2 * n)) := by
  sorry

end OMA.S_oeis_a116997
