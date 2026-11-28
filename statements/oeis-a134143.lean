import Mathlib

/-!
# A134143: Let T(n) = (p, p+2) denote the n-th pair of twin primes. Let S(n) = 2p+2 (see A054735). Then a(n) = number of ways of writing S(n)

Source: https://oeis.org/A134143
Credit: @Solfanbtc

`T(n) = (p, p+2)` is the n-th twin prime pair (n ≥ 1: (3,5), (5,7), (11,13), ...) and
`S(n) = 2p + 2` (A054735). `a(n)` is the number of ways of writing `S(n) = S(i) + S(j)` with
`i ≤ j < n` (the "m" in the OEIS name is a typo for `n`, as the Maple programs show).

Conjecture (OEIS A134143, from R. K. Guy, Unsolved Problems, Western Number Theory Meeting 1988):
`a(n) > 0` for `n ≥ 3`.

Formalization without indexing: since `n ↦ T(n)` is increasing, `i ≤ j < n` means that the lower
members `q, r` of `T(i), T(j)` satisfy `q ≤ r < p`, and `n ≥ 3` means `p ≥ 11`. We quantify over
twin primes directly instead of using `Nat.nth`, so that the statement does not implicitly
assume infinitely many twin primes. Checked with python3: this reproduces the 99 listed terms,
and `a(n) > 0` for `3 ≤ n ≤ 14871` (all twin pairs below 2·10^6).
-/

namespace OMA.S_oeis_a134143

/-- `p` is the lower member of a twin prime pair `(p, p+2)`. -/
def IsLowerTwin (p : ℕ) : Prop := p.Prime ∧ (p + 2).Prime

/-- Conjecture: for every twin pair `(p, p+2)` from the third one on (`p ≥ 11`), `2p+2` is a sum
`(2q+2) + (2r+2)` over earlier twin pairs `(q, q+2)`, `(r, r+2)` with `q ≤ r < p`. -/
theorem main : ∀ p : ℕ, IsLowerTwin p → 11 ≤ p →
    ∃ q r : ℕ, IsLowerTwin q ∧ IsLowerTwin r ∧ q ≤ r ∧ r < p ∧
      2 * p + 2 = (2 * q + 2) + (2 * r + 2) := by
  sorry

end OMA.S_oeis_a134143
