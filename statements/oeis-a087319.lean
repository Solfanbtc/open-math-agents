import Mathlib

/-!
# A087319: Smallest n^k + 1 with tau(n^k + 1) = tau(n), or 0 if none exists.

Source: https://oeis.org/A087319
Credit: @Solfanbtc

A087319(n) is the smallest number of the form `n^k + 1` (`k ≥ 0`; e.g. `a(2) = 2 = 2^0 + 1`)
whose number of divisors equals `τ(n)`, or `0` if there is none. If `n` is a square then
`a(n) = 0` (stated in the entry as a fact).

Conjecture (David Wasserman, 2005): the other zeros of the data, at
`n = 12, 20, 27, 28, 45, 48, 50, 52, 55`, are genuine. That is, for each of these `n` and every
`k ≥ 0`, `τ(n^k + 1) ≠ τ(n)` (he checked `k ≤ 255`). Checked with python3: with `k ≥ 0` the
definition reproduces every nonzero term for `n ≤ 55`, and for the nine `n` above no `k ≤ 8`
gives `τ(n^k + 1) = τ(n)` (one case, `55^8 + 1`, was left undecided by the quick factorer).
-/

namespace OMA.S_oeis_a087319

/-- The conjecture: for these `n`, no `n^k + 1` has as many divisors as `n`. -/
theorem main : ∀ n ∈ ({12, 20, 27, 28, 45, 48, 50, 52, 55} : Finset ℕ), ∀ k : ℕ,
    (n ^ k + 1).divisors.card ≠ n.divisors.card := by
  sorry

end OMA.S_oeis_a087319
