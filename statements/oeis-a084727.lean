import Mathlib

/-!
# A084727: Primes arising in A084726.

Source: https://oeis.org/A084727
Credit: @Solfanbtc

`a(n)` (offset 1) is the smallest prime of the form `1 + 1 (1 + d) (1 + 2d) ⋯ (1 + (n-1)d)`,
the product of the first `n` terms of an arithmetic progression with first term 1 and
common difference `d ≥ 1`, plus 1 (A084726 gives the least such `d`; e.g. a(4) = 281 =
1·4·7·10 + 1, a(5) = 76561 = 1·8·15·22·29 + 1). The difference must be positive: `d = 0`
would always give 2. Since the product increases with `d`, the smallest prime comes from
the smallest `d`.

Conjecture (Murthy and Srikanth, 2003): all terms exist, i.e. for every `n ≥ 1` some
`d ≥ 1` makes `1 + ∏_{i < n} (1 + i d)` prime.
-/

namespace OMA.S_oeis_a084727

/-- All terms of A084727 exist. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ d : ℕ, 1 ≤ d ∧ (1 + ∏ i ∈ Finset.range n, (1 + i * d)).Prime := by
  sorry

end OMA.S_oeis_a084727
