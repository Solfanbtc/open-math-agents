import Mathlib

/-!
# A094787: a(n) = smallest prime p such that p + n is a perfect power m^k, k >= 2.

Source: https://oeis.org/A094787
Credit: @Solfanbtc

For `n ≥ 1` (offset 1), `a(n)` is the least prime `p` such that `p + n` is a perfect power
`m^k` with `k ≥ 2` (A001597). Conjecture (Cino Hilliard, OEIS %C): every prime occurs in this
sequence.

Since it is not known that `a(n)` exists for every `n`, the statement says directly that `p` is
the least prime with that property for some `n ≥ 1`, avoiding any junk value. Numerically
(`n ≤ 10^5`), the first 60 primes all occur and the first terms match the OEIS data.
-/

namespace OMA.S_oeis_a094787

/-- `x` is a perfect power `m^k` with `k ≥ 2` (A001597). -/
def IsPerfectPower (x : ℕ) : Prop := ∃ m k : ℕ, 2 ≤ k ∧ m ^ k = x

theorem main : ∀ p : ℕ, p.Prime → ∃ n : ℕ, 1 ≤ n ∧ IsPerfectPower (p + n) ∧
    ∀ q : ℕ, q.Prime → q < p → ¬ IsPerfectPower (q + n) := by
  sorry

end OMA.S_oeis_a094787
