import Mathlib

/-!
# A086550: Smallest k with tau(k) - tau(k-1) = n

Source: https://oeis.org/A086550
Credit: @Solfanbtc

`a(n)` (offset 0) is the smallest `k` such that `τ(k) - τ(k-1) = n`, `τ` the number of divisors,
or `0` if no such number exists: `3, 2, 6, 50, 12, 36, …` (e.g. `τ(50) - τ(49) = 6 - 3 = 3`). Here
`k ≥ 2`, so that `k - 1 ≥ 1` (a search reproduces the first 40 data terms).

Conjecture (OEIS comment): no term is zero, i.e. for every `n ≥ 0` there is `k ≥ 2` with
`τ(k) - τ(k-1) = n`.
-/

namespace OMA.S_oeis_a086550

/-- Every difference `n ≥ 0` occurs as `τ(k) - τ(k-1)` for some `k ≥ 2`. -/
theorem main : ∀ n : ℕ, ∃ k : ℕ, 2 ≤ k ∧
    ((k.divisors.card : ℤ) - ((k - 1).divisors.card : ℤ)) = n := by
  sorry

end OMA.S_oeis_a086550
