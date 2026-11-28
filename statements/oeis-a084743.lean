import Mathlib

/-!
# A084743: Smallest prime of the form n^k + k, or 0 if no such prime exists.

Source: https://oeis.org/A084743
Credit: @Solfanbtc

A084743(n) (`n ≥ 1`) is the smallest prime of the form `n^k + k` (`k ≥ 1`), or `0` if there is
none. E.g. `a(1) = 2 = 1^1 + 1`, `a(3) = 11 = 3^2 + 2`, and `a(5) = 5^7954 + 7954`; the
exponents are A093324. For `n = 11` no such prime is known (`k > 190000`).

Conjecture (entry): no entry is zero, i.e. for every `n ≥ 1` there is `k ≥ 1` with
`n^k + k` prime. (`k = 0` would give `1`, which is not prime, so the bound `k ≥ 1` changes
nothing.)
-/

namespace OMA.S_oeis_a084743

/-- The conjecture: every `n ≥ 1` has a prime of the form `n^k + k`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ (n ^ k + k).Prime := by
  sorry

end OMA.S_oeis_a084743
