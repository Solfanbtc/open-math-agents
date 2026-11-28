import Mathlib

/-!
# A081978: Smallest triangular number with exactly n divisors, or 0 if no such number exists.

Source: https://oeis.org/A081978
Credit: @Solfanbtc

`a(n)` is 0 exactly when no triangular number `k(k+1)/2` has exactly `n` divisors, so
`a(n) > 0` means that some triangular number has exactly `n` divisors.

Conjecture (Jon E. Schoenfield, 2014): `a(2j) > 0` for all `j > 1`, i.e. for every `j > 1`
some triangular number has exactly `2j` divisors. (Checked by Schoenfield through `2j = 1000`;
the data of %S, %T, %U has nonzero `a(2j)` for all `2 ≤ j ≤ 22`, e.g. a(4) = 6, a(6) = 28,
a(8) = 66, ..., a(44) = 2096128.)
-/

namespace OMA.S_oeis_a081978

/-- Schoenfield's conjecture: for every `j > 1` there is a triangular number with exactly
`2j` divisors. -/
theorem main : ∀ j : ℕ, 1 < j → ∃ k : ℕ, (k * (k + 1) / 2).divisors.card = 2 * j := by
  sorry

end OMA.S_oeis_a081978
