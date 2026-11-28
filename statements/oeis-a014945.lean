import Mathlib

/-!
# A014945: Numbers k such that k divides 4^k - 1

Source: https://oeis.org/A014945
Credit: @Solfanbtc

A014945: the positive integers `k` with `k ∣ 4^k - 1`: `1, 3, 9, 21, 27, 63, 81, …` (the
condition reproduces all 46 data terms).

Conjecture (Thomas Ordowski, Dec 24 2018, OEIS comment): if `k` divides `4^k - 1`, then
`(4^k - 1)/k` is squarefree. Here `k` ranges over the positive integers (the terms of the
sequence; `k = 0` is excluded since it is not a term). Python check: for every term `k ≤ 12483`
no `p^2` with `p < 20000` prime divides `(4^k - 1)/k`.
-/

namespace OMA.S_oeis_a014945

/-- Ordowski's conjecture: for `k ≥ 1` with `k ∣ 4^k - 1`, `(4^k - 1)/k` is squarefree. -/
theorem main : ∀ k : ℕ, 1 ≤ k → k ∣ 4 ^ k - 1 → Squarefree ((4 ^ k - 1) / k) := by
  sorry

end OMA.S_oeis_a014945
