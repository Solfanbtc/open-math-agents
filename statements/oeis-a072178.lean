import Mathlib

/-!
# A072178: a(n)-th factorial is the smallest factorial containing exactly n 4's, or 0 if no such number exists.

Source: https://oeis.org/A072178
Credit: @Solfanbtc

`a(n)` (offset 1) is the least `k` such that the decimal expansion of `k!` contains exactly `n`
digits 4, or 0 if there is no such `k`. Data: 4, 19, 21, 24, 44, 42, 50, 57, 0, 60, ...
(the listed terms other than `a(9)` are reproduced by a search over `k ≤ 4000`, checked in Python).

Conjecture (%C): `a(9) = 0`, i.e. no factorial contains exactly nine digits 4 (the entry
reports that no factorial below 10000, read as `k!` with `k < 10000`, has nine 4's). The statement is that conjecture: for every
`k`, the number of 4's among the decimal digits of `k!` is not 9.
-/

namespace OMA.S_oeis_a072178

theorem main : ∀ k : ℕ, (Nat.digits 10 k.factorial).count 4 ≠ 9 := by
  sorry

end OMA.S_oeis_a072178
