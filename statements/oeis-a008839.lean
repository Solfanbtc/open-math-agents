import Mathlib

/-!
# A008839: 5^58 is the largest power of 5 with no digit 0

Source: https://oeis.org/A008839
Credit: @Solfanbtc

A008839: the numbers `k` such that the decimal expansion of `5^k` contains no zeros.
The entry: "Here is 5^58, conjecturally the largest power of 5 that does not contain a 0".

`main` states that `58` is the greatest such `k` (`k = 0`, `5^0 = 1`, counts as a term).
Checked with python3: the zeroless exponents below `3·10^4` end with 58.
-/

namespace OMA.S_oeis_a008839

/-- The conjecture: `58` is the largest `k` such that `5^k` has no decimal digit `0`. -/
theorem main : IsGreatest {k : ℕ | 0 ∉ Nat.digits 10 (5 ^ k)} 58 := by
  sorry

end OMA.S_oeis_a008839
