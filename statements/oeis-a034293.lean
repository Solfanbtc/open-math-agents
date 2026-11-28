import Mathlib

/-!
# A034293: 2^168 is the largest power of 2 with no decimal digit 2

Source: https://oeis.org/A034293
Credit: @Solfanbtc

A034293: the numbers `k` such that `2^k` does not contain the digit 2 ("probably finite").
The entry: "Here is 2^168, conjecturally the largest power of 2 that does not contain a 2:
374144419156711147060143317175368453031918731001856."

`main` states that `168` is the greatest such `k`. Checked with python3: below `2·10^4` the
exponents are 23 in number, the last ones being 54, 64, 74, 83, 168.
-/

namespace OMA.S_oeis_a034293

/-- The conjecture: `168` is the largest `k` such that `2^k` has no decimal digit `2`. -/
theorem main : IsGreatest {k : ℕ | 2 ∉ Nat.digits 10 (2 ^ k)} 168 := by
  sorry

end OMA.S_oeis_a034293
