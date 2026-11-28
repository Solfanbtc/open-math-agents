import Mathlib

/-!
# A052210: Numbers k such that k^3 starts with k itself (in base 10).

Source: https://oeis.org/A052210
Credit: @Solfanbtc

"`x` starts with `y`" means that the decimal string of `y` is a prefix of that of `x`.
A052210: 0, 1, 10, 32, 100, 1000, 10000, 31623, 100000, 316228, ...

Conjecture (Dhilan Lahoti, Aug 30 2015): "Replace the first term with 4, then add 1 to all the
others to find numbers k where k^3 starts with k+2. Similar processes can be used for any k+2m."
The second sentence is too vague to state; we state the first.

Minimal fix (indexing): read with the current data, which begins 0, 1, 10, ..., the recipe would
give 4, 2, 11, 33, ..., but `2^3 = 8` does not start with `4`. The comment fits exactly the data
read from the term 1 on (the entry's first term `0` appears to have been prepended later): replacing
`1` by `4` and adding 1 to the other terms `10, 32, 100, ...` gives 4, 11, 33, 101, 1001, 10001,
31624, ..., which is exactly the list of `k` with `k^3` starting with `k + 2` (python, all
`k < 2·10^6`). So we state: `k^3` starts with `k + 2` iff `k = 4` or `k = t + 1` for a term `t ≥ 10`
of A052210.

Encoding: `Nat.digits 10` lists digits least significant first, so the decimal string is its
reverse; prefixes of decimal strings are `List.IsPrefix` of the reversed digit lists.
-/

namespace OMA.S_oeis_a052210

/-- The decimal string of `y` is a prefix of the decimal string of `x`. -/
def StartsWith (x y : ℕ) : Prop := (Nat.digits 10 y).reverse <+: (Nat.digits 10 x).reverse

/-- Lahoti's conjecture (first sentence), for the data read from the term `1` on. -/
theorem main : ∀ k : ℕ,
    StartsWith (k ^ 3) (k + 2) ↔ (k = 4 ∨ ∃ t : ℕ, 10 ≤ t ∧ StartsWith (t ^ 3) t ∧ k = t + 1) := by
  sorry

end OMA.S_oeis_a052210
