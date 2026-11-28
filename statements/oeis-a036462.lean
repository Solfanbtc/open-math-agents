import Mathlib

/-!
# A036462: Conjecturally, a power of 2 written in base 3 cannot have this many 0's.

Source: https://oeis.org/A036462
Credit: @Solfanbtc

Let `z(n)` = A104320(n) be the number of 0's in the base-3 representation of `2ⁿ`. A036462 lists
(conjecturally) the numbers `m` that are never equal to `z(n)`:
`115, 124, 139, 243, 367, 445, 783, 914, ..., 5100` (44 data terms).

Conjectures (David W. Wilson, Oct 21 2016, edited by Antti Karttunen, Oct 29 2016, in the entry):
1. A104320 never takes the values in this sequence (the 44 listed terms);
2. this sequence is infinite, i.e. infinitely many `m` are never the number of base-3 zeros of a
   power of 2.
Both are stated, as a conjunction.

A python3 check: for `0 ≤ n ≤ 20000` no `z(n)` is one of the 44 listed values, and the values
`< 1300` not attained in that range are exactly the listed `115, ..., 1239`.

Conventions: the base-3 representation is `Nat.digits 3` (no leading zeros); `z(n)` counts its
zero digits.
-/

namespace OMA.S_oeis_a036462

/-- `z n = A104320(n)`: the number of 0's in the base-3 representation of `2ⁿ`. -/
def z (n : ℕ) : ℕ := (Nat.digits 3 (2 ^ n)).count 0

/-- The listed terms of A036462. -/
def data : List ℕ :=
  [115, 124, 139, 243, 367, 445, 783, 914, 958, 1095, 1112, 1200, 1239, 1312, 1487, 1752, 1902,
    2013, 2504, 2583, 2620, 2697, 2725, 2754, 2881, 3015, 3365, 3443, 3612, 3673, 3980, 3984,
    4002, 4105, 4184, 4212, 4315, 4343, 4394, 4477, 4516, 4862, 4918, 5100]

/-- Wilson's two conjectures. -/
theorem main : (∀ m ∈ data, ∀ n : ℕ, z n ≠ m) ∧ Set.Infinite {m : ℕ | ∀ n : ℕ, z n ≠ m} := by
  sorry

end OMA.S_oeis_a036462
