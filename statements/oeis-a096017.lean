import Mathlib

/-!
# A096017: Numbers n such that 4^k*n, for k >= 0, have a unique partition into three distinct positive squares.

Source: https://oeis.org/A096017
Credit: @Solfanbtc

A partition of `m` into three distinct positive squares is a triple `0 < a < b < c` with
`a^2 + b^2 + c^2 = m`. The terms are the numbers `n` such that every `4^k n` (`k ≥ 0`) has
exactly one such partition. As the data and the Mathematica program of the entry show, only
the primitive such `n` (those not divisible by 4) are listed: multiples of 4 are left out,
since a partition of `4m` into three squares has all three squares even.

The entry's comment: *It is conjectured that this sequence is complete* (keyword `fini`,
`full`): the 102 listed terms of %S, %T, %U are all the terms. Stated as: for every `n`,
`4 ∤ n` and every `4^k n` has a unique partition iff `n` is one of the listed terms.
Checked by computer for `n ≤ 200000`.
-/

namespace OMA.S_oeis_a096017

/-- Number of partitions of `m` into three distinct positive squares `a^2 + b^2 + c^2`,
`0 < a < b < c`. -/
def reps (m : ℕ) : ℕ :=
  ((Finset.Icc 1 m ×ˢ Finset.Icc 1 m ×ˢ Finset.Icc 1 m).filter fun t =>
    t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = m).card

/-- The listed terms of A096017 (%S, %T, %U). -/
def terms : List ℕ :=
  [14, 21, 26, 29, 30, 35, 38, 41, 42, 45, 46, 49, 50, 53, 54, 59, 61, 65, 66, 70, 75, 78, 81,
   83, 91, 93, 106, 107, 109, 113, 114, 115, 118, 121, 133, 137, 139, 142, 145, 147, 153,
   157, 162, 169, 171, 178, 190, 198, 202, 205, 211, 214, 219, 226, 235, 243, 253, 258, 262,
   265, 277, 283, 289, 291, 298, 307, 313, 323, 331, 337, 358, 363, 379, 387, 397, 403, 418,
   427, 438, 442, 445, 457, 466, 498, 499, 505, 547, 562, 577, 603, 643, 723, 793, 883, 907,
   1003, 1227, 1243, 1387, 1411, 1467, 1507]

/-- The conjecture that A096017 is complete. -/
theorem main :
    ∀ n : ℕ, (¬ 4 ∣ n ∧ ∀ k : ℕ, reps (4 ^ k * n) = 1) ↔ n ∈ terms := by
  sorry

end OMA.S_oeis_a096017
