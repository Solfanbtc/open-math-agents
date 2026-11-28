import Mathlib

/-!
# A029858: a(n) = (3^n - 3)/2 counts the integers below 10^(n-1) using only the digits 7, 8, 9

Source: https://oeis.org/A029858
Credit: @Solfanbtc

A029858 (offset 1): `a(n) = (3^n - 3)/2`, data 0, 3, 12, 39, 120, …

The entry says: "Conjectured to be the number of integers from 0 to 10^(n-1) - 1 that lack
0, 1, 2, 3, 4, 5 and 6 as a digit. - Alexandre Wajnberg, Apr 25 2005. This is easily verified
to be true. - Renzo Benedetti, Sep 25 2008". So the claim is a known (elementary) fact: such an
integer has only the digits 7, 8, 9, and there are `3 + 9 + … + 3^(n-1) = (3^n - 3)/2` of them
with at most `n - 1` digits.

`main` states it for every `n ≥ 1` (the offset); checked with python3 for `1 ≤ n ≤ 7`.
Conventions. The integer `0` is written with the digit `0`, so it never counts; since
`Nat.digits 10 0 = []`, we require `0 < x` explicitly. `3^n - 3` is even, so the division by 2
is exact.
-/

namespace OMA.S_oeis_a029858

/-- A029858: `(3^n - 3)/2`. -/
def a (n : ℕ) : ℕ := (3 ^ n - 3) / 2

/-- The number of integers `x` with `0 ≤ x ≤ 10^(n-1) - 1` none of whose decimal digits is one
of `0, 1, …, 6`. -/
def count (n : ℕ) : ℕ :=
  ((Finset.range (10 ^ (n - 1))).filter (fun x => 0 < x ∧ ∀ d ∈ Nat.digits 10 x, 6 < d)).card

/-- Wajnberg's claim (verified by Benedetti): for `n ≥ 1`, the count equals `a(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → count n = a n := by
  sorry

end OMA.S_oeis_a029858
