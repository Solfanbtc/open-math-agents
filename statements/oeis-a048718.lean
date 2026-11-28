import Mathlib

/-!
# A048718: Binary expansion matches ((0)*0001)*(0*); or, Zeckendorf-like expansion of n using recurrence f(n) = f(n-1) + f(n-4).

Source: https://oeis.org/A048718
Credit: @Solfanbtc

A048718 lists, in increasing order, the numbers whose binary expansion matches
`((0)*0001)*(0*)`, i.e. with at most one 1-bit in each range of four consecutive bits (any two
1-bits are at least 4 positions apart): `0, 1, 2, 4, 8, 16, 17, 32, 33, 34, 64, ...`.

Conjectures (Paul D. Hanna, Jan 22 2006, in the entry): for every term `a(n)`,
`a XOR 14a = 15a`, `3a XOR 9a = 10a`, `3a XOR 13a = 14a`, `5a XOR 9a = 12a`, `5a XOR 11a = 14a`,
`6a XOR 11a = 13a`, `7a XOR 9a = 14a`, `7a XOR 10a = 13a`, `7a XOR 11a = 12a`,
`12a XOR 21a = 25a`, `12a XOR 37a = 41a` ("etc."; the eleven listed identities are stated).

Status: SOLVED. The entry records (Sebastian Karlsson, Dec 31 2022) that the conjectures can be
verified using the Walnut theorem-prover.

A python3 check: the bitwise membership test reproduces the data, and the eleven identities hold
for all 476 terms below `2¹⁸`.

Conventions:
* Membership is `x &&& (x >>> k) = 0` for `k = 1, 2, 3` (no two 1-bits at distance 1, 2 or 3).
  Since A048718 enumerates exactly these numbers, "for every term" is "for every such `x`".
* `^^^` is bitwise XOR on `ℕ`.
-/

namespace OMA.S_oeis_a048718

/-- `x` is a term of A048718: no two 1-bits of `x` at distance `1`, `2` or `3`. -/
def IsTerm (x : ℕ) : Prop := x &&& (x >>> 1) = 0 ∧ x &&& (x >>> 2) = 0 ∧ x &&& (x >>> 3) = 0

/-- Hanna's XOR identities for the terms of A048718. -/
theorem main : ∀ x : ℕ, IsTerm x →
    (x ^^^ 14 * x = 15 * x) ∧ (3 * x ^^^ 9 * x = 10 * x) ∧ (3 * x ^^^ 13 * x = 14 * x) ∧
    (5 * x ^^^ 9 * x = 12 * x) ∧ (5 * x ^^^ 11 * x = 14 * x) ∧ (6 * x ^^^ 11 * x = 13 * x) ∧
    (7 * x ^^^ 9 * x = 14 * x) ∧ (7 * x ^^^ 10 * x = 13 * x) ∧ (7 * x ^^^ 11 * x = 12 * x) ∧
    (12 * x ^^^ 21 * x = 25 * x) ∧ (12 * x ^^^ 37 * x = 41 * x) := by
  sorry

end OMA.S_oeis_a048718
