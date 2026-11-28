import Mathlib

/-!
# A035064: Numbers k such that 2^k does not contain the digit 9 (probably finite).

Source: https://oeis.org/A035064
Credit: @Solfanbtc

Conjecture (in the entry: "probably finite"; N. J. A. Sloane, Feb 10 2023: 2^108 =
324518553658426726783156020576256 is conjecturally the largest power of 2 that does not contain
a 9): the sequence is finite and its terms are exactly the 37 listed terms
0, 1, ..., 11, 14, ..., 20, 23, ..., 28, 30, 31, 45, 46, 47, 57, 58, 59, 71, 77, 99, 108.

Conventions.
* Decimal digits via `Nat.digits 10`; 2^k "does not contain the digit 9" is
  `9 ∉ Nat.digits 10 (2 ^ k)`.
* Stated as an equality of sets with all terms of the data. (python3: for k < 20000 the k with
  no digit 9 in 2^k are exactly these 37 values; so the statement is equivalent to "no k > 108
  works", i.e. 108 is the largest term.)
-/

namespace OMA.S_oeis_a035064

/-- The listed terms of A035064. -/
def listed : Finset ℕ :=
  {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 14, 15, 16, 17, 18, 19, 20, 23, 24, 25, 26, 27, 28, 30,
    31, 45, 46, 47, 57, 58, 59, 71, 77, 99, 108}

theorem main : {k : ℕ | 9 ∉ Nat.digits 10 (2 ^ k)} = ↑listed := by
  sorry

end OMA.S_oeis_a035064
