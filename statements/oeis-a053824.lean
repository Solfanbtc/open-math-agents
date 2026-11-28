import Mathlib

/-!
# A053824: Sum of digits of (n written in base 5).

Source: https://oeis.org/A053824
Credit: @Solfanbtc

Conjecture (Omar E. Pol, Feb 21 2010, OEIS A053824): "it appears that this can be written as a
triangle: 0; 1,2,3,4; 1,2,3,4,5,2,3,4,5,6,...; ... See the conjecture in the entry A000120",
where the conjecture of A000120 (Gary W. Adamson, Jun 03 2009) is that the rows of the
corresponding triangle converge (there to A063787). For base 5 the limit is A173525 (cross-
referenced in the entry), the base-5 member of the family A063787, A173523..A173529:
A173525(m) = 1 + (sum of the base-5 digits of m - 1).

The triangle, as displayed in the entry: row 0 is a(0) = 0, and for k >= 1 row k lists a(n) for
5^(k-1) <= n < 5^k (rows of lengths 1, 4, 20, 100, ...). Convergence of the rows means: for every
position i (counted from 0), the i-th entry of row k exists and equals 1 + s_5(i) for all
sufficiently large k, where s_5(m) = (Nat.digits 5 m).sum and the i-th entry of row k is
s_5(5^(k-1) + i). (The base-8 and base-9 analogues are statements/oeis-a053829.lean and
statements/oeis-a053830.lean; none implies another.)
-/

namespace OMA.S_oeis_a053824

/-- Sum of the base-5 digits (A053824). -/
def s5 (n : ℕ) : ℕ := (Nat.digits 5 n).sum

theorem main : ∀ i : ℕ, ∃ K : ℕ, ∀ k ≥ K,
    i < 5 ^ k - 5 ^ (k - 1) ∧ s5 (5 ^ (k - 1) + i) = 1 + s5 i := by
  sorry

end OMA.S_oeis_a053824
