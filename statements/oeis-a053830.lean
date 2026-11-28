import Mathlib

/-!
# A053830: Sum of digits of (n written in base 9).

Source: https://oeis.org/A053830
Credit: @Solfanbtc

Conjecture (Omar E. Pol, Feb 23 2010, OEIS A053830, see also A000120 and A173529): A053830 can be
written as a triangle whose rows converge to A173529, where A173529(m) = 1 + (sum of the base-9
digits of m - 1).

The triangle, as displayed in the entry: row 0 is a(0) = 0, and for k >= 1 row k lists a(n) for
9^(k-1) <= n < 9^k (rows of lengths 1, 8, 72, ...: 0; 1..8; 1, 2, ..., 8, 9, 2, 3, ...).
Convergence of the rows to A173529 means: for every position i (counted from 0), the i-th entry
of row k exists and equals A173529(i + 1) = 1 + s_9(i) for all sufficiently large k. Here
s_9(m) = (Nat.digits 9 m).sum, and the i-th entry of row k is s_9(9^(k-1) + i).
(The base-8 analogue is statements/oeis-a053829.lean; neither implies the other.)
-/

namespace OMA.S_oeis_a053830

/-- Sum of the base-9 digits (A053830). -/
def s9 (n : ℕ) : ℕ := (Nat.digits 9 n).sum

theorem main : ∀ i : ℕ, ∃ K : ℕ, ∀ k ≥ K,
    i < 9 ^ k - 9 ^ (k - 1) ∧ s9 (9 ^ (k - 1) + i) = 1 + s9 i := by
  sorry

end OMA.S_oeis_a053830
