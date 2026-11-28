import Mathlib

/-!
# A053829: Sum of digits of (n written in base 8).

Source: https://oeis.org/A053829
Credit: @Solfanbtc

Conjecture (Omar E. Pol, Feb 21 2010, OEIS A053829, see also A000120 and A173528): A053829 can be
written as a triangle whose rows converge to A173528, where A173528(m) = 1 + (sum of the base-8
digits of m - 1).

The triangle, as displayed in the entry: row 0 is a(0) = 0, and for k >= 1 row k lists a(n) for
8^(k-1) <= n < 8^k (rows of lengths 1, 7, 56, 448, ...: 0; 1..7; 1, 2, ..., 7, 8, 2, 3, ...).
Convergence of the rows to A173528 means: for every position i (counted from 0), the i-th entry
of row k exists and equals A173528(i + 1) = 1 + s_8(i) for all sufficiently large k. Here
s_8(m) = (Nat.digits 8 m).sum, and the i-th entry of row k is s_8(8^(k-1) + i).
-/

namespace OMA.S_oeis_a053829

/-- Sum of the base-8 digits (A053829). -/
def s8 (n : ℕ) : ℕ := (Nat.digits 8 n).sum

theorem main : ∀ i : ℕ, ∃ K : ℕ, ∀ k ≥ K,
    i < 8 ^ k - 8 ^ (k - 1) ∧ s8 (8 ^ (k - 1) + i) = 1 + s8 i := by
  sorry

end OMA.S_oeis_a053829
