import Mathlib

/-!
# A053735: Sum of digits of (n written in base 3).

Source: https://oeis.org/A053735
Credit: @Solfanbtc

Omar E. Pol (Feb 20 2010, in the entry): A053735 can be written as a triangle with row lengths
A025192 (1, 2, 6, 18, ...): 0; 1, 2; 1, 2, 3, 2, 3, 4; ... where the k-th row contains
a(3^k + i) for 0 <= i < 2*3^k and converges to A173523 as k -> infinity. The entry notes these
were originally conjectures and were "Changed ... to statements" (F. T. Adams-Watters, 2015):
the claim is an elementary fact, stated here as such.

Conventions.
* a(n) = sum of the base-3 digits of n (`(Nat.digits 3 n).sum`), offset 0.
* A173523(m) = 1 + A053735(m-1) (m ≥ 1), its definition. The k-th row (k ≥ 0) is
  a(3^k + i), 0 ≤ i < 2·3^k, and "converges to A173523" means each row is the initial segment of
  length 2·3^k of A173523, i.e. a(3^k + i) = A173523(i+1) = 1 + a(i) for 0 ≤ i < 2·3^k (the
  rows are then nested prefixes of A173523). (python3 check for k ≤ 7; e.g.
  row 2 = 1,2,3,2,3,4 = 1 + (0,1,2,1,2,3).)
-/

namespace OMA.S_oeis_a053735

/-- A053735: sum of base-3 digits. -/
def a (n : ℕ) : ℕ := (Nat.digits 3 n).sum

/-- A173523 (offset 1): 1 + A053735(m-1). -/
def A173523 (m : ℕ) : ℕ := 1 + a (m - 1)

theorem main : ∀ k i : ℕ, i < 2 * 3 ^ k → a (3 ^ k + i) = A173523 (i + 1) := by
  sorry

end OMA.S_oeis_a053735
