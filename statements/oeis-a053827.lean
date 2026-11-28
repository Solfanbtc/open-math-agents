import Mathlib

/-!
# A053827: Sum of digits of (n written in base 6).

Source: https://oeis.org/A053827
Credit: @Solfanbtc

Omar E. Pol (Feb 21 2010, in the entry): "It appears that this can be written as a triangle:
0, 1,2,3,4,5, 1,2,3,4,5,6,2,3,4,5,6,7,..., where the rows converge to A173526" (see the
analogous conjecture in A000120).

Conventions.
* a(n) = sum of the base-6 digits of n (`(Nat.digits 6 n).sum`), offset 0.
* A173526(m) = 1 + A053827(m-1) (m ≥ 1), its definition.
* The triangle: after the initial 0, row k (k ≥ 0) consists of a(6^k + i), 0 ≤ i < 5·6^k
  (row lengths 5, 30, 180, ..., as displayed: 1,...,5; then 1,2,...,10 over 30 terms).
  "The rows converge to A173526" means each row is the initial segment of length 5·6^k of
  A173526, i.e. a(6^k + i) = A173526(i+1) for 0 ≤ i < 5·6^k (the rows are then nested
  prefixes of A173526). (python3: true for k ≤ 5.)
-/

namespace OMA.S_oeis_a053827

/-- A053827: sum of base-6 digits. -/
def a (n : ℕ) : ℕ := (Nat.digits 6 n).sum

/-- A173526 (offset 1): 1 + A053827(m-1). -/
def A173526 (m : ℕ) : ℕ := 1 + a (m - 1)

theorem main : ∀ k i : ℕ, i < 5 * 6 ^ k → a (6 ^ k + i) = A173526 (i + 1) := by
  sorry

end OMA.S_oeis_a053827
