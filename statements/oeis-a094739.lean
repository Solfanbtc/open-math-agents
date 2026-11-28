import Mathlib

/-!
# A094739: Numbers m such that 4^k*m, for integer k >= 0, are numbers having a unique partition into three squares.

Source: https://oeis.org/A094739
Credit: @Solfanbtc

A partition of `n` into three squares is a triple `0 ≤ x ≤ y ≤ z` with `n = x² + y² + z²`
(squares may be zero). The entry (Wolfdieter Lang's equivalent name) lists the positive integers
not divisible by 4 that have exactly one such partition; then every `4^k · m` also has exactly
one, and these are all positive integers with a unique partition.

Conjecture (D. H. Lehmer, 1948, as recorded in the entry): there are no more terms than the
33 listed (with Lehmer's list corrected: 163 included, 162 and 182 excluded).
Status: this has been PROVED. The list is complete by S. Arno, "The imaginary quadratic fields of
class number 4", Acta Arith. 60 (1992), 321–334, Theorem 8 (where 19 is missing, as observed by
I. Kaplansky, "Integers uniquely represented by certain ternary forms", 1997, Remark 2.1).

Formalization: the statement is that the set of positive `m` with `¬ 4 ∣ m` and exactly one
partition into three squares is exactly the 33-element list. The condition `¬ 4 ∣ m` is the
entry's alternative name and is needed: read literally, the name would also admit `m = 4`
(all `4^k · 4` have a unique partition), which is not a term.
Checked with `#eval`: for `1 ≤ m ≤ 1000` the defined set is exactly the list.
-/

namespace OMA.S_oeis_a094739

/-- Number of partitions of `n` into three squares: triples `x ≤ y ≤ z` with
`x² + y² + z² = n`. (Each of `x, y, z` is at most `√n`.) -/
def numPartitions (n : ℕ) : ℕ :=
  ((Finset.range (Nat.sqrt n + 1) ×ˢ Finset.range (Nat.sqrt n + 1) ×ˢ
      Finset.range (Nat.sqrt n + 1)).filter
    (fun t => t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧ t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = n)).card

/-- The 33 terms of A094739. -/
def terms : Finset ℕ :=
  {1, 2, 3, 5, 6, 10, 11, 13, 14, 19, 21, 22, 30, 35, 37, 42, 43, 46, 58, 67, 70, 78, 91, 93,
    115, 133, 142, 163, 190, 235, 253, 403, 427}

/-- Lehmer's conjecture (proved by Arno): the list of terms is complete. -/
theorem main : ∀ m : ℕ, (0 < m ∧ ¬ 4 ∣ m ∧ numPartitions m = 1) ↔ m ∈ terms := by
  sorry

end OMA.S_oeis_a094739
