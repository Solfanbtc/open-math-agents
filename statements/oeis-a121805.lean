import Mathlib

/-!
# A121805: The comma sequence is finite, for any initial term

Source: https://oeis.org/A121805
Credit: @Solfanbtc

The comma sequence (Eric Angelini): the lexicographically earliest sequence of positive
numbers such that the sequence formed by the pairs of digits adjacent to the commas between
the terms equals the sequence of successive differences.

OEIS gives the equivalent formal definition: for n > 1, let x be the least significant digit
of a(n-1); then a(n) = a(n-1) + 10*x + y, where y is the most significant digit of a(n) and
is the smallest such y, if such a y exists. If no such y exists, the sequence stops.
Since y is a leading digit it lies in 1..9 (y = 0 never works), so the search is over
1 ≤ y ≤ 9.

Starting from a(1) = 1 the sequence (A121805) has exactly 2137453 terms (W. Edwin Clark);
starting from 2 (A139284) it ends at a(194697747222394) = 9999999999999918 (G. Resta).

Conjecture (N. J. A. Sloane, Nov 14 2023, in the OEIS entry): this sequence is finite, for
any initial term. We state it for every positive initial term k (the source sequence is of
positive numbers): the comma-successor iteration started at k eventually has no successor.
For bases other than 10 see R. Dougherty-Bliss and N. Ter-Saakov, "The Comma Sequence is
Finite in Other Bases", arXiv:2408.03434; the base-10 statement below is the OEIS conjecture.
-/

namespace OMA.S_oeis_a121805

/-- Most significant decimal digit of `m` (0 for `m = 0`). -/
def leadDigit (m : ℕ) : ℕ := (Nat.digits 10 m).getLastD 0

/-- The candidate next term `x + 10 * (last digit of x) + y`. -/
def cand (x y : ℕ) : ℕ := x + 10 * (x % 10) + y

/-- Comma-successor of `x`: `cand x y` for the smallest `y ∈ {1,…,9}` that is the leading
digit of `cand x y`, or `none` if there is no such `y`. -/
def commaSucc (x : ℕ) : Option ℕ :=
  ((List.range' 1 9).find? (fun y => leadDigit (cand x y) == y)).map (cand x)

/-- `commaSeq k n` is the term `a(n+1)` of the comma sequence with `a(1) = k`,
or `none` once the sequence has stopped. -/
def commaSeq (k : ℕ) : ℕ → Option ℕ
  | 0 => some k
  | n + 1 => (commaSeq k n).bind commaSucc

/-- Conjecture (Sloane): for every positive initial term, the comma sequence is finite. -/
theorem main : ∀ k : ℕ, 0 < k → ∃ n : ℕ, commaSeq k n = none := by
  sorry

end OMA.S_oeis_a121805
