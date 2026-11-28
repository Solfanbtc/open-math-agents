import Mathlib

/-!
# A053599: Subsequences of 1..n with palindromic difference sequence

Source: https://oeis.org/A053599
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of nonempty subsequences `s(1) < ⋯ < s(r)` of `1, …, n` whose
difference sequence `(s(2) - s(1), …, s(r) - s(r-1))` is a palindrome: `1, 3, 7, 13, 23, …`
(for `n = 4`: `1, 2, 3, 4, 12, 13, 14, 23, 24, 34, 123, 234, 1234`). A subsequence is a nonempty
subset of `{1, …, n}`, listed increasingly (`Finset.sort`). A brute-force count with this
definition gives the first 14 data terms.

Conjecture (Clark Kimberling, Sep 27 2022, OEIS comment): let `b(n)` be the number of subsets `S`
of `{1, 2, …, n}` having more than one element such that (sum of the least two elements of `S`)
`> max(S)`. Then `b(0) = b(1) = 0` and `b(n+2) = a(n+1)` for `n ≥ 0`. (Python: holds for
`n < 14`; `b(0) = b(1) = 0` is immediate.)
-/

namespace OMA.S_oeis_a053599

/-- Difference sequence of a list. -/
def diffs : List ℕ → List ℤ
  | x :: y :: l => ((y : ℤ) - x) :: diffs (y :: l)
  | _ => []

/-- A053599: nonempty subsets of `{1, …, n}` whose increasing difference sequence is a palindrome. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun S =>
    S.Nonempty ∧ (diffs (S.sort (· ≤ ·))).reverse = diffs (S.sort (· ≤ ·))).card

/-- `b(n)`: subsets of `{1, …, n}` with at least two elements whose two least elements sum to more
than the maximum. -/
def b (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter fun S =>
    2 ≤ S.card ∧ ((S.sort (· ≤ ·)).getD 0 0 + (S.sort (· ≤ ·)).getD 1 0 > S.sup id)).card

/-- Kimberling's conjecture. -/
theorem main : b 0 = 0 ∧ b 1 = 0 ∧ ∀ n : ℕ, b (n + 2) = a (n + 1) := by
  sorry

end OMA.S_oeis_a053599
