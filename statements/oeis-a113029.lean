import Mathlib

/-!
# A113029: a(1) = 2, a(2) = 3; for n > 2, a(n) = least prime equal to the sum of two or more previous terms.

Source: https://oeis.org/A113029
Credit: @Solfanbtc

Claim (Robert G. Wilson v, Apr 08 2007, May 05 2007, comment in A113029): except for 17, which
uses all 4 of the previous terms (`17 = 2 + 3 + 5 + 7`), all the other terms use only two or
three of the previous terms, i.e. every term `a(n)`, `n > 2`, `a(n) ≠ 17`, is the sum of two or
three distinct earlier terms. The comment says "so far"; it is stated here for all terms.

Formalization.
* "Sum of two or more previous terms": the sum of a set of at least two distinct earlier terms
  (the Mathematica program sums subsets of the list). `a(n)` is the least prime that is such a
  sum and is not already a term (the program's `!MemberQ`; e.g. `5 = 2 + 3` is a sum of earlier
  terms when `a(4)` is chosen, but `a(4) = 7`).
* `pre n = [a(1), ..., a(n)]`; the step is defined with classical choice (`Nat.find`), with
  the junk value `0` if no such prime existed (it always exists: by C. R. Greathouse IV's
  argument in the entry, `a(n) = prime(n + 3)` for `n > 6`).
* `a n` is the OEIS `a(n)` (offset 1).

Checked with python3: the rule gives `2, 3, 5, 7, 17, 19, 29, 31, ...`, all listed terms, and
every term below 20000 other than 17 is a sum of two or three distinct earlier terms (17 is the
only exception).
-/

namespace OMA.S_oeis_a113029

open Classical in
/-- The next term after the list `l` of terms: the least prime not in `l` that is the sum of a
set of at least two distinct terms of `l` (`0` if there is none). -/
noncomputable def nextTerm (l : List ℕ) : ℕ :=
  if h : ∃ p : ℕ, p.Prime ∧ p ∉ l ∧ ∃ s ⊆ l.toFinset, 2 ≤ s.card ∧ ∑ x ∈ s, x = p
  then Nat.find h else 0

/-- `pre n = [a(1), ..., a(n)]`. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => []
  | 1 => [2]
  | 2 => [2, 3]
  | n + 3 => pre (n + 2) ++ [nextTerm (pre (n + 2))]

/-- A113029 (offset 1). -/
noncomputable def a (n : ℕ) : ℕ := (pre n).getD (n - 1) 0

/-- Every term `a(n)`, `n > 2`, other than 17 is the sum of two or three distinct earlier terms. -/
theorem main : ∀ n : ℕ, 3 ≤ n → a n ≠ 17 →
    ∃ s : Finset ℕ, s ⊆ (pre (n - 1)).toFinset ∧ (s.card = 2 ∨ s.card = 3) ∧
      ∑ x ∈ s, x = a n := by
  sorry

end OMA.S_oeis_a113029
