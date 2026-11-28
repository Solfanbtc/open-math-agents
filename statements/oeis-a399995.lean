import Mathlib

/-!
# A399995: a(1) = 0. For n > 1, a(n) is the number of ways to write a(n-1) as the sum of two earlier terms with distinct positions in the sequence.

Source: https://oeis.org/A399995
Credit: @Solfanbtc

Conjecture (OEIS A399995, comment): many numbers, beginning with 5 and 9, never occur in
this sequence (see A397471).

A397471 ("Numbers not appearing in A399995", all terms conjectural) lists
5, 9, 23, 25, 32, 34, 39, 41, 42, 53, 60, 62, 69, 72, 75, 78, 79, 81, 90, 94, 96, 100, 104,
106, 109, 115, 116, 121, 130, 136, 141, 144, 152, 157, 162, 165, 175, 187, 188, 190, 192,
198, 199, 200, 204, 214, 216, 225, 226, 229, 231, 238, 242, 244, 248, 249, 262
(every term of its %S, %T, %U lines). The statement says that none of these numbers is a
term of A399995.

Conventions:
* `terms n` is the list `[a(1), ..., a(n+1)]`. The next term counts the pairs of positions
  `i < j` among all terms so far (the last term included, as in the examples
  a(3) = 1 since a(1) + a(2) = a(2)) whose values add up to the last term; this is the
  Python program of the entry.
* Evaluated with `#eval`: `terms 19` is 0, 0, 1, 2, 2, 4, 3, 4, 6, 6, 8, 7, 6, 10, 11, 6, 12,
  13, 10, 15, matching the data. In Python, none of the listed numbers occurs among the first
  30000 terms, and they are exactly the values <= 262 missing there.
-/

namespace OMA.S_oeis_a399995

/-- The number of pairs of positions `i < j` in `l` whose values sum to the last entry. -/
def nextTerm (l : List ℕ) : ℕ :=
  ((Finset.range l.length ×ˢ Finset.range l.length).filter fun p =>
    p.1 < p.2 ∧ l.getD p.1 0 + l.getD p.2 0 = l.getLast?.getD 0).card

/-- `terms n = [a(1), ..., a(n+1)]`. -/
def terms : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => terms n ++ [nextTerm (terms n)]

/-- A399995(n) for `n ≥ 1`. -/
def a (n : ℕ) : ℕ := (terms (n - 1)).getD (n - 1) 0

/-- The terms of A397471. -/
def missing : List ℕ :=
  [5, 9, 23, 25, 32, 34, 39, 41, 42, 53, 60, 62, 69, 72, 75, 78, 79, 81, 90, 94, 96, 100,
    104, 106, 109, 115, 116, 121, 130, 136, 141, 144, 152, 157, 162, 165, 175, 187, 188, 190,
    192, 198, 199, 200, 204, 214, 216, 225, 226, 229, 231, 238, 242, 244, 248, 249, 262]

/-- Conjecture: no number listed in A397471 is a term of A399995. -/
theorem main : ∀ v ∈ missing, ∀ n : ℕ, 1 ≤ n → a n ≠ v := by
  sorry

end OMA.S_oeis_a399995
