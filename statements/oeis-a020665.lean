import Mathlib

/-!
# A020665: a(n) is the (conjectured) maximal exponent k such that n^k does not contain a digit zero in its decimal expansion.

Source: https://oeis.org/A020665
Credit: @Solfanbtc

The entry lists conjectured values (M. F. Hasler, Mar 08 2014: most of them are not proved
rigorously, the search has been pushed to about 10^9 or beyond for many n). The conjecture is
that every listed value is the true maximal exponent: for each listed n (offset 2, so the 79
terms of %S/%T/%U are n = 2, ..., 80), a(n) is the greatest k such that the decimal expansion of
n^k has no digit 0. The exponent k = 0 always qualifies (n^0 = 1), so the set is never empty and
a(n) = 0 means that every n^k with k >= 1 contains a 0.

The value for n = 2 alone (86) is also stated in statements/oeis-a007377.lean; this statement is
the conjunction over all 79 listed values. Checked numerically: each listed n^a(n) is zeroless
and n^k contains a 0 for a(n) < k < 2000.
-/

namespace OMA.S_oeis_a020665

/-- The 79 listed terms a(2), ..., a(80). -/
def terms : List ℕ :=
  [86, 68, 43, 58, 44, 35, 27, 34, 0, 41, 26, 14, 34, 27, 19, 27, 17, 44, 0, 13, 22, 10, 13,
   29, 15, 9, 16, 14, 0, 16, 7, 23, 5, 17, 22, 16, 10, 19, 0, 9, 13, 10, 6, 39, 7, 8, 19, 5, 0,
   19, 18, 7, 13, 11, 23, 7, 23, 14, 0, 16, 5, 14, 12, 3, 14, 14, 14, 12, 0, 8, 22, 6, 4, 19,
   11, 12, 10, 9, 0]

theorem main : ∀ i : ℕ, i < terms.length →
    IsGreatest {k : ℕ | 0 ∉ Nat.digits 10 ((i + 2) ^ k)} (terms.getD i 0) := by
  sorry

end OMA.S_oeis_a020665
