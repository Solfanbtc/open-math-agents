import Mathlib

/-!
# A026013: Nonnegative ±1 paths of length 2n from 2 to 4.

Source: https://oeis.org/A026013
Credit: @Solfanbtc

a(n) = number of (s(0), s(1), ..., s(2n)) such that s(i) is a nonnegative integer and
|s(i) - s(i-1)| = 1, s(0) = 2, s(2n) = 4 (offset 1).

Conjecture (R. J. Mathar, Nov 13 2012, in the entry):
(n+4)(n+1) a(n) - 4(n^2+4n+6) a(n-1) + 4(2n-3) a(n-2) = 0.

Conventions.
* The name says "|s(i) - s(i-1)| = 1 for i = 1,2,...,n"; with only n of the 2n steps
  constrained this contradicts the data. The intended condition is for all steps i = 1..2n: a
  brute-force count with all steps ±1 gives 1, 4, 15, 55, 200, 726, 2639, 9620 (n = 1..8),
  matching the data, and the entry's formula C(2n, n-1) - C(2n, n-4) (reflection principle)
  matches all 25 listed terms.
* Paths are encoded by their steps `d : Fin (2n) → Bool` (true = up); the height after the
  first j steps is 2 + #ups - #downs among them and must be ≥ 0 for every j.
* With offset 1 the recurrence involves a(n-2), so it is stated for n ≥ 3 (all indices ≥ 1);
  checked with python3 for 3 ≤ n < 80 (it also holds at n = 2 with a(0) = 0).
-/

namespace OMA.S_oeis_a026013

/-- Height after the first `j` steps, starting at 2. -/
def height {m : ℕ} (d : Fin m → Bool) (j : ℕ) : ℤ :=
  2 + ∑ i : Fin m, if i.val < j then (if d i then (1 : ℤ) else -1) else 0

/-- A026013. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun d : Fin (2 * n) → Bool =>
    (∀ j : ℕ, j ≤ 2 * n → 0 ≤ height d j) ∧ height d (2 * n) = 4).card

theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 4) * ((n : ℤ) + 1) * a n - 4 * ((n : ℤ) ^ 2 + 4 * n + 6) * a (n - 1)
      + 4 * (2 * (n : ℤ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a026013
