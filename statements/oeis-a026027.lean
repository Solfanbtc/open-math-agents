import Mathlib

/-!
# A026027: Nonnegative ±1 paths of length 2n-1 from 3 to 6.

Source: https://oeis.org/A026027
Credit: @Solfanbtc

a(n) = number of (s(0), s(1), ..., s(2n-1)) such that s(i) is a nonnegative integer and
|s(i) - s(i-1)| = 1, s(0) = 3, s(2n-1) = 6 (offset 2).

Conjecture (R. J. Mathar, Jun 22 2013, in the entry):
(13n+118)(n+5) a(n) + (13n^2-969n-3490) a(n-1) + 2(-203n^2+1080n+758) a(n-2)
  + 4(73n-182)(2n-5) a(n-3) = 0.

Conventions.
* The name says "|s(i) - s(i-1)| = 1 for i = 1,2,...,n"; with only n constrained steps out of
  2n-1 the other steps would be unconstrained, which contradicts the data. The intended
  condition is for i = 1, ..., 2n-1 (all steps): a brute-force count with all steps ±1 gives
  1, 5, 21, 84, 329, 1274, 4900 for n = 2..8, matching the data, and the entry's formula
  C(2n-1, n-2) - C(2n-1, n-6) (reflection principle) matches all 24 listed terms.
* Paths are encoded by their steps `d : Fin (2n-1) → Bool` (true = up); the height after the
  first j steps is 3 + #ups - #downs among them, and must be ≥ 0 for every j.
* With offset 2 the recurrence involves a(n-3), so it is stated for n ≥ 5 (all indices ≥ 2).
  Checked with python3 for 5 ≤ n < 80 (it also holds for n = 3, 4 with a(0) = a(1) = 0).
-/

namespace OMA.S_oeis_a026027

/-- Height after the first `j` steps, starting at 3. -/
def height {m : ℕ} (d : Fin m → Bool) (j : ℕ) : ℤ :=
  3 + ∑ i : Fin m, if i.val < j then (if d i then (1 : ℤ) else -1) else 0

/-- A026027. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun d : Fin (2 * n - 1) → Bool =>
    (∀ j : ℕ, j ≤ 2 * n - 1 → 0 ≤ height d j) ∧ height d (2 * n - 1) = 6).card

theorem main : ∀ n : ℕ, 5 ≤ n →
    (13 * (n : ℤ) + 118) * (n + 5) * a n + (13 * (n : ℤ) ^ 2 - 969 * n - 3490) * a (n - 1)
      + 2 * (-203 * (n : ℤ) ^ 2 + 1080 * n + 758) * a (n - 2)
      + 4 * (73 * (n : ℤ) - 182) * (2 * n - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026027
