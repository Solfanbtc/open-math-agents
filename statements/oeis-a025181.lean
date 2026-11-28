import Mathlib

/-!
# A025181: Integer paths from 0 to 3, first step ±1, later steps in {-1, 0, 1}.

Source: https://oeis.org/A025181
Credit: @Solfanbtc

a(n) = number of (s(0), s(1), ..., s(n)) such that s(i) is an integer, s(0) = 0, |s(1)| = 1,
|s(i) - s(i-1)| <= 1 for i >= 2, s(n) = 3 (offset 3).

Two conjectures (R. J. Mathar, Feb 25 2015, in the entry):
1. (n+3) a(n) + (-5n-7) a(n-1) + (3n-7) a(n-2) + (11n-7) a(n-3) + 4(-n+6) a(n-4)
   + 6(-n+5) a(n-5) = 0;
2. -(n+3)(n-3)(4n^2-12n+17) a(n) + (n-1)(8n^3-20n^2+30n-81) a(n-1)
   + 3(n-1)(n-2)(4n^2-4n+9) a(n-2) = 0.
`main` is their conjunction.

Conventions.
* `count n v` = number of such strings s(0..n) with s(n) = v (no sign restriction), and
  a(n) = count n 3. Checked with python3: all 27 listed terms (n = 3..29).
* With offset 3, recurrence 1 (involving a(n-5)) is stated for n ≥ 8 and recurrence 2
  (involving a(n-2)) for n ≥ 5, so that all indices are ≥ 3; both checked for n < 80 (they
  also hold below these ranges with count n 3 = 0 for n < 3).
-/

namespace OMA.S_oeis_a025181

/-- Number of admissible strings s(0..n) with s(n) = v. -/
def count : ℕ → ℤ → ℕ
  | 0, v => if v = 0 then 1 else 0
  | 1, v => count 0 (v - 1) + count 0 (v + 1)
  | n + 2, v => count (n + 1) (v - 1) + count (n + 1) v + count (n + 1) (v + 1)

/-- A025181 (offset 3). -/
def a (n : ℕ) : ℕ := count n 3

theorem main :
    (∀ n : ℕ, 8 ≤ n →
      ((n : ℤ) + 3) * a n + (-5 * (n : ℤ) - 7) * a (n - 1) + (3 * (n : ℤ) - 7) * a (n - 2)
        + (11 * (n : ℤ) - 7) * a (n - 3) + 4 * (-(n : ℤ) + 6) * a (n - 4)
        + 6 * (-(n : ℤ) + 5) * a (n - 5) = 0) ∧
    (∀ n : ℕ, 5 ≤ n →
      -((n : ℤ) + 3) * ((n : ℤ) - 3) * (4 * (n : ℤ) ^ 2 - 12 * n + 17) * a n
        + ((n : ℤ) - 1) * (8 * (n : ℤ) ^ 3 - 20 * n ^ 2 + 30 * n - 81) * a (n - 1)
        + 3 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (4 * (n : ℤ) ^ 2 - 4 * n + 9) * a (n - 2) = 0) := by
  sorry

end OMA.S_oeis_a025181
