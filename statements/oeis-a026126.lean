import Mathlib

/-!
# A026126: Nonnegative paths from 1 to 5, first step ±1, later steps in {-1, 0, 1}.

Source: https://oeis.org/A026126
Credit: @Solfanbtc

a(n) = number of (s(0), s(1), ..., s(n)) such that every s(i) is a nonnegative integer,
s(0) = 1, s(n) = 5, |s(1) - s(0)| = 1, |s(i) - s(i-1)| <= 1 for i >= 2 (offset 4).

Conjecture (R. J. Mathar, Jun 10 2013, in the entry):
-(n+8)(n-4) a(n) + (4n^2+5n-73) a(n-1) + (-2n^2+13n+38) a(n-2) - (4n+5)(n-3) a(n-3)
  + 3(n-3)(n-4) a(n-4) = 0.

Conventions.
* `count n v` = number of such strings s(0..n) with s(n) = v (0 for v < 0, which enforces
  nonnegativity at every step), and a(n) = count n 5. Checked with python3: all 26 listed
  terms (n = 4..29).
* With offset 4 the recurrence involves a(n-4), so it is stated for n ≥ 8 (all indices ≥ 4);
  checked for 8 ≤ n < 80 (it also holds for n = 4..7, where count n 5 = 0 below the offset).
-/

namespace OMA.S_oeis_a026126

/-- Number of admissible strings s(0..n) with s(n) = v. -/
def count : ℕ → ℤ → ℕ
  | 0, v => if v = 1 then 1 else 0
  | 1, v => if v < 0 then 0 else count 0 (v - 1) + count 0 (v + 1)
  | n + 2, v => if v < 0 then 0 else count (n + 1) (v - 1) + count (n + 1) v + count (n + 1) (v + 1)

/-- A026126 (offset 4). -/
def a (n : ℕ) : ℕ := count n 5

theorem main : ∀ n : ℕ, 8 ≤ n →
    -((n : ℤ) + 8) * ((n : ℤ) - 4) * a n + (4 * (n : ℤ) ^ 2 + 5 * n - 73) * a (n - 1)
      + (-2 * (n : ℤ) ^ 2 + 13 * n + 38) * a (n - 2)
      - (4 * (n : ℤ) + 5) * ((n : ℤ) - 3) * a (n - 3)
      + 3 * ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026126
