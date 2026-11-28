import Mathlib

/-!
# A026165: Nonnegative paths from 2 with first step ±1 and later steps in {-1, 0, 1}.

Source: https://oeis.org/A026165
Credit: @Solfanbtc

a(n) = number of (s(0), s(1), ..., s(n)) such that every s(i) is a nonnegative integer,
s(0) = 2, |s(1) - s(0)| = 1, |s(i) - s(i-1)| <= 1 for i >= 2 (offset 0; the endpoint is free).

Conjecture (R. J. Mathar, Jun 23 2013, in the entry):
(n+3) a(n) + (-5n-9) a(n-1) + (5n+1) a(n-2) + 5(n-1) a(n-3) + 6(-n+3) a(n-4) = 0.

Conventions.
* `count n v` is the number of such strings s(0..n) with s(n) = v (0 for v < 0); every path
  stays in [0, n+2], so a(n) = Σ_{v=0}^{n+2} count n v. Checked with python3: this reproduces
  all 27 listed terms (n = 0..26).
* The recurrence involves a(n-4), so it is stated for n ≥ 4 (all indices ≥ 0); checked for
  4 ≤ n < 80.
-/

namespace OMA.S_oeis_a026165

/-- Number of admissible strings s(0..n) with s(n) = v. -/
def count : ℕ → ℤ → ℕ
  | 0, v => if v = 2 then 1 else 0
  | 1, v => if v < 0 then 0 else count 0 (v - 1) + count 0 (v + 1)
  | n + 2, v => if v < 0 then 0 else count (n + 1) (v - 1) + count (n + 1) v + count (n + 1) (v + 1)

/-- A026165. -/
def a (n : ℕ) : ℕ := ∑ v ∈ Finset.range (n + 3), count n v

theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 3) * a n + (-5 * (n : ℤ) - 9) * a (n - 1) + (5 * (n : ℤ) + 1) * a (n - 2)
      + 5 * ((n : ℤ) - 1) * a (n - 3) + 6 * (-(n : ℤ) + 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026165
