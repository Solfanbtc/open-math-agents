import Mathlib

/-!
# A065713: Sum of digits of 4^n.

Source: https://oeis.org/A065713
Credit: @Solfanbtc

`a(n)` is the sum of the decimal digits of `4^n`: 1, 4, 7, 10, 13, 7, 19, ….

Conjecture (M. F. Hasler, 2017): `a(n) ~ 9 log_10(2) n`, i.e. `a(n) / n → 9 log 2 / log 10`
(heuristically: `4^n` has about `2 n log_10 2` digits, of average value 4.5). The proved lower
bound `a(n) > log_4(n) + 1/2` mentioned in the entry is much weaker. Checked with python3:
`a(n) / (9 log_10(2) n)` is 0.945 at `n = 100` and 0.998 at `n = 1000`.
-/

namespace OMA.S_oeis_a065713

open Filter Topology

/-- A065713(n): the decimal digit sum of `4^n`. -/
def a (n : ℕ) : ℕ := (Nat.digits 10 (4 ^ n)).sum

/-- Hasler's conjecture: `a(n) ~ 9 log_10(2) n`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (9 * Real.logb 10 2)) := by
  sorry

end OMA.S_oeis_a065713
