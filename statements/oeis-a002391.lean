import Mathlib

/-!
# A002391: Decimal expansion of natural logarithm of 3.

Source: https://oeis.org/A002391
Credit: @Solfanbtc

Conjecture (Mats Granvik, Jun 19 2011, in the entry's formulas):
`log(3) = ∑_{k ≥ 1} A191907(3, k) / k`, where A191907 is the square array
`T(n, k) = -(n - 1)` if `n ∣ k`, else `1`; so `T(3, k) = -2` if `3 ∣ k` and `1` otherwise, and the
series is `1 + 1/2 - 2/3 + 1/4 + 1/5 - 2/6 + ...`.

The entry A191907 records `∑_{k ≥ 1} T(n, k)/k = log(n)` as known (pointed out by Jaume Oliver
Lafont in A061347 and A002162); for `n = 3`, the partial sum up to `3N` is
`H_{3N} - 3 · (H_N / 3) = H_{3N} - H_N → log 3`. Stated here exactly as Granvik's conjecture.

Conventions:
* The series converges only conditionally (its terms are not absolutely summable), so the sum is
  the limit of the partial sums `∑_{k=1}^{N} T(3, k)/k` as `N → ∞` (not `HasSum`, which in `ℝ`
  would require absolute summability and is false here).
* A python3 check: the partial sum for `N = 3·10⁶` is `1.09861195...`, while
  `log 3 = 1.09861228...`.
-/

namespace OMA.S_oeis_a002391

open Filter Topology

/-- A191907: `T(n, k) = -(n - 1)` if `n ∣ k`, else `1`. -/
def T (n k : ℕ) : ℤ := if n ∣ k then -((n : ℤ) - 1) else 1

/-- Granvik's conjecture: `log 3 = ∑_{k ≥ 1} T(3, k) / k` (limit of partial sums). -/
theorem main :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (T 3 k : ℝ) / (k : ℝ)) atTop
      (𝓝 (Real.log 3)) := by
  sorry

end OMA.S_oeis_a002391
