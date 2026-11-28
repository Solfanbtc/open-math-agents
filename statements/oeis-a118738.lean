import Mathlib

/-!
# A118738: Number of ones in binary expansion of 5^n.

Source: https://oeis.org/A118738
Credit: @Solfanbtc

Conjecture (M. F. Hasler, Apr 17 2024, comment in A118738):
`a(n)/n → log_4(5) = 1.160964...` as `n → ∞`.

Formalization.
* `a n` is the number of ones in the binary expansion of `5^n` (its Hamming weight,
  `(Nat.digits 2 (5^n)).count 1`), offset 0 as in OEIS.
* `log_4(5) = log 5 / log 4` (`Real.logb 4 5`); it is half the bit length rate `log_2 5` of `5^n`.

Checked with python3: the Hamming weight of `5^n` reproduces all listed %S/%T/%U terms
`1, 2, 3, 6, 5, 6, 7, 8, 12, ...` (`n ≤ 71`).
-/

namespace OMA.S_oeis_a118738

open Filter Topology

/-- A118738: the number of ones in the binary expansion of `5^n`. -/
def a (n : ℕ) : ℕ := (Nat.digits 2 (5 ^ n)).count 1

/-- Hasler's conjecture: `a(n)/n → log_4 5`. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (Real.logb 4 5)) := by
  sorry

end OMA.S_oeis_a118738
