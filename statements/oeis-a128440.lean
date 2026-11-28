import Mathlib

/-!
# A128440: Array T(n,k) = floor(k*r^n) where r = golden ratio = (1 + sqrt(5))/2, read by descending antidiagonals.

Source: https://oeis.org/A128440
Credit: @Solfanbtc

Conjectures (Clark Kimberling, Nov 11 and Nov 13 2022, comments in A128440):
1. rows `2n-1` and `2n` are disjoint for every positive integer `n`;
2. (stronger) for any positive integer `n`, if the numbers in rows `2n-1` and `2n` are jointly
   arranged in increasing order, and each number is replaced by its position in the ordering,
   then the resulting two rows are identical to the first two rows.

Definitions.
* `T(n, k) = ⌊k φ^n⌋`, `φ = (1 + √5)/2` (`Real.goldenRatio`), `n, k ≥ 1`. Rows 1 and 2 are the
  lower and upper Wythoff sequences, which partition the positive integers.
* Row `m` is `{T(m, k) | k ≥ 1}`. The position of `x` in the joint increasing arrangement of
  rows `2n-1` and `2n` is the number of elements of their union that are `≤ x` (1-based;
  finite, as the rows are increasing and unbounded).
* Conjecture 2 says: for every `k ≥ 1`, the position of `T(2n-1, k)` is `T(1, k)` and the
  position of `T(2n, k)` is `T(2, k)`. Both conjectures are stated, joined by `∧`.

Checked with python3 (exact integer arithmetic via `T(n,k) = k F(n-1) + ⌊k F(n) φ⌋`, a formula
in the entry): the array reproduces all listed %S/%T/%U terms, and both conjectures hold for
`1 ≤ n ≤ 8`, `k ≤ 3000` (positions compared below the smaller of the two row maxima).
-/

namespace OMA.S_oeis_a128440

/-- `T(n, k) = ⌊k φ^n⌋`. -/
noncomputable def T (n k : ℕ) : ℕ := ⌊(k : ℝ) * Real.goldenRatio ^ n⌋₊

/-- Row `m` of the array. -/
def row (m : ℕ) : Set ℕ := {x | ∃ k : ℕ, 1 ≤ k ∧ x = T m k}

/-- The position of `x` in the joint increasing arrangement of rows `2n-1` and `2n`. -/
noncomputable def pos (n x : ℕ) : ℕ := {y | y ∈ row (2 * n - 1) ∪ row (2 * n) ∧ y ≤ x}.ncard

/-- Kimberling's two conjectures. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → Disjoint (row (2 * n - 1)) (row (2 * n))) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ k : ℕ, 1 ≤ k →
      pos n (T (2 * n - 1) k) = T 1 k ∧ pos n (T (2 * n) k) = T 2 k) := by
  sorry

end OMA.S_oeis_a128440
