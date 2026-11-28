import Mathlib

/-!
# A078121: the lower triangular matrix M with M^2 = M shifted by one row and column

Source: https://oeis.org/A078121
Credit: @Solfanbtc

A078121 is the infinite lower triangular matrix `M` (rows and columns indexed from 0) with
`[M^2](i, j) = M(i+1, j+1)` for all `i, j ≥ 0`, first column `M(k, 0) = 1` and diagonal
`M(k, k) = 1` (the name writes `M(0,k) = 1`, but the data and examples have the ones in
column 0: rows 1; 1, 1; 1, 2, 1; 1, 4, 4, 1; 1, 10, 16, 8, 1; ...).
Since `M` is lower triangular, `[M^2](i, j) = ∑_{t ≤ i} M(i, t) M(t, j)`, and these conditions
determine `M` uniquely (row `i + 1` is computed from rows `≤ i`); conversely the matrix so
computed satisfies them, so the statement below is not vacuous.

Conjecture (entry, formula section): `M(n, k)` is the coefficient of `x^(2^n - 2^(n-k))` in the
power series expansion of `1/∏_{j=0..n-k} (1 - x^(2^j))`, whenever `0 ≤ k < n`.
We state it for every matrix `M : ℕ → ℕ → ℕ` with the defining properties.

Sanity check (python): the formula agrees with all 33 listed entries with `0 ≤ k < n`.
-/

namespace OMA.S_oeis_a078121

open PowerSeries

/-- The coefficient of `x^N` in `1/∏_{j=0..J} (1 - x^(2^j))`. -/
noncomputable def coeffBinary (N J : ℕ) : ℚ :=
  coeff N (∏ j ∈ Finset.range (J + 1), (1 - (X : PowerSeries ℚ) ^ (2 ^ j)))⁻¹

/-- The conjecture, for every matrix satisfying the defining properties of A078121. -/
theorem main : ∀ M : ℕ → ℕ → ℕ,
    (∀ i j, i < j → M i j = 0) → (∀ k, M k 0 = 1) → (∀ k, M k k = 1) →
    (∀ i j, ∑ t ∈ Finset.range (i + 1), M i t * M t j = M (i + 1) (j + 1)) →
    ∀ n k, k < n → (M n k : ℚ) = coeffBinary (2 ^ n - 2 ^ (n - k)) (n - k) := by
  sorry

end OMA.S_oeis_a078121
