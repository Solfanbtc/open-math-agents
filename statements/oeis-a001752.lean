import Mathlib

/-!
# A001752: Expansion of 1/((1+x)*(1-x)^5).

Source: https://oeis.org/A001752
Credit: @Solfanbtc

Conjecture (Stefano Spezia, Jan 12 2022): for `n > 2`, `a(n-3)` is the absolute value of the
coefficient of `x^(n-2)` in the characteristic polynomial of the `n × n` matrix `M(n)`, the
`n`-th principal submatrix of the array A010751, `M[i,j] = floor((j - i + 1)/2)`.

Conventions. `a(n)` is the coefficient of `x^n` in the power series `1/((1+x)(1-x)^5)` over
`ℚ` (offset 0). Indices of `M(n)` run over `Fin n`; only `j - i` matters, so starting at `0`
or `1` gives the same matrix. The floor is `Int.fdiv`. Mathlib's `charpoly` is
`det(X I - M)`; the absolute value makes the sign convention irrelevant.
Check (python3, `n = 3..19`): the coefficient is `Σ_{i<j} (M_ii M_jj - M_ij M_ji)`, giving
`1, 4, 11, 24, 46, ..., 2685`, the first 17 data terms.
-/

namespace OMA.S_oeis_a001752

/-- A001752(n): coefficient of `x^n` in `1/((1+x)(1-x)^5)`. -/
noncomputable def a (n : ℕ) : ℚ :=
  PowerSeries.coeff n ((1 + PowerSeries.X) * (1 - PowerSeries.X) ^ 5 : PowerSeries ℚ)⁻¹

/-- The `n`-th principal submatrix of A010751: `M[i,j] = floor((j - i + 1)/2)`. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => Int.fdiv ((j : ℤ) - (i : ℤ) + 1) 2

/-- Spezia's conjecture. -/
theorem main : ∀ n : ℕ, 2 < n →
    (|((M n).charpoly.coeff (n - 2))| : ℚ) = a (n - 3) := by
  sorry

end OMA.S_oeis_a001752
