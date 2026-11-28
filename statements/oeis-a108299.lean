import Mathlib

/-!
# A108299: `T(n,k) = binomial(n - ⌊(k+1)/2⌋, ⌊k/2⌋) (-1)^⌊(k+1)/2⌋`

Source: https://oeis.org/A108299
Credit: @Solfanbtc

Triangle (offset 0), `0 ≤ k ≤ n`: `T(n, k) = C(n - ⌊(k+1)/2⌋, ⌊k/2⌋) (-1)^⌊(k+1)/2⌋`;
rows `1; 1, -1; 1, -1, -1; 1, -1, -2, 1; …` (reproduces the data).

Conjecture (L. Edson Jeffery, Mar 12 2011, OEIS comment): let `N = 2n + 1` with `n > 2`. Then
`T(n, k)` (`0 ≤ k ≤ n`) gives the `k`-th coefficient in the characteristic function
`p_N(x) = 0`, of degree `n`, of the `n × n` tridiagonal unit-primitive matrix
`G_N = A_{N,1}`, which has `1`s on the super- and subdiagonal, `0`s on the diagonal except a `1`
in the last diagonal entry; its solutions are `φ_j = 2 cos((2j - 1)π/N)`, `j = 1, …, n`.
Example: `G_7 = ((0,1,0),(1,0,1),(0,1,1))`, `p(x) = x^3 - x^2 - 2x + 1`, `T(3, ·) = (1, -1, -2, 1)`:
the `k`-th coefficient is the one of `x^(n-k)` (`p_N` monic).

Stated, for `n > 2`, as the two parts of `main`: (1) the coefficient of `x^(n-k)` in the
characteristic polynomial of `G_N` is `T(n, k)` for `0 ≤ k ≤ n`; (2) over `ℝ` this polynomial is
`∏_{j=1}^{n} (x - 2 cos((2j - 1)π/N))`. (Python: (1) holds for `3 ≤ n < 25`.)
-/

namespace OMA.S_oeis_a108299

open Polynomial

/-- A108299: `T(n, k)`. -/
def T (n k : ℕ) : ℤ := (Nat.choose (n - (k + 1) / 2) (k / 2) : ℤ) * (-1) ^ ((k + 1) / 2)

/-- Jeffery's `n × n` matrix `G_N`, `N = 2n + 1`. -/
def G (n : ℕ) : Matrix (Fin n) (Fin n) ℤ := fun i j =>
  if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else if i = j ∧ (i : ℕ) = n - 1 then 1 else 0

/-- Jeffery's conjecture on the characteristic polynomial of `G_N`. -/
theorem main : ∀ n : ℕ, 2 < n →
    (∀ k ≤ n, (G n).charpoly.coeff (n - k) = T n k) ∧
    ((G n).map (Int.cast : ℤ → ℝ)).charpoly =
      ∏ j ∈ Finset.range n,
        (X - C (2 * Real.cos ((2 * ((j : ℝ) + 1) - 1) * Real.pi / (2 * n + 1)))) := by
  sorry

end OMA.S_oeis_a108299
