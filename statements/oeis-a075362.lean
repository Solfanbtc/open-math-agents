import Mathlib

/-!
# A075362: Triangle read by rows with the n-th row containing the first n multiples of n.

Source: https://oeis.org/A075362
Credit: @Solfanbtc

`T(n, k) = n * k` for `1 ≤ k ≤ n` (%F, Zumkeller).

Conjecture (OEIS entry, %C, L. Edson Jeffery, 2012): with `N = 2n` and `U_r` the Chebyshev
polynomials of the second kind (`U_0 = 1`, `U_1 = 2x`, `U_r = 2x U_{r-1} - U_{r-2}`), row `n` of
the triangle is the main diagonal of `X_N = S_N^T S_N`, where `S_N` is the `n × n` matrix whose
column `k - 1` is `V_{k-1} = (U_{k-1}(cos(π/N)), U_{k-1}(cos(3π/N)), …, U_{k-1}(cos((2n-1)π/N)))^T`;
"hence `T(n,k)` is the sum of squares
`T(n,k) = sum[m=1,...,n (U_(k-1)(cos((2*m-1)*Pi/N)))^2] = [V_(k-1)]^T*V_(k-1)`".

The diagonal entry `[X_N]_(k-1,k-1)` is by definition `V_{k-1}^T V_{k-1}`, so the content of the
conjecture is the identity, for `1 ≤ k ≤ n`,
`∑_{m=1}^{n} U_{k-1}(cos((2m-1)π/(2n)))^2 = n k`.
(The interpretation of `V_{k-1}` as the spectrum of Jeffery's unit-primitive matrices is a remark,
not part of the identity.) The range `k ≤ n` matters: for `n = 3` the sums for `k = 4, 5` are
`6, 3`, not `12, 15`. Checked numerically in Python for all `1 ≤ k ≤ n < 30`.

`U_r` is Mathlib's `Polynomial.Chebyshev.U ℝ r` (indexed by `ℤ`), with the same recurrence.
-/

namespace OMA.S_oeis_a075362

open Polynomial

/-- The entry `T(n, k) = n * k` of the triangle. -/
def T (n k : ℕ) : ℕ := n * k

/-- Jeffery's conjecture: `T(n, k) = ∑_{m=1}^{n} U_{k-1}(cos((2m-1)π/(2n)))^2` for `1 ≤ k ≤ n`. -/
theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    ((T n k : ℕ) : ℝ) = ∑ m ∈ Finset.Icc 1 n,
      ((Chebyshev.U ℝ ((k : ℤ) - 1)).eval
        (Real.cos ((2 * (m : ℝ) - 1) * Real.pi / (2 * (n : ℝ))))) ^ 2 := by
  sorry

end OMA.S_oeis_a075362
