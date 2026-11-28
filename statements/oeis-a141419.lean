import Mathlib

/-!
# A141419: Triangle T(n, k) = A000217(n) - A000217(n - k), 1 <= k <= n.

Source: https://oeis.org/A141419
Credit: @Solfanbtc

Conjecture (in the entry, L. E. Jeffery's comment): with N = 2n+1, U_r the Chebyshev
polynomials of the second kind (U_0 = 1, U_1 = 2x, U_r = 2x U_(r-1) - U_(r-2)), the column
vectors V_(k-1) = (U_(k-1)(cos(π/N)), U_(k-1)(cos(3π/N)), ..., U_(k-1)(cos((2n-1)π/N)))^T,
S_N = [V_0, ..., V_(n-1)] and X_N = S_N^T S_N, the row n of the triangle is the main diagonal
of X_N: T(n,k) = [X_N](k-1,k-1). As the entry remarks, this says exactly
T(n,k) = Σ_{m=1}^{n} U_(k-1)(cos((2m-1)π/N))^2 (the (k-1,k-1) entry of S_N^T S_N is the squared
norm of the column V_(k-1)); that identity is what is stated.

Conventions.
* A000217(m) = m(m+1)/2, so T(n,k) = n(n+1)/2 - (n-k)(n-k+1)/2 (natural numbers; exact).
* U_r is Mathlib's `Polynomial.Chebyshev.U ℝ r` (same recurrence and initial values).
* python3: the identity holds (to 1e-6) for all 1 ≤ k ≤ n ≤ 24.
-/

namespace OMA.S_oeis_a141419

/-- T(n, k) = A000217(n) - A000217(n - k). -/
def T (n k : ℕ) : ℕ := n * (n + 1) / 2 - (n - k) * (n - k + 1) / 2

theorem main : ∀ n k : ℕ, 1 ≤ k → k ≤ n →
    ∑ m ∈ Finset.Icc 1 n,
        ((Polynomial.Chebyshev.U ℝ ((k - 1 : ℕ) : ℤ)).eval
          (Real.cos ((2 * m - 1) * Real.pi / (2 * n + 1)))) ^ 2
      = (T n k : ℝ) := by
  sorry

end OMA.S_oeis_a141419
