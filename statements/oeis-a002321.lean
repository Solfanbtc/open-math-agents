import Mathlib

/-!
# A002321: Mertens's function: Sum_{k=1..n} mu(k), where mu is the Moebius function A008683.

Source: https://oeis.org/A002321
Credit: @Solfanbtc

Conjecture (OEIS A002321): `a(n) + 2 = A192763(n,1)` for `n > 1`, and `= A192763(1,n)` for `n > 1`.

A192763 is the symmetric square array `T(n,k)` (`n, k ≥ 1`) defined by the PARI program of
Michael Somos in that entry:
```
T(n, k) = if( n<1 || k<1, 0, if( k>n, T(k, n), if( k==1, if( n<3, n,
  (-T(n-1, 1) - sum( i=2, n-1, T(n, i))) / (n+1) + T(n-1, 1)),
  if( n>k, T(k, (n-1)%k+1), -sum( i=1, n-1, T(n, i))))))
```
PARI divides exactly, so the array is taken with values in `ℚ`. These equations determine `T`
uniquely on `n, k ≥ 1` (the PARI recursion terminates), so we state the conjecture for every
`T : ℕ → ℕ → ℚ` satisfying them. Checked numerically for `n < 400`.
-/

namespace OMA.S_oeis_a002321

/-- Mertens's function `M(n) = ∑_{k=1}^n μ(k)` (A002321). -/
def mertens (n : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.moebius k

/-- `T` satisfies the defining recurrence of A192763 (the PARI program), for indices `≥ 1`. -/
def IsA192763 (T : ℕ → ℕ → ℚ) : Prop :=
  (∀ n k, 1 ≤ n → n < k → T n k = T k n) ∧
  T 1 1 = 1 ∧ T 2 1 = 2 ∧
  (∀ n, 3 ≤ n → T n 1 =
    (-T (n - 1) 1 - ∑ i ∈ Finset.Icc 2 (n - 1), T n i) / ((n : ℚ) + 1) + T (n - 1) 1) ∧
  (∀ n k, 2 ≤ k → k < n → T n k = T k ((n - 1) % k + 1)) ∧
  (∀ n, 2 ≤ n → T n n = -∑ i ∈ Finset.Icc 1 (n - 1), T n i)

theorem main : ∀ T : ℕ → ℕ → ℚ, IsA192763 T → ∀ n : ℕ, 1 < n →
    (mertens n : ℚ) + 2 = T n 1 ∧ (mertens n : ℚ) + 2 = T 1 n := by
  sorry

end OMA.S_oeis_a002321
