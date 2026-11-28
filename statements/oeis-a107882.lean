import Mathlib

/-!
# A107882: Column 1 of triangle A107880.

Source: https://oeis.org/A107882
Credit: @Solfanbtc

A107882 (offset 0) is determined by its g.f. identity
`1 = ∑_{k ≥ 0} a(k) x^k (1 - x)^(2 + k(k+1)/2)`. Comparing coefficients of `x^n`:
`a(0) = 1` and, for `n ≥ 1`, `a(n) = - ∑_{k < n} a(k) (-1)^(n-k) C(2 + k(k+1)/2, n - k)`,
which is the definition used below. Data: 1, 2, 5, 19, 104, 766, 7197, 82910, ...
(`#eval` of `a` reproduces the first 12 terms).

Conjecture (B. W. J. Irwin, 2016, in the entry): `a(n)` is given by nested sums,
`a(2) = ∑_{i=1}^{2} (i + 1)`, `a(3) = ∑_{i=1}^{2} ∑_{j=1}^{i+1} (j + 2)`,
`a(4) = ∑_{i=1}^{2} ∑_{j=1}^{i+1} ∑_{k=1}^{j+2} (k + 3)`, ..., i.e. in general
`a(n) = ∑_{x_1=1}^{2} ∑_{x_2=1}^{x_1+1} ⋯ ∑_{x_{n-1}=1}^{x_{n-2}+n-2} (x_{n-1} + n - 1)` for `n ≥ 2`.
With `N 0 j b = b` and `N (r+1) j b = ∑_{x=1}^{b} N r (j+1) (x + j)`, this nested sum is
`N (n - 1) 1 2`. `#eval` gives 5, 19, 104, 766, 7197, 82910, 1136923 for `n = 2, ..., 8`, as in
the data. (For `n = 1` the formula also gives `N 0 1 2 = 2 = a(1)`; the source starts at `n = 2`.)
-/

namespace OMA.S_oeis_a107882

/-- A107882, through the coefficient recurrence of its g.f. identity. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 1 else
    -∑ k : Fin n, a k * (-1) ^ (n - (k : ℕ)) * (Nat.choose (2 + (k : ℕ) * ((k : ℕ) + 1) / 2) (n - k) : ℤ)
termination_by n
decreasing_by exact k.isLt

/-- The nested sums: `r` summations left, offset `j`, current upper limit `b`. -/
def N : ℕ → ℕ → ℕ → ℕ
  | 0, _, b => b
  | r + 1, j, b => ∑ x ∈ Finset.Icc 1 b, N r (j + 1) (x + j)

/-- Irwin's conjecture: `a(n)` equals the nested sum, for `n ≥ 2`. -/
theorem main : ∀ n : ℕ, 2 ≤ n → a n = (N (n - 1) 1 2 : ℤ) := by
  sorry

end OMA.S_oeis_a107882
