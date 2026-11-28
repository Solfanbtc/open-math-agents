import Mathlib

/-!
# A113413: A Riordan array of coordination sequences.

Source: https://oeis.org/A113413 (and https://oeis.org/A137513)
Credit: @Solfanbtc

`T(n, k)` (rows `n ≥ 0`, `0 ≤ k ≤ n`) is the Riordan array `((1+x)/(1-x), x(1+x)/(1-x))`:
`T(n, k) = [x^n] (1+x)/(1-x) · (x(1+x)/(1-x))^k`. Rows: 1; 2, 1; 2, 4, 1; 2, 8, 6, 1; ...
(this reproduces every listed term of %S, %T, %U, checked in Python).

A137513 is the triangle of coefficients of the Mittag-Leffler polynomials `M(m, t)`
(`M(0,t) = 1, M(1,t) = 2t, M(2,t) = 4t^2, M(3,t) = 4t + 8t^3, ...`). We use the explicit form
`M(m, t) = Σ_{j=0..m} C(m, j) 2^j (m-1)^{(m-j)} t^{(j)}` (falling factorials; the formula of the
entry's Mathematica/Sage programs, equal to `(m-1)! Σ_{j=1..m} j 2^j C(m,j) C(t,j)` from %F),
which reproduces every listed term of A137513.

Indexing of `A137513(r, c)` in the conjecture: rows and columns are counted from 1 (the entry has
offset 1), so `A137513(r, c)` is the coefficient of `t^(c-1)` in `M(r-1, t)`. This is the only
reading under which the formula holds even for `k = 0` (`T(n, 0) = 2` needs `A137513(2, 2) = 2`,
the `t^1` coefficient of `M(1,t) = 2t`; the 0-based reading gives `4`). With it the formula
holds for all `0 ≤ k < n ≤ 15` (checked in Python); it fails for `k = n` (e.g. `n = k = 1`
gives `0 ≠ 1`), which is why the source restricts to `k < n`.

Conjecture (W. Schulte, 2022): for `0 ≤ k < n`,
`T(n, k) = (Σ_{i=2..k+2} A137513(k+2, i) (n-k)^(i-2)) / k!`.
-/

namespace OMA.S_oeis_a113413

open PowerSeries Polynomial

/-- `(1+x)/(1-x)` as a power series over `ℤ`. -/
noncomputable def f : PowerSeries ℤ := (1 + PowerSeries.X) * PowerSeries.mk (fun _ => 1)

/-- A113413: the Riordan array `((1+x)/(1-x), x(1+x)/(1-x))`. -/
noncomputable def T (n k : ℕ) : ℤ := PowerSeries.coeff n (f * (PowerSeries.X * f) ^ k)

/-- The Mittag-Leffler polynomial `M(m, t)`. -/
noncomputable def ML (m : ℕ) : Polynomial ℤ :=
  ∑ j ∈ Finset.range (m + 1),
    Polynomial.C ((m.choose j : ℤ) * 2 ^ j * ((m - 1).descFactorial (m - j) : ℤ)) *
      descPochhammer ℤ j

/-- A137513(r, c), rows and columns counted from 1: the coefficient of `t^(c-1)` in `M(r-1, t)`. -/
noncomputable def A137513 (r c : ℕ) : ℤ := (ML (r - 1)).coeff (c - 1)

theorem main : ∀ n k : ℕ, k < n →
    (T n k : ℚ) =
      (∑ i ∈ Finset.Icc 2 (k + 2), (A137513 (k + 2) i : ℚ) * ((n - k : ℕ) : ℚ) ^ (i - 2)) /
        (k.factorial : ℚ) := by
  sorry

end OMA.S_oeis_a113413
