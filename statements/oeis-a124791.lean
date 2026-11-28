import Mathlib

/-!
# A124791: Mathar's recurrence for the row sums of the generalized Motzkin triangle A124790

Source: https://oeis.org/A124791 (with https://oeis.org/A124790)
A124790 (offset 0) is a generalized Motzkin triangle: for even `k`, column `k` has g.f.
`x^k M(x)^(k/2)`, where `M(x) = 2/(1-x+√(1-2x-3x^2))` is the g.f. of the Motzkin numbers A001006;
for odd `k`, column `k` has g.f. `x^k S(x) M(x)^⌊k/2⌋`, where
`S(x) = (1+x-√(1-2x-3x^2))/(2x(1+x))` is the g.f. of A005043.
A124791(n) is the `n`-th row sum: 1, 1, 1, 3, 5, 13, 29, 73, ...
Conjecture (R. J. Mathar, Dec 02 2014):
`(n+1) a(n) + (-n+2) a(n-1) + (-5n+7) a(n-2) + 3(-n+2) a(n-3) = 0`, stated for `n ≥ 3` (where
all indices are `≥ 0`).

Formalization.
* `m` is A001006: `m(0) = 1`, `m(n+1) = m(n) + ∑_{k<n} m(k) m(n-1-k)` (the coefficient form of
  `M = 1 + xM + x^2 M^2`, which characterizes the closed form above).
* `s` is the sequence with g.f. `S`: from `√(1-2x-3x^2) = 1 - x - 2x^2 M` one gets
  `S(1+x) = 1 + xM`, i.e. `s(0) = 1`, `s(n+1) = m(n) - s(n)` (1, 0, 1, 1, 3, 6, 15, ...).
* `T(n,k)` is the coefficient of `x^(n-k)` in `M^(k/2)` (even `k`) or `S M^⌊k/2⌋` (odd `k`).
Checked with python3: the triangle reproduces the 66 listed terms of A124790, the row sums the 29
listed terms of A124791, and the recurrence holds for all `3 ≤ n ≤ 40`.

Credit: @Solfanbtc
-/

namespace OMA.S_oeis_a124791

open PowerSeries

/-- The Motzkin numbers A001006. -/
def m : ℕ → ℤ
  | 0 => 1
  | n + 1 => m n + ∑ k : Fin n, m k * m (n - 1 - k)
termination_by n => n
decreasing_by all_goals omega

/-- The coefficients of `S(x) = (1+x-√(1-2x-3x^2))/(2x(1+x))` (A005043). -/
def s : ℕ → ℤ
  | 0 => 1
  | n + 1 => m n - s n

/-- The triangle A124790. -/
noncomputable def T (n k : ℕ) : ℤ :=
  if k ≤ n then
    coeff (n - k) (if k % 2 = 0 then (mk m) ^ (k / 2) else mk s * (mk m) ^ (k / 2))
  else 0

/-- A124791: the row sums of A124790. -/
noncomputable def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k

theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 1) * a n + (-(n : ℤ) + 2) * a (n - 1) + (-5 * (n : ℤ) + 7) * a (n - 2)
      + 3 * (-(n : ℤ) + 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a124791
