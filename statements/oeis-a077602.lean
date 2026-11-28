import Mathlib

/-!
# A077602: Decimal expansion of lim_{n->inf} M(n,1)/2^n, where M(n,1) is the sum of the coefficients of the n-th Moebius polynomial (cf. A074587).

Source: https://oeis.org/A077602
Credit: @Solfanbtc

The Moebius polynomials (A074586, A077596) satisfy, for `n ≥ 1`,
`M(n, x) = 1 + x * Σ_{k=1}^{n-1} M(k, x) * ⌊n/k⌋`.
Writing `coeff n k` for the coefficient of `x^k` in `M(n, x)`, this means
`coeff n 0 = 1` and `coeff n (k+1) = Σ_{j=1}^{n-1} ⌊n/j⌋ * coeff j k` (as in the Mathematica
program of A077596). `M(n, 1) = Σ_{k<n} coeff n k` (`M(n, x)` has degree `n - 1`), e.g.
`M(8, x) = 1 + 19x + 67x^2 + 108x^3 + 98x^4 + 53x^5 + 16x^6 + 2x^7`.

A077596(n), as defined in its entry: `2^(n-1)` for `n ≤ 4`, the coefficient of
`x^((n-1)/2)` for odd `n`, of `x^(n/2-1)` for even `n > 4`. The conjecture describes A077596(n)
as the largest coefficient of `M(n, x)`; we use the definition of A077596 itself. (The
definition reproduces every term of the data of A077596, and agrees with the largest coefficient
for all `1 ≤ n ≤ 400`, checked in Python.)

Conjecture (in A077602): `M(n, 1) ~ A077596(n) * sqrt(π n / 2)` as `n → ∞`.
(Numerically the ratio is `1.00030` at `n = 100` and `1.000075` at `n = 400`.)
-/

namespace OMA.S_oeis_a077602

/-- `coeff n k`: the coefficient of `x^k` in the `n`-th Moebius polynomial `M(n, x)`, `n ≥ 1`. -/
def coeff : ℕ → ℕ → ℕ
  | _, 0 => 1
  | n, k + 1 => ∑ j : Fin n, if 1 ≤ j.val then (n / j.val) * coeff j.val k else 0
decreasing_by exact j.isLt

/-- `M(n, 1)`, the sum of the coefficients of `M(n, x)` (A074587). -/
def M1 (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, coeff n k

/-- A077596. -/
def A077596 (n : ℕ) : ℕ :=
  if n ≤ 4 then 2 ^ (n - 1)
  else if n % 2 = 1 then coeff n ((n - 1) / 2) else coeff n (n / 2 - 1)

theorem main : Asymptotics.IsEquivalent Filter.atTop (fun n : ℕ => (M1 n : ℝ))
    (fun n : ℕ => (A077596 n : ℝ) * Real.sqrt (Real.pi * n / 2)) := by
  sorry

end OMA.S_oeis_a077602
