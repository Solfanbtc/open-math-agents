import Mathlib

/-!
# A137777: Triangular sequence of coefficients from the expansion of the derivative of the Bernoulli polynomial function: p(x,t) = t*exp(x*t)

Source: https://oeis.org/A137777
Credit: @Solfanbtc

Definition (%N, %F): `p(x,t) = t e^{xt} / (e^t - 1) = Σ B_n(x) t^n / n!` and
`q(x,t) = ∂p/∂t = Σ_{n ≥ 0} Q(x,n) t^n / n!`, so `Q(x,n) = B_{n+1}(x)`; row `n` of the triangle
is the coefficient list of `2 (n+2)! Q(x,n) = 2 (n+2)! B_{n+1}(x)`, which has `n + 2` entries
`T(n,k)`, `k = 0..n+1`. This is the indexing of the conjecture below (its sum runs over
`k = 0..n+1`). The OEIS data list, following P. Luschny's description "coefficients of
`2 (m+1)! B_m(x)`", starts with the extra row `{2}` for `m = 0`; data row `m ≥ 1` is row
`n = m - 1` here. Python (exact rationals) confirms these definitions reproduce all 54 listed terms.

A129825(n) = n! · Bernoulli(n-1) for n > 2, with a(0) = 0, a(1) = 1, a(2) = 1.

Conjecture (R. J. Mathar, Jun 03 2009): `Σ_{k=0}^{n+1} T(n,k) = 2 · A129825(n+2)` for all `n ≥ 0`.
(Checked with python3 for `n < 50`.) `Polynomial.bernoulli` is the standard Bernoulli polynomial
(`B_1(x) = x - 1/2`), and Mathlib's `bernoulli` has `B_1 = -1/2`; A129825 only uses
`Bernoulli(m)` for `m ≥ 2`, where the conventions agree.
-/

namespace OMA.S_oeis_a137777

/-- `T n k` = coefficient of `x^k` in `2 (n+2)! B_{n+1}(x)`. -/
noncomputable def T (n k : ℕ) : ℚ :=
  2 * ((n + 2).factorial : ℚ) * (Polynomial.bernoulli (n + 1)).coeff k

/-- A129825. -/
noncomputable def A129825 (n : ℕ) : ℚ :=
  if n = 0 then 0 else if n ≤ 2 then 1 else (n.factorial : ℚ) * bernoulli (n - 1)

/-- Mathar's conjecture on the row sums of A137777. -/
theorem main : ∀ n : ℕ, ∑ k ∈ Finset.range (n + 2), T n k = 2 * A129825 (n + 2) := by
  sorry

end OMA.S_oeis_a137777
