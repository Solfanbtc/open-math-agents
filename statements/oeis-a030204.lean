import Mathlib

/-!
# A030204: Expansion of q^(-1/8) * eta(q) * eta(q^2) in powers of q.

Source: https://oeis.org/A030204
Credit: @Solfanbtc

The entry carries two unproved claims about a(n), the coefficients of
`Product_{k>0} (1 - x^k) * (1 - x^(2k))`:
1. (Vaclav Kotesovec, Sep 26 2026) `Sum_{k=1..n} a(k)^2 ~ E * n` with E = 1.76274717... (Finch),
   and the conjecture `E = A244920 = 2*log(1+sqrt(2))`. Since E > 0, "~ E n" is the same as
   `(1/n) Sum_{k=1..n} a(k)^2 → E`; we state the limit with E = 2 log(1+√2).
2. (Simon Plouffe, Sep 15 2025, "Empirical")
   `Sum_{n>=0} a(n) / exp(n*Pi) = (1/2) * exp(Pi/8) * sqrt(Pi) * 2^(1/8) / Gamma(3/4)^2`.
`main` is their conjunction.

Conventions.
* `a n` is the coefficient of `x^n` in `∏_{k=1}^{n} (1 - x^k)(1 - x^(2k))`; factors with
  k > n do not affect that coefficient, so this is the coefficient of the infinite product.
  Data: 1, -1, -2, 1, 0, 2, 1, 0, 0, -2, ... (offset 0).
* Numerical checks (python3, via Somos's g.f. psi(x)·phi(-x)): (1/n) Σ_{k≤n} a(k)^2 = 1.76285 at
  n = 2·10^6 (2 log(1+√2) = 1.762747...); the series in 2 gives 0.95313220370521... on both sides.
-/

namespace OMA.S_oeis_a030204

open Polynomial in
/-- A030204: coefficients of `∏_{k ≥ 1} (1 - x^k)(1 - x^(2k))`. -/
noncomputable def a (n : ℕ) : ℤ :=
  (∏ k ∈ Finset.Icc 1 n, ((1 - X ^ k) * (1 - X ^ (2 * k)) : ℤ[X])).coeff n

theorem main :
    Filter.Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, ((a k : ℝ)) ^ 2) / n) Filter.atTop
        (nhds (2 * Real.log (1 + Real.sqrt 2))) ∧
    HasSum (fun n : ℕ => (a n : ℝ) / Real.exp (n * Real.pi))
        ((1 / 2) * Real.exp (Real.pi / 8) * Real.sqrt Real.pi * (2 : ℝ) ^ ((1 : ℝ) / 8)
          / Real.Gamma (3 / 4) ^ 2) := by
  sorry

end OMA.S_oeis_a030204
