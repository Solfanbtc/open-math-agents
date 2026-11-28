import Mathlib

/-!
# A124571: Expansion of limit b(n)/x^n where b(n) = b(n-1)^2 + b(n-1)*x, b(1) = x^2.

Source: https://oeis.org/A124571
Credit: @Solfanbtc

Question (Paul D. Hanna, Jul 28 2025): what is the limit of a(n)^(1/n)?
Conjecture (Vaclav Kotesovec, Jul 29 2025): the limit is equal to the golden ratio.

Definitions.
* b(1) = x^2, b(n) = b(n-1)^2 + b(n-1) x (polynomials over ℕ).
* With S_n = b(n)/x^n one gets S_1 = x and S_(n+1) = S_n + x^(n-1) S_n^2, so passing from S_n
  to S_(n+1) only changes coefficients of degree ≥ n + 1: the coefficient of x^n is final in
  S_n. Hence the limit series A(x) = Sum_{n>=1} a(n) x^n has a(n) = [x^n] S_n = [x^(2n)] b(n)
  (offset 1). This reproduces all 38 data terms (python3).
* Statement: a(n)^(1/n) → φ = (1 + √5)/2.
-/

namespace OMA.S_oeis_a124571

open Polynomial

/-- b(n). -/
noncomputable def b : ℕ → ℕ[X]
  | 0 => 0
  | 1 => X ^ 2
  | (n + 2) => b (n + 1) ^ 2 + b (n + 1) * X

/-- A124571(n), offset 1. -/
noncomputable def a (n : ℕ) : ℕ := (b n).coeff (2 * n)

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / n)) Filter.atTop
      (nhds Real.goldenRatio) := by
  sorry

end OMA.S_oeis_a124571
