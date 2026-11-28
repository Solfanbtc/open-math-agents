import Mathlib

/-!
# A012200: arctanh(arctan(arcsin(x))) = x + 1/3!*x^3 + 17/5!*x^5 + 393/7!*x^7 + 25601/9!*x^9 + ...

Source: https://oeis.org/A012200
Credit: @Solfanbtc

Conjecture (Vaclav Kotesovec, OEIS A012200, formula section, Feb 07 2015):
a(n) ~ (2*n)! / (sin(tan(1)))^(2*n+1).

Conventions:
* By the name, arctanh(arctan(arcsin(x))) = Sum_{n >= 0} a(n) x^(2n+1)/(2n+1)!, so a(n) is the
  (2n+1)-th derivative at 0 of f(x) = arctanh(arctan(arcsin x)) (offset 0). Here
  arctanh(y) = (1/2) log((1+y)/(1-y)), and `Real.arcsin`, `Real.arctan` are Mathlib's. The
  function is smooth near 0 (|arctan(arcsin x)| < 1 there), so the iterated derivative at 0
  only depends on f near 0. Checked in Python by composing the power series: this gives all
  14 listed terms 1, 1, 17, 393, 25601, ...
* `~` is asymptotic equivalence as n → ∞ (`Asymptotics.IsEquivalent`).
-/

namespace OMA.S_oeis_a012200

open Filter Asymptotics

/-- The inverse hyperbolic tangent, `(1/2) log((1+y)/(1-y))`. -/
noncomputable def arctanh (y : ℝ) : ℝ := Real.log ((1 + y) / (1 - y)) / 2

/-- `f(x) = arctanh(arctan(arcsin x))`. -/
noncomputable def f (x : ℝ) : ℝ := arctanh (Real.arctan (Real.arcsin x))

/-- A012200: `a(n) = f^{(2n+1)}(0)`. -/
noncomputable def a (n : ℕ) : ℝ := iteratedDeriv (2 * n + 1) f 0

/-- Kotesovec's conjecture: `a(n) ~ (2n)! / sin(tan 1)^(2n+1)`. -/
theorem main :
    a ~[atTop] fun n : ℕ =>
      (Nat.factorial (2 * n) : ℝ) / Real.sin (Real.tan 1) ^ (2 * n + 1) := by
  sorry

end OMA.S_oeis_a012200
