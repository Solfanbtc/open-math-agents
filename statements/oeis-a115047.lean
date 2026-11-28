import Mathlib

/-!
# A115047: a(3)=1; a(n) = Sum_{i=1..n-3} binomial(n-4,i-1)*binomial(n,i+1)*a(i+2)*a(n-i)*i*(n-i-2)/(2*(n-1)) for n > 3.

Source: https://oeis.org/A115047
Credit: @Solfanbtc

Conjecture (Michael Somos, Sep 20 2014, OEIS A115047): a(n) is divisible by n if n is a prime.

Minimal fix: the offset is 3 and a(3) = 1 is not divisible by 3, so the claim fails at the
prime n = 3; it is stated for primes n >= 5 (it holds for all primes 5 <= n < 120 numerically).

Definition: the recurrence of the name, computed in ℚ (the division by 2(n-1)); with i = j + 1
(j = 0, ..., n-4) the summand is binomial(n-4, j) binomial(n, j+2) a(j+3) a(n-j-1) (j+1) (n-j-3).
The values are integers (1, 1, 5, 61, 1379, 49946, ... as listed; checked for n < 120), and the
divisibility is stated in ℚ as: a(n) / n is an integer.
-/

namespace OMA.S_oeis_a115047

/-- The sequence A115047 (offset 3), as rationals; `a n = 0` for `n < 3`. -/
noncomputable def a (n : ℕ) : ℚ :=
  if h : n ≤ 3 then (if n = 3 then 1 else 0) else
    (∑ j : Fin (n - 3), ((n - 4).choose j : ℚ) * (n.choose (j + 2) : ℚ) * a (j + 3) *
      a (n - (j + 1)) * ((j : ℚ) + 1) * ((n : ℚ) - j - 3)) / (2 * ((n : ℚ) - 1))
termination_by n
decreasing_by all_goals (have := j.isLt; omega)

theorem main : ∀ n : ℕ, n.Prime → 5 ≤ n → ∃ z : ℤ, a n = n * z := by
  sorry

end OMA.S_oeis_a115047
