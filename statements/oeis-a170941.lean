import Mathlib

/-!
# A170941: a(n+1) = a(n) + n*a(n-1) - a(n-2) + a(n-3).

Source: https://oeis.org/A170941
Credit: @Solfanbtc

Claim (entry comment, David Callan, 2012): a(n)/A000085(n) → 1/e as n → ∞, i.e. the asymptotic
proportion of involutions of [n] that contain no adjacent transposition is 1/e.
(The entry's later asymptotic formula a(n) ~ exp(√n - n/2 - 5/4)·n^(n/2)/√2·(1 + 31/(24√n)),
Vaclav Kotesovec, 2014, would imply this, together with the classical asymptotics of A000085;
no proof is cited, so the claim is stated as conjectured.)

Definitions. a(0) = a(1) = a(2) = 1, a(3) = 2 and a(n+1) = a(n) + n·a(n-1) - a(n-2) + a(n-3) for
n ≥ 3 (computed in ℤ; all values are positive). A000085 (number of involutions of [n]):
t(0) = t(1) = 1, t(n) = t(n-1) + (n-1)·t(n-2). A python check reproduces all 28 listed terms;
a(n)/t(n) is 0.4029 at n = 100, 0.3793 at n = 1000 and 0.3745 at n = 2999 (1/e ≈ 0.3679).
-/

namespace OMA.S_oeis_a170941

/-- A170941. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | n + 4 => a (n + 3) + (n + 3 : ℤ) * a (n + 2) - a (n + 1) + a n

/-- A000085: number of involutions of [n]. -/
def t : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => t (n + 1) + (n + 1) * t n

theorem main :
    Filter.Tendsto (fun n : ℕ => (a n : ℝ) / t n) Filter.atTop (nhds (Real.exp (-1))) := by
  sorry

end OMA.S_oeis_a170941
