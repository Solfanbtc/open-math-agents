import Mathlib

/-!
# A081352: Main diagonal of square maze arrangement of natural numbers A081349.

Source: https://oeis.org/A081352
Credit: @Solfanbtc

`a(n) = (n+1)(n+2) - (-1)^n = 2 C(n+2, 2) - (-1)^n` (offset 0).

Conjecture (Ross La Haye, 2016). For proper fractions `a/b` (`0 < a < b`) and an integer `D`,
let `f(a, b, D) = a/b + gcd(a, b)/D`. For `n ≥ 4`, list all pairs `(a, b)` with
`0 < a < b ≤ n`. `f` gives a *total strict order* on them consistent with the order by value
when (i) `a/b < a'/b'` implies `f(a,b,D) < f(a',b',D)` (the order by value stays intact), and
(ii) equivalent fractions are strictly ordered by numerator: `a/b = a'/b'` and `a < a'` imply
`f(a,b,D) < f(a',b',D)`. Together, (i) and (ii) make `f` injective on these pairs. The minimum
positive integer `D` for which this holds is `2 C(n-1, 2) - (-1)^(n-1)`, which is
`a(n-3)`. For example, `n = 4` gives `D = 7`, while `D = 6` fails
(`f(2,4,6) = f(2,3,6) = 5/6`).
Checked with python3 (exact rationals) for `4 ≤ n ≤ 18`: the least such `D` equals
`2 C(n-1, 2) - (-1)^(n-1)` (the entry reports `n = 4..17`).
-/

namespace OMA.S_oeis_a081352

/-- `f(a, b, D) = a/b + gcd(a, b)/D`. -/
def f (a b : ℕ) (D : ℤ) : ℚ := (a : ℚ) / b + (Nat.gcd a b : ℚ) / D

/-- `f(·, ·, D)` totally orders the fractions `a/b`, `0 < a < b ≤ n`, consistently with their
values, ordering equivalent fractions by numerator. -/
def Good (n : ℕ) (D : ℤ) : Prop :=
  ∀ a b a' b' : ℕ, 0 < a → a < b → b ≤ n → 0 < a' → a' < b' → b' ≤ n →
    ((a : ℚ) / b < (a' : ℚ) / b' → f a b D < f a' b' D) ∧
    ((a : ℚ) / b = (a' : ℚ) / b' → a < a' → f a b D < f a' b' D)

/-- The conjecture: for `n ≥ 4`, the least positive integer `D` that works is
`2 C(n-1, 2) - (-1)^(n-1)`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    IsLeast {D : ℤ | 0 < D ∧ Good n D} (2 * ((n - 1).choose 2 : ℤ) - (-1) ^ (n - 1)) := by
  sorry

end OMA.S_oeis_a081352
