import Mathlib

/-!
# A107877: Column 1 of triangle A107876.

Source: https://oeis.org/A107877
Credit: @Solfanbtc

Conjecture (Benedict W. J. Irwin, Nov 26 2016, %F lines of A107877): `a(n)` can be expressed
with a series of nested sums,
`a(3) = Sum_{i=1..2} (i+2)`,
`a(4) = Sum_{i=1..2} Sum_{j=1..i+2} (j+3)`,
`a(5) = Sum_{i=1..2} Sum_{j=1..i+2} Sum_{k=1..j+3} (k+4)`,
`a(6) = Sum_{i=1..2} Sum_{j=1..i+2} Sum_{k=1..j+3} Sum_{l=1..k+4} (l+5)`.

The pattern, for `n ≥ 3`: `n - 2` nested sums; the variable `v_1` of the outer sum runs over
`1..2`, the variable `v_{t+1}` of level `t + 1` over `1..v_t + (t+1)`, and the summand is
`v_{n-2} + (n-1)`. With `nested t u r` = the value of `r` further levels starting at level `t`
with upper bound `u` (and `nested t u 0 = u`, the summand), this reads
`a(n) = nested 1 2 (n - 2)`: e.g. `nested 1 2 1 = Sum_{i=1..2} (i + 2)`, since the summand at
level `t` is `v_t + (t + 1)`, the bound the next level would have. The conjecture is stated
for every `n ≥ 3`, the range of the examples.

Definition of `a` (A107877, offset 0): by the g.f. identity defining the sequence in its PARI
program, `1 = Sum_{k ≥ 0} a(k) x^k (1-x)^(1 + k(k+1)/2)`; comparing coefficients of `x^n`,
`a(0) = 1` and for `n ≥ 1`
`a(n) = - Sum_{k < n} a(k) (-1)^(n-k) binomial(1 + k(k+1)/2, n-k)`.

Checked with python3: this recursion gives all listed %S/%T/%U terms
(1, 1, 2, 7, 37, 268, ...), and `nested 1 2 (n-2) = a(n)` for `3 ≤ n ≤ 9`; `#eval` of the
Lean definitions agrees.
-/

namespace OMA.S_oeis_a107877

/-- A107877 via the g.f. `1 = Sum_k a(k) x^k (1-x)^(1 + k(k+1)/2)`. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 1
  else -∑ k : Fin n, a k.val * (-1) ^ (n - k.val) *
    ((1 + k.val * (k.val + 1) / 2).choose (n - k.val) : ℤ)
decreasing_by exact k.isLt

/-- `nested t u r`: `r` further nested sums, the current one at level `t` running `1..u`;
the next level runs `1..v + (t + 1)`; with no sums left the value is the bound `u`. -/
def nested (t u : ℕ) : ℕ → ℕ
  | 0 => u
  | r + 1 => ∑ v ∈ Finset.Icc 1 u, nested (t + 1) (v + t + 1) r

/-- Irwin's nested-sum formula for A107877. -/
theorem main : ∀ n : ℕ, 3 ≤ n → a n = (nested 1 2 (n - 2) : ℤ) := by
  sorry

end OMA.S_oeis_a107877
