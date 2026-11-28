import Mathlib

/-!
# A070965: a(1) = 1; a(n+1) = sum_{k | n} a(k) mu(k)

Source: https://oeis.org/A070965
Credit: @Solfanbtc

`a(1) = 1` and `a(n+1) = ∑_{k ∣ n} a(k) μ(k)` (sum over the positive divisors `k` of `n`, `μ` the
Möbius function): 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, -1, ... (offset 1).

Conjecture (W. Edwin Clark, Aug 20 2004): all integers are present, i.e. every integer `z` equals
`a(n)` for some `n ≥ 1`.

Encoding: `a : ℕ → ℤ`, indexed from 1 (`a 0 = 0` is unused); every divisor `k` of `n + 1` is
`≤ n + 1 < n + 2`, so the recursion is well founded.

Sanity check (python): the recursion reproduces all 105 listed terms, and every integer in
`[-300, 300]` occurs among `a(1), ..., a(2·10^6)`; `#eval` in Lean gives the first 40 listed terms.
-/

namespace OMA.S_oeis_a070965

/-- A070965. -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | n + 2 => ∑ k : (n + 1).divisors, a k * ArithmeticFunction.moebius k
decreasing_by exact Nat.lt_succ_of_le (Nat.divisor_le k.2)

/-- Clark's conjecture: every integer occurs in A070965. -/
theorem main : ∀ z : ℤ, ∃ n : ℕ, 1 ≤ n ∧ a n = z := by
  sorry

end OMA.S_oeis_a070965
