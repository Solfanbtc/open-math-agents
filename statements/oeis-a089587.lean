import Mathlib

/-!
# A089587: a(n) is the smallest integer k, 0<k<n, that most often satisfies the condition: k^m > k^(m+1) (modulo n) as m varies from 1 to n-1

Source: https://oeis.org/A089587
Credit: @Solfanbtc

For `0 < k < n`, let `c(n, k)` be the number of `m` with `1 ≤ m ≤ n - 1` and
`(k^m mod n) > (k^(m+1) mod n)`. `a(n)` is the smallest `k` with `0 < k < n` maximizing
`c(n, k)`, with `a(1) = 0` and `a(2) = 1` (both agree with this rule, `a(1) = 0` being the
value for an empty choice). The definition reproduces all terms of %S, %T, %U.

Conjectures of the entry (comment, and formula section):
1. `a(n) = 2` only when `n` is a Fermat number `2^(2^j) + 1`, and `a(2^(2^j) + 1) = 2`;
   together: `a(n) = 2 ↔ n` is a Fermat number (checked for `n < 1200`).
2. `a(2^n - 1) = 2^(n-1)`. This fails trivially at `n = 1` (`a(1) = 0 ≠ 1`), so it is
   stated for `n ≥ 2` (checked for `2 ≤ n ≤ 11`).
3. `a(4^n - 2) = 4^(n-1)` for `n ≥ 1` (checked for `n ≤ 5`).
-/

namespace OMA.S_oeis_a089587

/-- `c n k`: the number of `m ∈ [1, n-1]` with `k^m mod n > k^(m+1) mod n`. -/
def c (n k : ℕ) : ℕ := ((Finset.Icc 1 (n - 1)).filter fun m => k ^ (m + 1) % n < k ^ m % n).card

/-- `a n`: the smallest `k`, `0 < k < n`, maximizing `c n k` (`0` when there is no such `k`). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k | 0 < k ∧ k < n ∧ ∀ j, 0 < j → j < n → c n j ≤ c n k}

/-- The three conjectures of A089587. -/
theorem main :
    (∀ n : ℕ, a n = 2 ↔ ∃ j : ℕ, n = 2 ^ (2 ^ j) + 1) ∧
    (∀ n : ℕ, 2 ≤ n → a (2 ^ n - 1) = 2 ^ (n - 1)) ∧
    (∀ n : ℕ, 1 ≤ n → a (4 ^ n - 2) = 4 ^ (n - 1)) := by
  sorry

end OMA.S_oeis_a089587
