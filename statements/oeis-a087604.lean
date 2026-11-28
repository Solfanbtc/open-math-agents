import Mathlib

/-!
# A087604: smallest k such that k written n times followed by a 3 is prime.

Source: https://oeis.org/A087604
Credit: @Solfanbtc

For `n ≥ 1`, A087604(n) is the smallest `k ≥ 1` such that the decimal concatenation of `n`
copies of `k` followed by the digit `3` is prime, or `0` if there is no such `k`; e.g.
`a(5) = 4` since `444443` is prime but `111113, 222223, 333333` are not. `rep k n` is the
concatenation of `n` copies of `k`, and the number in question is `10 * rep k n + 3`.
Trivially `a(3n) = 0`: the digit sum is `3n · (digit sum of k) + 3`.

Conjecture (entry): no other term is zero, i.e. for every `n ≥ 1` with `3 ∤ n` there is
`k ≥ 1` with `10 * rep k n + 3` prime. Checked with python3 (Miller-Rabin): the definition
reproduces the 55 listed terms, and such `k` exist for all `n < 120`, `3 ∤ n` (largest
`a(97) = 823`).
-/

namespace OMA.S_oeis_a087604

/-- The decimal concatenation of `n` copies of `k` (`k ≥ 1`). -/
def rep (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rep k n * 10 ^ (Nat.digits 10 k).length + k

/-- The conjecture: for `n ≥ 1` not divisible by `3`, some `kk…k3` (`n` copies of `k`) is
prime. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ¬ 3 ∣ n → ∃ k : ℕ, 1 ≤ k ∧ (10 * rep k n + 3).Prime := by
  sorry

end OMA.S_oeis_a087604
