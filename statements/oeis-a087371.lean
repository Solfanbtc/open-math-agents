import Mathlib

/-!
# A087371: Smallest k such that 10^k + 2n-1 is a prime >10, or 0 if no such k exists. Index of the smallest power of 10 which when increased by the n-th odd number yields a prime.

Source: https://oeis.org/A087371
Credit: @Solfanbtc

For `n ≥ 1`, `a(n)` is the least `k` such that `10^k + 2n - 1` is a prime greater than 10, and
`a(n) = 0` if there is no such `k`. Here this is `sInf` of the set of such `k` (with
`sInf ∅ = 0`). (`k = 0` never qualifies: `1 + (2n - 1) = 2n` is even.) Example:
`a(10) = 1` since `10 + 19 = 29` is prime; `a(3) = 0` since `5 ∣ 10^k + 5`. Checked with python3
against the first 45 terms.

Conjecture (A. Murthy): there exists a finite `M` such that `a(n) < M` for all `n`. `main`
states this.
-/

namespace OMA.S_oeis_a087371

/-- `a n`: the least `k` with `10^k + 2n - 1` a prime `> 10`, or 0 if there is none. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | (10 ^ k + (2 * n - 1)).Prime ∧ 10 < 10 ^ k + (2 * n - 1)}

theorem main : ∃ M : ℕ, ∀ n : ℕ, 1 ≤ n → a n < M := by
  sorry

end OMA.S_oeis_a087371
