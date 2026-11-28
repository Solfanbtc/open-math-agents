import Mathlib

/-!
# A102820: Number of primes between 2*prime(n) and 2*prime(n+1), where prime(n) is the n-th prime.

Source: https://oeis.org/A102820
Credit: @Solfanbtc

Conjecture (Peter Munn, Jun 01 2023, comment in A102820): the asymptotic proportions of
`0`'s, `1`'s, ..., `k`'s, ... among the terms are `1/3, 2/9, ..., 2^k/3^(k+1), ...`.

Formalization.
* `a n = π(2 p_{n+1}) - π(2 p_n)` (the PARI/Mathematica definition in the entry); since
  `2 p_n` and `2 p_{n+1}` are even and `> 2`, this is the number of primes strictly between
  them. Here `p_i = Nat.nth Nat.Prime i` is 0-indexed, so `a n` is the OEIS term `a(n + 1)`;
  the shift does not affect asymptotic proportions.
* "Asymptotic proportion of `k`'s" is the natural density of `{n | a n = k}`: the fraction of
  `n < N` with `a n = k` tends to `2^k / 3^(k+1)` as `N → ∞`, for every `k`.

Checked with python3: `a` reproduces all listed %S/%T/%U terms. (Empirically, for the
1.27 million indices with `p_{n+1} < 2 * 10^7`, the proportions of 0, 1, 2 are 0.262, 0.270,
0.180, still drifting towards 1/3, 2/9, 4/27.)
-/

namespace OMA.S_oeis_a102820

open Filter Topology

/-- `a n` = A102820(n + 1): the number of primes between `2 p_n` and `2 p_{n+1}`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.primeCounting (2 * Nat.nth Nat.Prime (n + 1)) - Nat.primeCounting (2 * Nat.nth Nat.Prime n)

/-- For every `k`, the natural density of `{n | a n = k}` is `2^k / 3^(k+1)`. -/
theorem main : ∀ k : ℕ,
    Tendsto (fun N : ℕ => (((Finset.range N).filter (fun n => a n = k)).card : ℝ) / N) atTop
      (𝓝 ((2 : ℝ) ^ k / 3 ^ (k + 1))) := by
  sorry

end OMA.S_oeis_a102820
