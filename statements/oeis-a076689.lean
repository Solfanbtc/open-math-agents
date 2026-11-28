import Mathlib

/-!
# A076689: Smallest k such that k*prime(n)# + 1 is prime.

Source: https://oeis.org/A076689
Credit: @Solfanbtc

For `n ≥ 1`, `prime(n)# = primorial (prime(n))` is the product of the first `n` primes
(`prime(n) = Nat.nth Nat.Prime (n - 1)`), and `a(n)` is the smallest `k` with
`k * prime(n)# + 1` prime. (`k = 0` never qualifies, and such `k` exist by Dirichlet's theorem,
so the infimum is the genuine minimum.)

Conjectures (Pierre Cami, 2017), both stated in `main`:
1. `lim_{N → ∞} (Σ_{n=1}^N a(n)) / (Σ_{n=1}^N n) = 1/2`;
2. `a(n)/n < 4` for all `n ≥ 1`, i.e. `a(n) < 4n`.
Checked with python3 (Miller-Rabin): the definition reproduces the 31 listed terms, `a(n) < 4n`
for `n ≤ 300`, and the ratio in (1) is about `0.462` at `N = 300`.
-/

namespace OMA.S_oeis_a076689

open Filter Topology

/-- A076689(n), for `n ≥ 1`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | (k * primorial (Nat.nth Nat.Prime (n - 1)) + 1).Prime}

/-- Pierre Cami's two conjectures. -/
theorem main :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (a n : ℝ)) / ∑ n ∈ Finset.Icc 1 N, (n : ℝ))
      atTop (𝓝 (1 / 2)) ∧
    ∀ n : ℕ, 1 ≤ n → a n < 4 * n := by
  sorry

end OMA.S_oeis_a076689
