import Mathlib

/-!
# A084697: a(1) = 2; a(n+1) is the smallest prime of the form a(n) + k*n, k ≥ 1.

Source: https://oeis.org/A084697
Credit: @Solfanbtc

`a(1) = 2` and, for `n ≥ 1`, `a(n+1)` is the smallest prime `a(n) + k n` with `k ≥ 1`.
Since `a(n)` is a prime greater than `n` (inductively `a(n+1) ≥ a(n) + n`), `gcd(a(n), n) = 1`
and Dirichlet's theorem guarantees such primes, so the infimum below is the genuine minimum.
`a 0` is an unused placeholder.

Conjecture (Robert Israel, 2015): `a(n) ~ c n^2 log(n)` for some positive constant `c`, i.e.
`a(n) / (n^2 log n) → c` for some `c > 0`. Checked with python3: the definition reproduces the
48 listed terms, and `a(n) / (n^2 log n)` is about `0.607, 0.635, 0.638, 0.634` at
`n = 10^3, 10^4, 10^5, 4·10^5`.
-/

namespace OMA.S_oeis_a084697

open Filter Topology

/-- A084697 (indexed from `1`; `a 0` is a placeholder). -/
noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 2 => sInf {p : ℕ | p.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ p = a (n + 1) + k * (n + 1)}

/-- The conjecture: `a(n) ~ c n^2 log n` for some `c > 0`. -/
theorem main : ∃ c : ℝ, 0 < c ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / ((n : ℝ) ^ 2 * Real.log n)) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a084697
