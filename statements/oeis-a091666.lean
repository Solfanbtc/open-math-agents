import Mathlib

/-!
# A091666: Difference between prime(n)^2 and the next prime.

Source: https://oeis.org/A091666
Credit: @Solfanbtc

`a(n) = q - p^2`, where `p = prime(n)` (`n ≥ 1`, `prime(1) = 2`) and `q` is the least prime
`> p^2`. Data: `1, 2, 4, 4, 6, 4, 4, 6, 12, 12, …` (`a(1) = 5 - 4`).

The entry has two conjectures:
1. (Charles R Greathouse IV) `a(n) ≪ log^2 n`. This is not stated here: it follows directly
   from the upstream `Cramer.cramer_conjecture` (`p_{k+1} - p_k = O(log^2 p_k)`), since the gap
   following `p^2` is at most the prime gap containing `p^2 + 1`, which is
   `O(log^2 (p^2)) = O(log^2 n)`.
2. (Alain Rocchelli, 2023) `lim_{N → ∞} (Σ_{n=1}^N a(n)) / (Σ_{n=1}^N log prime(n)) = 2`.
   This is `main`.
Checked with python3 (Miller-Rabin): the definition reproduces the listed terms, and the ratio
in (2) is about `2.43, 2.18, 2.20, 2.15, 2.15` at `N = 10, 10^3, 10^4, 10^5, 2·10^5`, still
slowly decreasing.
-/

namespace OMA.S_oeis_a091666

open Filter Topology

/-- `prime(n)`, 1-indexed. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A091666(n): the next prime after `prime(n)^2`, minus `prime(n)^2`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {q : ℕ | q.Prime ∧ prime n ^ 2 < q} - prime n ^ 2

/-- Rocchelli's conjecture: `Σ a(n) / Σ log prime(n) → 2`. -/
theorem main :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (a n : ℝ)) /
      ∑ n ∈ Finset.Icc 1 N, Real.log (prime n)) atTop (𝓝 2) := by
  sorry

end OMA.S_oeis_a091666
