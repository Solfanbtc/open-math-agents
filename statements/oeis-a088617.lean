import Mathlib

/-!
# A088617: Triangle read by rows: T(n,k) = C(n+k,n)*C(n,k)/(k+1), for n >= 0, k = 0..n.

Source: https://oeis.org/A088617
Credit: @Solfanbtc

Conjecture (D. Callan, Jul 25 2008, COMMENT): "The expected number of U's in a Schroeder n-path
is asymptotically sqrt(1/2)*n for large n."

Conventions.
* A Schroeder n-path uses steps U = (1,1), D = (1,-1), H = (2,0), never goes below the x-axis
  and runs from (0,0) to (2n,0). By the COMMENT of E. Deutsch, T(n,k) is the number of
  Schroeder n-paths with exactly k U's (checked by brute force for n < 8). So, for the uniform
  distribution on Schroeder n-paths, the expected number of U's is
  E(n) = (Sum_k k*T(n,k)) / (Sum_k T(n,k)) (the denominator is the Schroeder number A006318(n)).
* T(n,k) is an integer, so `/` in `T` is exact natural division.
* "Asymptotically sqrt(1/2)*n" is `E ~ (n ↦ sqrt(1/2) * n)` along `atTop` (Mathlib's
  `Asymptotics.IsEquivalent`). Numerically E(3000)/3000 ≈ 0.70702 vs sqrt(1/2) ≈ 0.70711.
-/

namespace OMA.S_oeis_a088617

open Asymptotics Filter

/-- The triangle A088617. -/
def T (n k : ℕ) : ℕ := (n + k).choose n * n.choose k / (k + 1)

/-- Expected number of U steps in a uniformly random Schroeder `n`-path. -/
noncomputable def E (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (n + 1), (k : ℝ) * T n k) / ∑ k ∈ Finset.range (n + 1), (T n k : ℝ)

theorem main : E ~[atTop] fun n : ℕ => Real.sqrt (1 / 2) * n := by
  sorry

end OMA.S_oeis_a088617
