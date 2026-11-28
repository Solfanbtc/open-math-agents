import Mathlib

/-!
# A069931: Number of k, 1 ≤ k ≤ n, such that k divides sigma(n)

Source: https://oeis.org/A069931
Credit: @Solfanbtc

`a(n) = #{k : 1 ≤ k ≤ n, k ∣ σ(n)}` (offset 1): `1, 1, 2, 1, 3, 5, 3, 3, 1, 5, …` (the first 30
data terms are reproduced by this definition).

Conjecture (Benoit Cloitre, OEIS formula, "still conjectured"):
`∑_{k=1}^{n} a(k) = C n log(n)^2 + o(n log(n)^2)` with `C = 0.35…`. Stated as: there is `C` whose
decimal expansion begins `0.35` (`0.35 ≤ C < 0.36`) with `(∑_{k ≤ n} a(k))/(n log(n)^2) → C`
(equivalent to the `o(·)` form). Numerically the ratio is `0.352`, `0.363`, `0.386` at
`n = 10^3, 10^4, 10^5` (Python), so the data so far do not settle the value.
-/

namespace OMA.S_oeis_a069931

open ArithmeticFunction

/-- A069931: the number of `k ≤ n` dividing `σ(n)`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => k ∣ sigma 1 n).card

/-- Cloitre's conjecture: `∑_{k ≤ n} a(k) ~ C n log(n)^2` with `C = 0.35…`. -/
theorem main : ∃ C : ℝ, 0.35 ≤ C ∧ C < 0.36 ∧
    Filter.Tendsto (fun n : ℕ => ((∑ k ∈ Finset.Icc 1 n, a k : ℕ) : ℝ) / (n * Real.log n ^ 2))
      Filter.atTop (nhds C) := by
  sorry

end OMA.S_oeis_a069931
