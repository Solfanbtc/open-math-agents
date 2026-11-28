import Mathlib

/-!
# A059099: Expansion of e.g.f. exp(exp(x)-1)/(2-exp(x)).

Source: https://oeis.org/A059099
Credit: @Solfanbtc

`a(n) = n! [x^n] exp(exp(x) - 1)/(2 - exp(x))`. We use the entry's formula
`a(n) = Σ_{m=0..n} Σ_{i=0..n} S2(n, i) · i(i-1)⋯(i-m+1)` (Stirling transform of A000522), where
`S2` is the Stirling number of the second kind and the product is the falling factorial
`i.descFactorial m`. Checked with `#eval`/python3: it gives 1, 2, 7, 33, 198, 1453, 12669, …,
as listed.

Conjecture (Velin Yanev, 2026): for `n > 0`,
`a(n) = e · Σ_{k ≥ 0} k^n Γ(k + 1, 2) / (2^(k+1) k!)`, where
`Γ(s, x) = ∫_x^∞ t^(s-1) e^(-t) dt` is the upper incomplete gamma function, so
`Γ(k + 1, 2) = ∫_2^∞ t^k e^(-t) dt`. `main` states that the series converges (absolutely: all
terms are nonnegative) with sum `a(n)`. Checked numerically with python3 for `n ≤ 9`.
-/

namespace OMA.S_oeis_a059099

open MeasureTheory Set

/-- A059099(n). -/
def a (n : ℕ) : ℕ :=
  ∑ m ∈ Finset.range (n + 1), ∑ i ∈ Finset.range (n + 1),
    Nat.stirlingSecond n i * i.descFactorial m

/-- The upper incomplete gamma function value `Γ(k + 1, 2) = ∫_2^∞ t^k e^(-t) dt`. -/
noncomputable def upperGamma (k : ℕ) : ℝ :=
  ∫ t in Ioi (2 : ℝ), t ^ k * Real.exp (-t)

/-- Yanev's conjecture. -/
theorem main : ∀ n : ℕ, 0 < n →
    HasSum (fun k : ℕ => Real.exp 1 * ((k : ℝ) ^ n * upperGamma k / (2 ^ (k + 1) * k.factorial)))
      (a n : ℝ) := by
  sorry

end OMA.S_oeis_a059099
