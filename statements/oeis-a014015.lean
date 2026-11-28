import Mathlib

/-!
# A014015: Denominators of sign-alternating Egyptian fraction expansion of e - 2

Source: https://oeis.org/A014015
Credit: @Solfanbtc

`e - 2 = 1/a(0) - 1/a(1) + 1/a(2) - ⋯` (offset 0), the greedy sign-alternating Egyptian fraction
expansion (it must begin with `1/1`, Greg Huber): with `r(0) = e - 2`, at each step
`a(n) = ⌊1/r(n)⌋` is the least denominator with `1/a(n) ≥ r(n)`, and the remainder is
`r(n+1) = 1/a(n) - r(n)`. This reproduces all 8 data terms
`1, 3, 19, 983, 1140455, 25739184407616, …` (exact rational arithmetic with `e` to ~800 digits).

Conjecture (Jon E. Schoenfield, Jun 22 2018, OEIS comment): `a(n) ≥ a(n-1)^2 + a(n-1)` for
`n ≥ 1`, so `log(a(n))/2^n` is strictly increasing; "Conjecture:
`lim_{n→∞} log(a(n))/2^n = 0.9748...`". Stated as: the limit exists and equals a real `L` whose
decimal expansion begins `0.9748`, i.e. `0.9748 ≤ L < 0.9749`. (Numerically
`log(a(n))/2^n = 0.9655, 0.9665, 0.9718` for `n = 6, 7, 8`.)
-/

namespace OMA.S_oeis_a014015

/-- The remainders `r(n)` of the greedy alternating expansion of `e - 2`. -/
noncomputable def r : ℕ → ℝ
  | 0 => Real.exp 1 - 2
  | n + 1 => 1 / (⌊1 / r n⌋₊ : ℝ) - r n

/-- A014015: `a(n) = ⌊1 / r(n)⌋`. -/
noncomputable def a (n : ℕ) : ℕ := ⌊1 / r n⌋₊

/-- Schoenfield's conjecture: `log(a(n))/2^n` converges to a limit `0.9748...`. -/
theorem main : ∃ L : ℝ, 0.9748 ≤ L ∧ L < 0.9749 ∧
    Filter.Tendsto (fun n : ℕ => Real.log (a n) / 2 ^ n) Filter.atTop (nhds L) := by
  sorry

end OMA.S_oeis_a014015
