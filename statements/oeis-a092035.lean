import Mathlib

/-!
# A092035: Decimal expansion of (Pi/e)^2.

Source: https://oeis.org/A092035
Credit: @Solfanbtc

Conjecture (Peter Bala, Jun 20 2022, OEIS %F):
`(π/e)^2 = 12 · Σ_{k ≥ 1} ((-1)^(k+1) / k^2) · cos(√(2 k^2 π^2 / 3 - 4))`.
For `k ≥ 1` the radicand is positive (`2π²/3 - 4 ≈ 2.58`), and the series converges absolutely
(terms bounded by `1/k^2`), so `tsum` is the ordinary sum. In Lean the summation index is shifted, `k ↦ k + 1` with
`k : ℕ`, so `(-1)^(k+1)` becomes `(-1)^(k+2)`. Numerically, 2·10^6 terms agree
with `(π/e)^2 = 1.33570570705...` to about 12 digits.
-/

namespace OMA.S_oeis_a092035

open Real

theorem main :
    (π / exp 1) ^ 2 =
      12 * ∑' k : ℕ, ((-1 : ℝ) ^ (k + 2) / ((k : ℝ) + 1) ^ 2) *
        cos (√(2 * ((k : ℝ) + 1) ^ 2 * π ^ 2 / 3 - 4)) := by
  sorry

end OMA.S_oeis_a092035
