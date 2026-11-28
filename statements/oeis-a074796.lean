import Mathlib

/-!
# A074796: Number of k ≤ n with tau(k) ≡ 2 (mod 3)

Source: https://oeis.org/A074796
Credit: @Solfanbtc

`a(n)` (offset 1) is the number of `k ≤ n` such that `τ(k) ≡ 2 (mod 3)`, `τ(k)` the number of
divisors: `0, 1, 2, 2, 3, 3, 4, …`. The entry records "`a(n)` is asymptotic to `c n` with
`c = 0.38…`" (an early numerical estimate) and the later, precise conjecture:

Conjecture (Amiram Eldar, Feb 01 2025, OEIS formula): the constant is `3 ζ(3)/π² = 0.3653814847…`
(A346602); see A211338 (counts of terms up to `10^k`: `…, 365381169, 3653826361`). Stated as
`a(n)/n → 3 ζ(3)/π²`. (This is the `τ ≡ 2` counterpart of the A074794 conjecture for `τ ≡ 1`;
neither follows from the other by an elementary argument.)
-/

namespace OMA.S_oeis_a074796

open Filter Topology Real

/-- A074796: the number of `k ≤ n` with `τ(k) ≡ 2 (mod 3)`. -/
def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => k.divisors.card % 3 = 2).card

/-- Eldar's conjecture: `a(n)/n → 3 ζ(3)/π²`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (3 * (riemannZeta 3).re / π ^ 2)) := by
  sorry

end OMA.S_oeis_a074796
