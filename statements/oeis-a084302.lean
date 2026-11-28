import Mathlib

/-!
# A084302: Remainder of tau(n) modulo 6.

Source: https://oeis.org/A084302
Credit: @Solfanbtc

`a(n) = τ(n) mod 6` (`n ≥ 1`), where `τ(n)` is the number of divisors of `n`.

Conjecture (Amiram Eldar, 2024): the asymptotic mean of this sequence is
`3 ζ(3) / ζ(2) = 2.192288…`, i.e. `(1/N) Σ_{n=1}^N a(n) → 3 ζ(3)/ζ(2)`. (The entry's sums of
the first `10^k` terms, `…, 2192385128, 21923168052`, approach this value. The entry notes the
conjecture would follow if A211337 and A211338, `τ(n) ≡ 1` resp. `≡ 2 (mod 3)`, had equal
asymptotic densities.) `ζ` is Mathlib's `riemannZeta`, and `ζ(2)`, `ζ(3)` are real, so their
real parts are used.
-/

namespace OMA.S_oeis_a084302

open Filter Topology

/-- A084302(n) = τ(n) mod 6. -/
def a (n : ℕ) : ℕ := n.divisors.card % 6

/-- The conjecture: the mean of `τ(n) mod 6` tends to `3 ζ(3)/ζ(2)`. -/
theorem main :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, (a n : ℝ)) / N) atTop
      (𝓝 (3 * (riemannZeta 3).re / (riemannZeta 2).re)) := by
  sorry

end OMA.S_oeis_a084302
