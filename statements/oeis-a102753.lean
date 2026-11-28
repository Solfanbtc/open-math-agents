import Mathlib

/-!
# A102753: Decimal expansion of (Pi^2)/2.

Source: https://oeis.org/A102753
Credit: @Solfanbtc

Conjecture (Peter Bala, Oct 08 2021, in the entry's formulas):
`π²/2 = ∑_{n = -∞}^{∞} (cos(π √(n² + 1)) - cos(π n))`, using the Eisenstein summation convention,
i.e. the sum is the limit of the symmetric partial sums `∑_{n=-N}^{N}` as `N → ∞`.

WARNING: the claim appears to be FALSE as printed. The terms behave like
`-(-1)ⁿ π²/(8n²)`, so the series even converges absolutely, and a python3 computation of the
symmetric partial sums gives `-0.89414547123...` for `N = 10³, 10⁵, 10⁶, 2·10⁶`, while
`π²/2 = 4.93480220...`. The computed value agrees with `-π J₁(π)` (`J₁` the Bessel function) to
about `10⁻¹²`, which is what Poisson summation suggests; the printed right-hand side is probably
a slip. The entry does not record a refutation. The claim is stated here exactly as written, so
that it can be disproved (`OMA.disproof`).

Conventions: `n` ranges over `ℤ`; the symmetric partial sum is over `Finset.Icc (-N) N`.
-/

namespace OMA.S_oeis_a102753

open Filter Topology

/-- Bala's conjecture as printed (apparently false: the sum is `-π J₁(π) ≈ -0.894`). -/
theorem main :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
        (Real.cos (Real.pi * Real.sqrt ((n : ℝ) ^ 2 + 1)) - Real.cos (Real.pi * n)))
      atTop (𝓝 (Real.pi ^ 2 / 2)) := by
  sorry

end OMA.S_oeis_a102753
