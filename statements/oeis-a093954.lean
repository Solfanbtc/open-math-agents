import Mathlib

/-!
# A093954: Decimal expansion of Pi/(2*sqrt(2)).

Source: https://oeis.org/A093954
Credit: @Solfanbtc

Conjecture (Peter Bala, Mar 03 2015, in the entry): with
Pi/(2*sqrt(2)) = Sum_{k >= 0} (-1)^floor(k/2)/(2k + 1), the asymptotic expansion
  Pi/(2*sqrt(2)) - Sum_{k=0..n-1} (-1)^floor(k/2)/(2k+1)
    ~ 1/(2n) - 3/(2n)^3 + 57/(2n)^5 - 2763/(2n)^7 + ...
holds for n a multiple of 4, the unsigned coefficients [1, 3, 57, 2763, ...] being A000281.
(Bala, Sep 21 2016, adds that it follows from the asymptotic expansions given in A181048 and
A181049.)

Conventions.
* A000281(j) is defined by its e.g.f. Sum_j A000281(j) x^(2j)/(2j)! = cos(x)/cos(2x):
  A000281(j) = (2j)! [x^(2j)] cos(x) / cos(2x), computed in ℚ⟦x⟧ (cos(2x) = rescale 2 of cos;
  it has constant term 1, so it is invertible).
* n = 4m with m → ∞. "Asymptotic expansion" is stated in the standard sense: for every K, the
  remainder minus the first K terms is O(m^-(2K+1)), i.e. O(n^-(2K+1)).
* Numerical check (python3, 60 digits): for n = 40, 80, 160, 320 the remainder minus the first
  four terms, times (2n)^9, is 245204, 249320, 250381, 250648, approaching the next coefficient
  250737 = A000281(4); for n = 42 (not a multiple of 4) the expansion fails.
-/

namespace OMA.S_oeis_a093954

/-- A000281: (2j)! [x^(2j)] cos(x)/cos(2x). -/
noncomputable def A000281 (j : ℕ) : ℚ :=
  ((2 * j).factorial : ℚ) *
    PowerSeries.coeff (2 * j)
      (PowerSeries.cos ℚ * (PowerSeries.rescale (2 : ℚ) (PowerSeries.cos ℚ))⁻¹)

/-- The remainder Pi/(2√2) - Sum_{k<n} (-1)^floor(k/2)/(2k+1). -/
noncomputable def remainder (n : ℕ) : ℝ :=
  Real.pi / (2 * Real.sqrt 2) - ∑ k ∈ Finset.range n, (-1 : ℝ) ^ (k / 2) / (2 * k + 1)

theorem main : ∀ K : ℕ,
    (fun m : ℕ => remainder (4 * m)
        - ∑ j ∈ Finset.range K, (-1 : ℝ) ^ j * (A000281 j : ℝ) / (2 * (4 * m : ℝ)) ^ (2 * j + 1))
      =O[Filter.atTop] (fun m : ℕ => 1 / (m : ℝ) ^ (2 * K + 1)) := by
  sorry

end OMA.S_oeis_a093954
