import Mathlib

/-!
# A093585: Numerators of even raw moments in the distribution of a triangle picked at random from points on the circumference of a unit circle.

Source: https://oeis.org/A093585
Credit: @Solfanbtc

Conjecture (R. Israel, Jan 01 2018, FORMULA): the moments are
sqrt(3)*Gamma(n+2/3)*Gamma(n+1/3)*(27/16)^n/(2*Pi*(n!)^2).

Conventions.
* Three points are picked independently and uniformly on the unit circle, at angles
  `a, b, c ∈ [0, 2π]`; the random variable is the area of the triangle they span (see the
  MathWorld link "Circle Triangle Picking" and the EXAMPLE: the raw moments are
  1, 3/(2π), 3/8, 35/(32π), 45/128, ...).
* The even raw moments are E[area^(2n)], n ≥ 0 (A093585/A093586 are their numerators and
  denominators: 1, 3/8, 45/128, 105/256, ...). The conjectured formula gives exactly these at
  n = 0 (1), n = 1 (3/8), and agrees numerically for n ≤ 4, so it is the n-th even moment.
* The area is computed by the shoelace formula; it is raised to the even power `2n`, so its sign
  does not matter. The expectation is the triple integral over `[0, 2π]^3` divided by `(2π)^3`.
-/

namespace OMA.S_oeis_a093585

open Real

/-- Signed area of the triangle with vertices at angles `a`, `b`, `c` on the unit circle. -/
noncomputable def signedArea (a b c : ℝ) : ℝ :=
  ((cos b - cos a) * (sin c - sin a) - (cos c - cos a) * (sin b - sin a)) / 2

/-- The `2n`-th raw moment of the area of a random triangle inscribed in the unit circle. -/
noncomputable def evenMoment (n : ℕ) : ℝ :=
  (∫ a in (0 : ℝ)..2 * π, ∫ b in (0 : ℝ)..2 * π, ∫ c in (0 : ℝ)..2 * π,
      signedArea a b c ^ (2 * n)) / (2 * π) ^ 3

theorem main : ∀ n : ℕ, evenMoment n =
    √3 * Gamma (n + 2 / 3) * Gamma (n + 1 / 3) * (27 / 16) ^ n / (2 * π * (n.factorial : ℝ) ^ 2) := by
  sorry

end OMA.S_oeis_a093585
