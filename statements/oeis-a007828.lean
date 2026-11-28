import Mathlib

/-!
# A007828: Largest t such that a spherical t-design with n points exists in 3 dimensions.

Source: https://oeis.org/A007828
Credit: @Solfanbtc

The OEIS entry lists a(1), ..., a(64) (offset 1):
0,1,1,2,1,3,2,3,2,3,3,5,3,4,3,5,4,5,4,5,4,5,5,7,5,6,5,6,6,7,6,7,6,7,
6,8,7,7,7,8,7,8,7,8,8,8,8,9,8,9,8,9,8,9,9,9,9,9,9,10,9,9,9,10
and comments: "Most of these values are just conjectures." The values come from the numerical
searches of R. H. Hardin and N. J. A. Sloane, *McLaren's Improved Snub Cube and Other New
Spherical Designs in Three Dimensions*, Discrete Comput. Geom. 15 (1996), 429-441.
Some of the small values are proved; the entry does not say which, so the conjecture stated here
is that every listed value is correct.

Conventions.
* A spherical `t`-design is a finite set `X` of points of the unit sphere `S²` of `ℝ³` such that,
  for every real polynomial `p` in three variables of total degree at most `t`, the average of `p`
  over `X` equals the average of `p` over `S²` with respect to the rotation-invariant surface
  measure (here `volume.toSphere`, the measure induced on the sphere by Lebesgue measure; it is a
  positive multiple of surface area, so the normalized average `⨍` is the same).
* "With n points" means `n` distinct points (a `Finset` of cardinality `n`), as in Hardin–Sloane.
* Every nonempty finite set is a `0`-design, and for fixed `n` the possible `t` are bounded, so the
  largest `t` is expressed with `IsGreatest`.
-/

namespace OMA.S_oeis_a007828

open MeasureTheory

/-- Three-dimensional Euclidean space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- `X` is a spherical `t`-design: its points lie on the unit sphere and the average over `X` of
every polynomial of total degree at most `t` equals its average over the unit sphere. -/
def IsSphericalDesign (t : ℕ) (X : Finset E3) : Prop :=
  (∀ x ∈ X, ‖x‖ = 1) ∧
  ∀ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ t →
    (X.card : ℝ)⁻¹ * ∑ x ∈ X, MvPolynomial.eval (fun i => x i) p =
      ⨍ y, MvPolynomial.eval (fun i => (y : E3) i) p ∂(volume : Measure E3).toSphere

/-- The listed values a(1), ..., a(64), indexed from `0`. -/
def data : Fin 64 → ℕ :=
  ![0, 1, 1, 2, 1, 3, 2, 3, 2, 3, 3, 5, 3, 4, 3, 5, 4, 5, 4, 5, 4, 5, 5, 7, 5, 6, 5, 6, 6, 7, 6, 7,
    6, 7, 6, 8, 7, 7, 7, 8, 7, 8, 7, 8, 8, 8, 8, 9, 8, 9, 8, 9, 8, 9, 9, 9, 9, 9, 9, 10, 9, 9, 9, 10]

/-- For `1 ≤ n ≤ 64`, the largest `t` such that a spherical `t`-design with `n` points exists in
three dimensions is the value listed in A007828. -/
theorem main : ∀ n : Fin 64,
    IsGreatest {t : ℕ | ∃ X : Finset E3, X.card = n.val + 1 ∧ IsSphericalDesign t X} (data n) := by
  sorry

end OMA.S_oeis_a007828
