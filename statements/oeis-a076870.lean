import Mathlib

/-!
# A076870: a(n) = smallest m such that a spherical n-design with m points exists in four dimensions.

Source: https://oeis.org/A076870 (Hardin and Sloane; cf. A076868, A076869, A007828)
Credit: @Solfanbtc

"Four dimensions" means the unit sphere `S³ ⊂ ℝ⁴` (consistent with the data: `a(2) = 5` is
the regular simplex in `ℝ⁴`, `a(3) = 8` the cross-polytope, `a(5) = 24` the 24-cell; in the
three-dimensional analogue A076868, `a(2) = 4` is the tetrahedron in `ℝ³`).

A spherical `t`-design is a finite nonempty set `X` of points of the unit sphere such that
for every real polynomial `p` in the four coordinates of total degree at most `t`, the average
of `p` over `X` equals the average of `p` over the sphere (with respect to the surface measure,
Mathlib's `volume.toSphere`).

The entry's data is `a(0..8) = 1, 2, 5, 8, 20, 24, 42, 48, 96`, and its comment says
"Most of these values are just conjectures" (without saying which). The conjecture stated here
is that all listed values are correct.
-/

namespace OMA.S_oeis_a076870

open MeasureTheory

/-- Euclidean four-space `ℝ⁴`. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- The unit sphere `S³ ⊂ ℝ⁴`. -/
abbrev S3 := Metric.sphere (0 : E4) 1

/-- The surface measure on `S³`. -/
noncomputable abbrev σ : Measure S3 := (volume : Measure E4).toSphere

/-- Evaluate a polynomial in the four coordinates at a point of `S³`. -/
noncomputable def evalAt (p : MvPolynomial (Fin 4) ℝ) (x : S3) : ℝ :=
  MvPolynomial.eval (fun i => (x : E4) i) p

/-- `X` is a spherical `t`-design on `S³`. -/
def IsSphericalDesign (t : ℕ) (X : Finset S3) : Prop :=
  X.Nonempty ∧
    ∀ p : MvPolynomial (Fin 4) ℝ, p.totalDegree ≤ t →
      (X.card : ℝ)⁻¹ * ∑ x ∈ X, evalAt p x =
        (σ Set.univ).toReal⁻¹ * ∫ x, evalAt p x ∂σ

/-- A076870: the smallest number of points of a spherical `n`-design in four dimensions. -/
noncomputable def a076870 (n : ℕ) : ℕ :=
  sInf {m | ∃ X : Finset S3, X.card = m ∧ IsSphericalDesign n X}

/-- Conjecture (OEIS A076870): the listed values `a(0), …, a(8)` are correct. -/
theorem main : (List.range 9).map a076870 = [1, 2, 5, 8, 20, 24, 42, 48, 96] := by
  sorry

end OMA.S_oeis_a076870
