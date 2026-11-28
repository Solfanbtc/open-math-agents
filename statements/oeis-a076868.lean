import Mathlib

/-!
# A076868: a(n) = smallest m such that a spherical n-design with m points exists in three dimensions.

Source: https://oeis.org/A076868
Credit: @Solfanbtc

Claim (OEIS A076868): the data 1, 2, 4, 6, 12, 12, 24, 24, 36, 48, 60, 70 (offset 0) lists,
for n = 0, ..., 11, the smallest number of points of a spherical n-design on the unit
sphere of R^3; the comment says that most of these values are just conjectures (Hardin and
Sloane, McLaren's improved snub cube and other new spherical designs in three dimensions,
arXiv:math/0207211). The statement is the whole listed table, every term of %S.

Conventions:
* A spherical n-design is a finite nonempty set X of points of the unit sphere S^2 such that
  every real polynomial in three variables of total degree at most n has the same average
  over X as over the sphere. The points are distinct (X is a `Finset`).
* The sphere average uses Mathlib's surface measure
  `(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere`, a constant multiple of the
  standard surface measure; the constant cancels in an average. The equality of averages
  is written without division: `(∫ p dσ) * |X| = σ(S^2) * ∑_{x ∈ X} p(x)`.
* "Smallest m such that a design with m points exists" is `IsLeast` of the set of sizes.
-/

namespace OMA.S_oeis_a076868

open MeasureTheory

/-- The unit sphere `S^2` in `ℝ^3`. -/
abbrev S2 := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Surface measure on `S^2` (up to a constant factor). -/
noncomputable abbrev σ : Measure S2 := (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere

/-- Evaluation of a polynomial in three variables at a point of the sphere. -/
noncomputable def evalAt (p : MvPolynomial (Fin 3) ℝ) (x : S2) : ℝ :=
  MvPolynomial.eval (fun i => (x : EuclideanSpace ℝ (Fin 3)) i) p

/-- `X` is a spherical `n`-design: nonempty, and every polynomial of total degree `≤ n` has
the same average over `X` as over the sphere. -/
def IsSphericalDesign (n : ℕ) (X : Finset S2) : Prop :=
  X.Nonempty ∧ ∀ p : MvPolynomial (Fin 3) ℝ, p.totalDegree ≤ n →
    (∫ x, evalAt p x ∂σ) * (X.card : ℝ) = σ.real Set.univ * ∑ x ∈ X, evalAt p x

/-- The listed values: `a(0), ..., a(11)`. -/
def listed : List ℕ := [1, 2, 4, 6, 12, 12, 24, 24, 36, 48, 60, 70]

/-- Claim: for `n = 0, ..., 11` the smallest number of points of a spherical `n`-design
in three dimensions is the listed value. -/
theorem main : ∀ n : ℕ, n < listed.length →
    IsLeast {m : ℕ | ∃ X : Finset S2, X.card = m ∧ IsSphericalDesign n X}
      (listed.getD n 0) := by
  sorry

end OMA.S_oeis_a076868
