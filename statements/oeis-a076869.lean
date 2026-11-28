import Mathlib

/-!
# A076869: Largest t such that a spherical t-design with n points exists in four dimensions.

Source: https://oeis.org/A076869
Credit: @Solfanbtc

The entry lists, for `n = 1, ..., 42`,
`a(n) = 0, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 4, 4, 4, 5, 4, 5,
4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6`,
the largest `t` such that a spherical `t`-design with `n` points exists on the unit sphere `S³` of
`ℝ⁴` (Hardin and Sloane), and says: "Most of these values are just conjectures." The conjecture
stated here is that every listed value is correct, i.e. for each `1 ≤ n ≤ 42` the listed `a(n)` is
the largest `t` admitting an `n`-point spherical `t`-design in `ℝ⁴`. (The entry does not say which
values are proved: e.g. the regular simplex (`n = 5`, `t = 2`), the cross-polytope (`n = 8`,
`t = 3`) and the 24-cell (`n = 24`, `t = 5`) are the classical designs.)

Conventions:
* A spherical `t`-design is a finite set `X` of (distinct) points of the unit sphere such that the
  average over `X` of every real polynomial of total degree `≤ t` in the 4 coordinates equals its
  average over the sphere, with respect to the surface measure `(volume : Measure ℝ⁴).toSphere`
  (any rotation-invariant measure gives the same normalized average).
* "with n points": `X.card = n`. Every finite nonempty set is a `0`-design, so the set of
  admissible `t` is nonempty; the claim includes that it is bounded with maximum `a(n)`
  (`IsGreatest`).
-/

namespace OMA.S_oeis_a076869

open MeasureTheory

/-- `ℝ⁴` with the Euclidean norm. -/
abbrev E := EuclideanSpace ℝ (Fin 4)

/-- `X` is a spherical `t`-design on the unit sphere of `ℝ⁴`. -/
def IsSphericalDesign (t : ℕ) (X : Finset E) : Prop :=
  (∀ x ∈ X, ‖x‖ = 1) ∧
    ∀ p : MvPolynomial (Fin 4) ℝ, p.totalDegree ≤ t →
      (∑ x ∈ X, MvPolynomial.eval (fun i => x i) p) / (X.card : ℝ) =
        (∫ y, MvPolynomial.eval (fun i => (y : E) i) p ∂(volume : Measure E).toSphere) /
          ((volume : Measure E).toSphere Set.univ).toReal

/-- The values listed in the entry, `a(1), ..., a(42)`. -/
def data : List ℕ :=
  [0, 1, 1, 1, 2, 2, 2, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 4, 4, 4, 5, 4, 5,
    4, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6]

/-- For `1 ≤ n ≤ 42`, the largest `t` such that an `n`-point spherical `t`-design exists in four
dimensions is the listed `a(n)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → n ≤ 42 →
    IsGreatest {t : ℕ | ∃ X : Finset E, X.card = n ∧ IsSphericalDesign t X}
      (data.getD (n - 1) 0) := by
  sorry

end OMA.S_oeis_a076869
