import Mathlib

/-!
# A093525: Decimal expansion of 13/720 - Pi^2/15015.

Source: https://oeis.org/A093525
Credit: @Solfanbtc

`13/720 - π²/15015 = 0.0173982...` is the average volume of a tetrahedron spanned by four points
picked independently and uniformly at random in a tetrahedron of unit volume.

Context (the entry): Klee (1969) conjectured that this average volume is `1/60` (and reported
Monte Carlo experiments suggesting `1/57` as the closest integer reciprocal). The problem was
settled by Buchta and Reitzner (announced 1992, general result 2001) and, independently, by
Mannion (1994): the average is `13/720 - π²/15015`, so Klee's conjectured value `1/60` is wrong.
Stated here is the resolution, the proved value (SOLVED; it refutes `1/60`).

By affine invariance the reference tetrahedron may be the standard simplex
`T = {x ∈ ℝ³ : xᵢ ≥ 0, x₁ + x₂ + x₃ ≤ 1}` (volume `1/6`); for points `x₀, ..., x₃` uniform in `T`,
the ratio `vol(conv(x₀, ..., x₃)) / vol(T)` equals `|det(x₁ - x₀, x₂ - x₀, x₃ - x₀)|`, so the
claim is `E |det| = (1/vol(T)⁴) ∫_{T⁴} |det| = 6⁴ ∫_{T⁴} |det| = 13/720 - π²/15015`.

A python3 Monte Carlo check (4·10⁵ samples) gives `E|det| ≈ 0.017360`, against
`13/720 - π²/15015 = 0.017398` and `1/60 = 0.016667`.

Conventions: points are `x : Fin 4 → (Fin 3 → ℝ)` with the product Lebesgue measure; the
integral is over `Set.pi univ (fun _ => T)`; the matrix has entries `x (j+1) i - x 0 i`.
-/

namespace OMA.S_oeis_a093525

open MeasureTheory

/-- The standard simplex in `ℝ³`. -/
def T : Set (Fin 3 → ℝ) := {x | (∀ i, 0 ≤ x i) ∧ x 0 + x 1 + x 2 ≤ 1}

/-- `|det(x₁ - x₀, x₂ - x₀, x₃ - x₀)|` = `vol(conv(x₀, ..., x₃)) / vol(T)`. -/
noncomputable def ratio (x : Fin 4 → (Fin 3 → ℝ)) : ℝ :=
  |Matrix.det (Matrix.of fun i j : Fin 3 => x j.succ i - x 0 i)|

/-- Buchta–Reitzner / Mannion: the mean volume of a random tetrahedron in a unit tetrahedron is
`13/720 - π²/15015` (refuting Klee's conjectured `1/60`). -/
theorem main :
    (6 : ℝ) ^ 4 * ∫ x in Set.univ.pi (fun _ : Fin 4 => T), ratio x =
      13 / 720 - Real.pi ^ 2 / 15015 := by
  sorry

end OMA.S_oeis_a093525
