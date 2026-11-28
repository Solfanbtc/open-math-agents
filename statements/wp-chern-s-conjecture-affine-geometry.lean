import Mathlib

/-!
# Chern's conjecture (affine geometry)

Source: https://en.wikipedia.org/wiki/Chern's_conjecture_(affine_geometry)
Credit: @Solfanbtc

Conjecture (S.-S. Chern, 1955): the Euler characteristic of a compact affine manifold vanishes.
(Known cases: complete affine manifolds, Kostant–Sullivan 1975; special affine manifolds,
Klingler 2015. The general case is open.)

Formalization.
* An affine manifold of dimension `n` is a Hausdorff space `M` with an atlas of charts to
  `ℝ^n = EuclideanSpace ℝ (Fin n)` (Mathlib's `ChartedSpace`) whose transition maps are locally
  affine: near every point of its domain, a transition map `e' ∘ e⁻¹` (`e.symm.trans e'`) agrees with an affine map
  `ℝ^n → ℝ^n`. This is the standard definition (equivalently, a flat torsion-free connection on
  the tangent bundle).
* "compact": `CompactSpace M`.
* The Euler characteristic is `Σ_{i=0}^{n} (-1)^i dim_ℚ H_i(M; ℚ)`, with `H_i(M; ℚ)` Mathlib's
  singular homology with coefficients in `ℚ`. For a compact `n`-manifold the rational homology
  is finite-dimensional and vanishes above degree `n`, so this is the usual Euler
  characteristic.
-/

namespace OMA.S_wp_chern_s_conjecture_affine_geometry

open CategoryTheory

/-- The charted space `M` (modelled on `ℝ^n`) has an affine atlas: all transition maps are
locally affine. -/
def IsAffineAtlas (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] : Prop :=
  ∀ e ∈ atlas (EuclideanSpace ℝ (Fin n)) M, ∀ e' ∈ atlas (EuclideanSpace ℝ (Fin n)) M,
    ∀ x ∈ (e.symm.trans e').source,
      ∃ A : EuclideanSpace ℝ (Fin n) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n),
        ∀ᶠ y in nhds x, (e.symm.trans e') y = A y

/-- Singular homology `H_i(X; ℚ)`. -/
noncomputable def H (i : ℕ) (X : Type) [TopologicalSpace X] : ModuleCat.{0} ℚ :=
  ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℚ) i).obj
    (ModuleCat.of ℚ ℚ)).obj (TopCat.of X)

/-- Euler characteristic `Σ_{i ≤ n} (-1)^i dim_ℚ H_i(X; ℚ)` (for an `n`-dimensional manifold). -/
noncomputable def eulerChar (n : ℕ) (X : Type) [TopologicalSpace X] : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank ℚ (H i X) : ℤ)

theorem main :
    ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) M], IsAffineAtlas n M →
      eulerChar n M = 0 := by
  sorry

end OMA.S_wp_chern_s_conjecture_affine_geometry
