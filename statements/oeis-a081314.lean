import Mathlib

/-!
# A081314: Order of symmetry groups of n points on 3-dimensional sphere with the volume enclosed by their convex hull maximized.

Source: https://oeis.org/A081314
Credit: @Solfanbtc

The entry: "If more than one configuration with maximal volume exists for a given n, the one
with the largest symmetry group is chosen. Berman and Hanes give optimality proofs for n<=8.
Higher terms are only conjectures. [...] A conjectured continuation of the sequence starting
with n=28 is: 12,6,2,6,120,2,4,4,2,20,4,12,24,12,20,4,8,2,2,2,4,1,24".

So the conjecture is that the listed terms for n ≥ 9 are correct: the data terms for
9 ≤ n ≤ 27 and the conjectured continuation for 28 ≤ n ≤ 50. `main` states exactly this.

Conventions.
* A configuration is a set of `n` distinct points on the unit sphere of `ℝ³`
  (`EuclideanSpace ℝ (Fin 3)`); its volume is the Lebesgue measure of its convex hull.
* A configuration is optimal if no `n`-point configuration has larger volume.
* Its symmetry group is the group of linear isometries of `ℝ³` (the full orthogonal group
  O(3), reflections included, as in the entry: a(12) = 120 is the full icosahedral group)
  mapping the set onto itself; `Nat.card` gives its order.
* a(n) is the largest symmetry-group order among optimal configurations (the tie-breaking
  rule of the entry), stated with `IsGreatest`.
-/

namespace OMA.S_oeis_a081314

/-- Euclidean 3-space. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- `S` is a configuration of `n` distinct points on the unit sphere. -/
def IsConfig (n : ℕ) (S : Finset E3) : Prop :=
  S.card = n ∧ ∀ x ∈ S, ‖x‖ = 1

/-- `S` is an `n`-point configuration whose convex hull has maximal volume. -/
def IsMaxVolume (n : ℕ) (S : Finset E3) : Prop :=
  IsConfig n S ∧ ∀ T : Finset E3, IsConfig n T →
    MeasureTheory.volume (convexHull ℝ (T : Set E3)) ≤
      MeasureTheory.volume (convexHull ℝ (S : Set E3))

/-- The order of the symmetry group (in O(3)) of the point set `S`. -/
noncomputable def symmetryOrder (S : Finset E3) : ℕ :=
  Nat.card {g : E3 ≃ₗᵢ[ℝ] E3 | g '' (S : Set E3) = (S : Set E3)}

/-- The listed terms a(4), ..., a(27) followed by the conjectured continuation a(28), ..., a(50). -/
def terms : List ℕ :=
  [24, 12, 48, 20, 8, 12, 16, 4, 120, 4, 24, 12, 24, 4, 6, 2, 8, 2, 4, 6, 4, 2, 2, 20,
   12, 6, 2, 6, 120, 2, 4, 4, 2, 20, 4, 12, 24, 12, 20, 4, 8, 2, 2, 2, 4, 1, 24]

/-- The listed or conjectured value of a(n), for 4 ≤ n ≤ 50. -/
def a (n : ℕ) : ℕ := terms.getD (n - 4) 0

theorem main : ∀ n : ℕ, 9 ≤ n → n ≤ 50 →
    IsGreatest {k : ℕ | ∃ S : Finset E3, IsMaxVolume n S ∧ symmetryOrder S = k} (a n) := by
  sorry

end OMA.S_oeis_a081314
