import Mathlib

/-!
# A067151: Number of regions in regular n-gon which are quadrilaterals (4-gons) when all its diagonals are drawn.

Source: https://oeis.org/A067151
Credit: @Solfanbtc

Conjecture (Bill McEachen, OEIS A067151, %F, Mar 03 2024): a(n) ~ c * n^4. (The accompanying
question "Is c = 1/64 ?" is a question, not a conjecture, and is not stated.)

Conventions:
* The regular n-gon (n ≥ 3) has vertices `exp(2πik/n)`, `k < n`, in `ℂ` viewed as the real
  plane. All its sides and diagonals are the segments between two distinct vertices; the
  regions are the connected components of the open polygon (interior of the convex hull of the
  vertices) minus the union of these segments. Each region is the interior of a convex polygon,
  so it is a quadrilateral iff its closure has exactly 4 extreme points.
* `a n` is the number of such regions (offset 4: a(4) = 0 since the square is cut into 4
  triangles, a(6) = 6, the regions around the center). It is defined for every `n`, and is only
  used asymptotically.
* "a(n) ~ c * n^4" is read as: for some real `c > 0`, `a(n) / n^4 → c` as `n → ∞` (`c > 0`, as
  `~` with `c = 0` would not be an asymptotic equivalence). The data give
  a(49)/49^4 ≈ 0.0152, a(50)/50^4 ≈ 0.0157, a(51)/51^4 ≈ 0.0153.
-/

namespace OMA.S_oeis_a067151

open Filter Topology

/-- The `k`-th vertex of the regular `n`-gon inscribed in the unit circle. -/
noncomputable def vertex (n k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (n : ℂ))

/-- The open regular `n`-gon. -/
noncomputable def openPolygon (n : ℕ) : Set ℂ :=
  interior (convexHull ℝ (Set.range fun k : Fin n => vertex n k))

/-- The union of all sides and diagonals. -/
noncomputable def diagonals (n : ℕ) : Set ℂ :=
  ⋃ (i : Fin n) (j : Fin n) (_ : i ≠ j), segment ℝ (vertex n i) (vertex n j)

/-- The open polygon with all diagonals removed. -/
noncomputable def cut (n : ℕ) : Set ℂ := openPolygon n \ diagonals n

/-- The regions: connected components of `cut n`. -/
def regions (n : ℕ) : Set (Set ℂ) :=
  {R | ∃ z ∈ cut n, R = connectedComponentIn (cut n) z}

/-- A067151: the number of regions which are quadrilaterals. -/
noncomputable def a (n : ℕ) : ℕ :=
  {R ∈ regions n | (Set.extremePoints ℝ (closure R)).ncard = 4}.ncard

/-- McEachen's conjecture: `a(n) ~ c n^4` for some constant `c > 0`. -/
theorem main :
    ∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 4) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a067151
