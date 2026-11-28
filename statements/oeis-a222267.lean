import Mathlib

/-!
# A222267: the number of lines through an n × n × n grid is asymptotic to 7/(16 ζ(3)) n^6

Source: https://oeis.org/A222267
Credit: @Solfanbtc

A222267 (offset 2): `a(n)` is the number of distinct lines through (at least) two points of the
grid `{0, …, n-1}^3 ⊂ ℝ^3`. Data 28, 253, 1492, 5485, …

Conjecture (C. Tooth, Mar 03 2016): "a(n) is approximately 0.3639537*n^6, with a relative error
of about 10^-5 when n is near 200." A. Weinberger (Nov 09 2026, in the entry): "The conjectured
asymptotic growth rate is correct; the exact leading coefficient is
a(n) ~ 7/(16*zeta(3))*n^6 = 0.3639594755...*n^6", with a heuristic argument (lines are
double-counted by ordered pairs `(P, Q)` with no grid point strictly inside `PQ` and `2Q - P`
outside the cube; the two conditions have limiting probabilities `1/ζ(3)` and `7/8` and are
asymptotically independent, which the comment says "isn't immediate, but it can be checked").
The argument is only sketched in the entry, so `main` states the precise asymptotic
`a(n)/n^6 → 7/(16 ζ(3))`, which makes Tooth's numerical observation exact.

Definitions. Points are `Fin 3 → ℝ`; a line is the affine span `line[ℝ, P, Q]` of two distinct
grid points. `ζ(3) = Sum_{k ≥ 1} 1/k^3`. Checked with python3: this count gives 28, 253, 1492,
5485 for `n = 2, …, 5`.
-/

namespace OMA.S_oeis_a222267

/-- The grid `{0, …, n-1}^3` in `ℝ^3`. -/
def grid (n : ℕ) : Set (Fin 3 → ℝ) := {P | ∀ i, ∃ c : ℕ, c < n ∧ P i = c}

/-- A222267: the number of distinct lines through two distinct points of the grid. -/
noncomputable def a (n : ℕ) : ℕ :=
  {L : AffineSubspace ℝ (Fin 3 → ℝ) |
    ∃ P ∈ grid n, ∃ Q ∈ grid n, P ≠ Q ∧ L = line[ℝ, P, Q]}.ncard

/-- `ζ(3)`. -/
noncomputable def zeta3 : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + 1) ^ 3

open Filter Topology in
/-- `a(n) ~ 7/(16 ζ(3)) n^6`. -/
theorem main :
    Tendsto (fun n : ℕ => (a n : ℝ) / (n : ℝ) ^ 6) atTop (𝓝 (7 / (16 * zeta3))) := by
  sorry

end OMA.S_oeis_a222267
