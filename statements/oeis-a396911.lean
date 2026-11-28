import Mathlib

/-!
# A396911: Shortest path indices during walk over golden ratio phyllotaxis starting at the center.

Source: https://oeis.org/A396911
Credit: @Solfanbtc

Vogel's phyllotaxis: the points `p(k) = (√k cos(kθ), √k sin(kθ))`, `k = 0, 1, 2, ...`, with
`θ = π (3 - √5)` the golden angle (A131988, `≈ 2.39996`). Starting at `p(0) = (0,0)`, move each
time to the closest (Euclidean distance) unvisited point; `a(n)` is the index of the point
reached after `n` moves.

Conjecture (Sean A. Irvine, Jun 21 2026): `a(n) ≤ (3/2) n^2`.

Ties: whether two closest candidates can tie is an open question of the entry (P. von
Brömssen). `main` therefore states the bound for every greedy walk, i.e. for every way of
breaking ties; if no tie ever occurs, the greedy walk is unique and this is exactly the
conjecture. Distances are compared through squared Euclidean distances.
Checked (python3, floating point): the greedy walk reproduces the 51 data terms, the
closest and second closest candidates never differ by less than `0.003` in squared distance
for `n < 120`, and `a(n) ≤ 1.5 n^2` for `n < 120`.
-/

namespace OMA.S_oeis_a396911

/-- The golden angle `π (3 - √5)`. -/
noncomputable def θ : ℝ := Real.pi * (3 - Real.sqrt 5)

/-- `x`-coordinate of `p(k)`. -/
noncomputable def px (k : ℕ) : ℝ := Real.sqrt k * Real.cos (k * θ)

/-- `y`-coordinate of `p(k)`. -/
noncomputable def py (k : ℕ) : ℝ := Real.sqrt k * Real.sin (k * θ)

/-- Squared Euclidean distance between `p(i)` and `p(j)`. -/
noncomputable def sqDist (i j : ℕ) : ℝ := (px i - px j) ^ 2 + (py i - py j) ^ 2

/-- `w` is a greedy walk: it starts at index `0`, and each move goes to an unvisited point
at minimal distance among the unvisited points. -/
def IsGreedyWalk (w : ℕ → ℕ) : Prop :=
  w 0 = 0 ∧ ∀ n : ℕ, (∀ m ≤ n, w (n + 1) ≠ w m) ∧
    ∀ k : ℕ, (∀ m ≤ n, k ≠ w m) → sqDist (w n) (w (n + 1)) ≤ sqDist (w n) k

/-- Irvine's conjecture: `a(n) ≤ (3/2) n^2`. -/
theorem main : ∀ w : ℕ → ℕ, IsGreedyWalk w → ∀ n : ℕ, (w n : ℝ) ≤ 3 / 2 * (n : ℝ) ^ 2 := by
  sorry

end OMA.S_oeis_a396911
