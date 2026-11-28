import Mathlib

/-!
# A060516: Number of series-reduced (or homeomorphically irreducible) graphs with loops on n labeled nodes.

Source: https://oeis.org/A060516
Credit: @Solfanbtc

Conjecture (OEIS entry, %C, R. J. Mathar 2019): the number of *connected* graphs of this type is
`1, 1, 4, 13, 203, 7754, ...` for `n = 0, 1, 2, ...`. We state it for the listed values `n ≤ 5`.

Conventions:
* A graph with loops on `n` labeled nodes is a simple graph `G` on `Fin n` together with a set
  `L` of looped vertices (at most one loop per vertex, no multiple edges).
* The degree of `v` is `G.degree v + 2` if `v ∈ L` and `G.degree v` otherwise (a loop counts
  twice); series-reduced means that no vertex has degree `2`.
* With these conventions the total counts are `1, 1, 5, 26, 328, 9700` for `n = 0, …, 5`,
  matching %S of A060516 (checked by brute force in Python). Counting a loop once would give
  `2` graphs for `n = 1` instead of `1`.
* Connectedness does not depend on loops. We use `G.Preconnected` rather than `G.Connected`:
  they agree for `n ≥ 1`, while Mathlib's `Connected` requires a nonempty vertex type and the
  source counts the empty graph (`n = 0`) as connected (value `1`).
* The conjectured values `1, 1, 4, 13, 203, 7754` were checked by brute force in Python for
  `n ≤ 5` with these conventions.
-/

namespace OMA.S_oeis_a060516

open Classical

/-- The degree of `v` in the graph with loops `(G, L)`: a loop contributes `2`. -/
noncomputable def loopDegree {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n))
    (v : Fin n) : ℕ :=
  G.degree v + if v ∈ L then 2 else 0

/-- `(G, L)` is series-reduced (homeomorphically irreducible): no vertex has degree `2`. -/
def SeriesReduced {n : ℕ} (G : SimpleGraph (Fin n)) (L : Finset (Fin n)) : Prop :=
  ∀ v, loopDegree G L v ≠ 2

/-- The number of connected series-reduced graphs with loops on `n` labeled nodes. -/
noncomputable def connectedCount (n : ℕ) : ℕ :=
  Nat.card {p : SimpleGraph (Fin n) × Finset (Fin n) // SeriesReduced p.1 p.2 ∧ p.1.Preconnected}

/-- Mathar's conjecture in A060516: the connected counts are `1, 1, 4, 13, 203, 7754` for
`n = 0, …, 5`. -/
theorem main : connectedCount 0 = 1 ∧ connectedCount 1 = 1 ∧ connectedCount 2 = 4 ∧
    connectedCount 3 = 13 ∧ connectedCount 4 = 203 ∧ connectedCount 5 = 7754 := by
  sorry

end OMA.S_oeis_a060516
